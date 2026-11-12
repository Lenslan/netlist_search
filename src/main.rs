//! netlist_search: trace a wire of a gate-level netlist back to its drivers
//! and print the cone logic in RTL-style form.

use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow};
use clap::Parser;

use netlist_search::liberty::CellLib;
use netlist_search::logic::expr::Radix;
use netlist_search::logic::{AnalyzeOpts, analyze};
use netlist_search::netlist::design::Design;
use netlist_search::netlist::index::ModuleIndex;
use netlist_search::report::{render, wires_to_show};
use netlist_search::trace::{TraceOpts, trace};

#[derive(Parser, Debug)]
#[command(
    name = "netlist_search",
    version,
    about = "Trace a wire of a gate-level netlist back to registers, black boxes and ports, \
             and print the logic of every wire on the way in RTL-style form"
)]
struct Args {
    /// Gate-level structural Verilog netlist (may be given several times)
    #[arg(long, required = true, num_args = 1.., value_name = "FILE")]
    netlist: Vec<PathBuf>,

    /// Liberty cell library (may be given several times)
    #[arg(long, required = true, num_args = 1.., value_name = "FILE")]
    lib: Vec<PathBuf>,

    /// Top module, if it cannot be determined automatically
    #[arg(long, value_name = "MODULE")]
    top: Option<String>,

    /// Instance path of the module holding the wire, e.g. u_core/u_fsm.
    /// Omit it for a wire of the top module
    #[arg(long, default_value = "", value_name = "PATH")]
    inst: String,

    /// Wire to trace: name, name[i] or name[msb:lsb]
    #[arg(long, value_name = "NAME")]
    wire: String,

    /// Only show the wires whose logic depends on this signal
    /// (a register, port or net name, with or without a bit index)
    #[arg(long, value_name = "SIGNAL")]
    filter: Option<String>,

    /// How constants are written: dec, hex or bin
    #[arg(long, default_value = "dec")]
    radix: String,

    /// Do not follow drivers across module boundaries
    #[arg(long)]
    no_cross: bool,

    /// Maximum number of module boundaries to cross
    #[arg(long, default_value_t = 8, value_name = "N")]
    max_hier_depth: u32,

    /// Maximum number of net bits in the cone
    #[arg(long, default_value_t = 200_000, value_name = "N")]
    max_nodes: usize,

    /// Print endpoint forms even when they are large
    #[arg(long)]
    expand: bool,

    /// Show a wire as a bit of `bus + K` or `bus * K` rather than as the
    /// equivalent range or set test, whenever both describe it
    #[arg(long)]
    prefer_arith: bool,

    /// Never print a result that is not proven (no simulation matching)
    #[arg(long)]
    strict: bool,

    /// Multiply the effort spent on endpoint forms (use when the report says
    /// a limit was reached)
    #[arg(long, default_value_t = 1, value_name = "N", value_parser = clap::value_parser!(u32).range(1..=1000))]
    effort: u32,

    /// Only trace and print local forms; skip the endpoint forms
    #[arg(long)]
    no_lift: bool,

    /// Write the report to this file instead of stdout
    #[arg(short, long, value_name = "FILE")]
    output: Option<PathBuf>,

    /// Print timings and counts to stderr
    #[arg(long)]
    stats: bool,

    /// Append a raw dump of the cone (for debugging)
    #[arg(long, hide = true)]
    dump_cone: bool,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let Some(radix) = Radix::parse(&args.radix) else {
        eprintln!("error: unknown --radix '{}': expected dec, hex or bin", args.radix);
        return ExitCode::FAILURE;
    };
    // The BDD and expression code recurse deeply on large cones: give them room.
    let worker = std::thread::Builder::new()
        .name("netlist_search".into())
        .stack_size(1 << 30)
        .spawn(move || run(&args, radix));
    let result = match worker {
        Ok(handle) => handle.join(),
        Err(e) => {
            eprintln!("error: cannot start the worker thread: {e}");
            return ExitCode::FAILURE;
        }
    };
    match result {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(e)) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
        Err(_) => {
            eprintln!("error: internal failure (this is a bug in the tool, please report it)");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &Args, radix: Radix) -> Result<()> {
    let t0 = Instant::now();

    let mut lib = CellLib::new();
    for f in &args.lib {
        lib.load_file(f)?;
    }
    if lib.is_empty() {
        return Err(anyhow!("no cell was found in the library file(s)"));
    }
    for w in lib.warnings.iter().take(20) {
        eprintln!("warning: {w}");
    }
    if lib.warnings.len() > 20 {
        eprintln!("warning: ... and {} more library warnings", lib.warnings.len() - 20);
    }
    let t_lib = t0.elapsed();

    let mut maps: Vec<memmap2::Mmap> = Vec::new();
    for p in &args.netlist {
        let file = std::fs::File::open(p).with_context(|| format!("cannot open {}", p.display()))?;
        if file.metadata().map(|m| m.len()).unwrap_or(0) == 0 {
            return Err(anyhow!("{} is empty", p.display()));
        }
        // SAFETY: the mapping is only read. The netlist must not be modified
        // while the tool runs.
        let map = unsafe { memmap2::Mmap::map(&file) }
            .with_context(|| format!("cannot map {}", p.display()))?;
        maps.push(map);
    }
    let sources: Vec<&[u8]> = maps.iter().map(|m| &m[..]).collect();
    let index = ModuleIndex::build(&sources)?;
    if index.modules.is_empty() {
        return Err(anyhow!("no module was found in the netlist file(s)"));
    }
    for w in &index.warnings {
        eprintln!("warning: {w}");
    }
    let t_index = t0.elapsed();

    let design = Design::new(index, &lib);
    let path = design.resolve(args.top.as_deref(), &args.inst)?;
    let module = design.module(path.module())?;
    let bits = design.find_wire_bits(module, &args.wire)?;
    let t_resolve = t0.elapsed();

    let trace_opts = TraceOpts {
        max_nodes: args.max_nodes,
        max_hier_depth: args.max_hier_depth,
        cross: !args.no_cross,
    };
    let analyze_opts = AnalyzeOpts {
        radix,
        expand: args.expand,
        prefer_arith: args.prefer_arith,
        strict: args.strict,
        ..AnalyzeOpts::default()
    }
    .with_effort(args.effort);
    let filter = args.filter.as_deref();

    let mut report = String::new();
    let (mut nodes, mut endpoints) = (0usize, 0usize);
    let (mut t_trace, mut t_lift) = (Duration::ZERO, Duration::ZERO);
    for (i, &bit) in bits.iter().enumerate() {
        if i > 0 {
            report.push('\n');
        }
        let t = Instant::now();
        let cone = trace(&design, &path, bit, &trace_opts)?;
        t_trace += t.elapsed();
        nodes += cone.nodes.len();
        endpoints += cone.endpoints.len();

        let t = Instant::now();
        let shown = wires_to_show(&cone, filter);
        let analysis = (!args.no_lift).then(|| analyze(&cone, Some(&shown), &analyze_opts));
        t_lift += t.elapsed();
        report.push_str(&render(&design, &path, &cone, analysis.as_ref(), &shown, filter));
        if args.dump_cone {
            report.push_str("\nCone dump:\n");
            report.push_str(&cone.dump());
        }
    }

    // Parse warnings of the modules that were actually read.
    let mut warned = 0usize;
    for id in 0..design.index.modules.len() as u32 {
        for w in design.module_warnings(id) {
            warned += 1;
            if warned <= 20 {
                eprintln!("warning: {w}");
            }
        }
    }
    if warned > 20 {
        eprintln!("warning: ... and {} more netlist warnings", warned - 20);
    }

    match &args.output {
        Some(p) => {
            std::fs::write(p, &report).with_context(|| format!("cannot write {}", p.display()))?
        }
        None => std::io::stdout().lock().write_all(report.as_bytes())?,
    }

    if args.stats {
        let size: usize = maps.iter().map(|m| m.len()).sum();
        eprintln!(
            "stats: lib {:.2}s, index {:.2}s, resolve {:.2}s, trace {:.2}s, analyse {:.2}s, total {:.2}s",
            t_lib.as_secs_f64(),
            (t_index - t_lib).as_secs_f64(),
            (t_resolve - t_index).as_secs_f64(),
            t_trace.as_secs_f64(),
            t_lift.as_secs_f64(),
            t0.elapsed().as_secs_f64(),
        );
        eprintln!(
            "stats: netlist {:.1} MB, {} modules ({} parsed), {} lib cells; {} cone(s), {} net bits, {} endpoints",
            size as f64 / 1e6,
            design.index.modules.len(),
            design.parsed_modules(),
            lib.len(),
            bits.len(),
            nodes,
            endpoints,
        );
    }
    Ok(())
}

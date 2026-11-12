//! netlist_search: trace a wire of a gate-level netlist back to its drivers
//! and print the cone logic in RTL-style form.

use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use anyhow::{Context, Result, anyhow};
use clap::Parser;

use netlist_search::liberty::CellLib;
use netlist_search::logic::{AnalyzeOpts, analyze};
use netlist_search::netlist::design::Design;
use netlist_search::netlist::index::ModuleIndex;
use netlist_search::report::{Radix, ReportOpts, render};
use netlist_search::trace::{TraceOpts, trace};

#[derive(Parser, Debug)]
#[command(
    name = "netlist_search",
    version,
    about = "Trace a wire of a gate-level netlist back to its drivers, \
             and print the logic of every wire in the cone in RTL-style form"
)]
struct Args {
    /// Gate-level structural Verilog netlist (may be given several times)
    #[arg(long, required = true, num_args = 1.., value_name = "FILE")]
    netlist: Vec<PathBuf>,

    /// Liberty cell library (may be given several times)
    #[arg(long, required = true, num_args = 1.., value_name = "FILE")]
    lib: Vec<PathBuf>,

    /// Top module, if it cannot be determined automatically
    #[arg(long)]
    top: Option<String>,

    /// Instance path of the module holding the wire, e.g. u_core/u_fsm
    #[arg(long, default_value = "")]
    inst: String,

    /// Wire to trace: name, name[i] or name[msb:lsb]
    #[arg(long)]
    wire: String,

    /// Do not follow drivers across module boundaries
    #[arg(long)]
    no_cross: bool,

    /// Maximum number of module boundaries to cross
    #[arg(long, default_value_t = 8)]
    max_hier_depth: u32,

    /// Maximum number of net bits in the cone
    #[arg(long, default_value_t = 200_000)]
    max_nodes: usize,

    /// Only show wires whose logic depends on an endpoint whose name contains this
    #[arg(long)]
    filter: Option<String>,

    /// How to write constants
    #[arg(long, default_value = "dec")]
    radix: String,

    /// Print endpoint forms even when they are large
    #[arg(long)]
    expand: bool,

    /// Show a wire as a bit of `bus + K` or `bus * K` rather than as the
    /// equivalent range or set test, whenever both describe it
    #[arg(long)]
    prefer_arith: bool,

    /// Only trace and print local forms; skip the endpoint forms
    #[arg(long)]
    no_lift: bool,

    /// Write the report here instead of stdout
    #[arg(short, long)]
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
    // Deep recursion in the netlist walkers and the BDD: give them room.
    let worker = std::thread::Builder::new()
        .name("netlist_search".into())
        .stack_size(512 * 1024 * 1024)
        .spawn(move || run(&args, radix))
        .expect("spawn worker thread");
    match worker.join() {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(e)) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
        Err(_) => {
            eprintln!("error: internal panic (this is a bug; please report it)");
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
        return Err(anyhow!("no cell was loaded from the library files"));
    }
    for w in &lib.warnings {
        eprintln!("warning: {w}");
    }
    let t_lib = t0.elapsed();

    let files: Vec<std::fs::File> = args
        .netlist
        .iter()
        .map(|p| {
            std::fs::File::open(p).with_context(|| format!("cannot open {}", p.display()))
        })
        .collect::<Result<_>>()?;
    let maps: Vec<memmap2::Mmap> = files
        .iter()
        .zip(&args.netlist)
        .map(|(f, p)| {
            // SAFETY: the file is only read, and the mapping is dropped at the end of main.
            unsafe { memmap2::Mmap::map(f) }
                .with_context(|| format!("cannot map {}", p.display()))
        })
        .collect::<Result<_>>()?;
    let sources: Vec<&[u8]> = maps.iter().map(|m| &m[..]).collect();
    let index = ModuleIndex::build(&sources)?;
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
    let report_opts = ReportOpts {
        radix,
        filter: args.filter.clone(),
        expand: args.expand,
        dump_cone: args.dump_cone,
    };

    let analyze_opts = AnalyzeOpts {
        radix,
        expand: args.expand,
        prefer_arith: args.prefer_arith,
        ..AnalyzeOpts::default()
    };

    let mut report = String::new();
    let mut nodes = 0usize;
    let mut endpoints = 0usize;
    let mut t_lift = std::time::Duration::ZERO;
    for (i, &bit) in bits.iter().enumerate() {
        if i > 0 {
            report.push('\n');
        }
        let cone = trace(&design, &path, bit, &trace_opts)?;
        nodes += cone.nodes.len();
        endpoints += cone.endpoints.len();
        let t = Instant::now();
        let analysis = (!args.no_lift).then(|| analyze(&cone, &analyze_opts));
        t_lift += t.elapsed();
        report.push_str(&render(&design, &path, &cone, analysis.as_ref(), &report_opts));
    }
    let t_trace = t0.elapsed();

    match &args.output {
        Some(p) => {
            std::fs::write(p, &report)
                .with_context(|| format!("cannot write {}", p.display()))?;
        }
        None => {
            let mut out = std::io::stdout().lock();
            out.write_all(report.as_bytes())?;
        }
    }

    if args.stats {
        eprintln!(
            "stats: lib {:.2}s, index {:.2}s, resolve {:.2}s, trace {:.2}s, lift {:.2}s, total {:.2}s; \
             {} modules parsed, {} net bits in {} cone(s), {} endpoints",
            t_lib.as_secs_f64(),
            (t_index - t_lib).as_secs_f64(),
            (t_resolve - t_index).as_secs_f64(),
            (t_trace - t_resolve).saturating_sub(t_lift).as_secs_f64(),
            t_lift.as_secs_f64(),
            t0.elapsed().as_secs_f64(),
            design.parsed_modules(),
            nodes,
            bits.len(),
            endpoints,
        );
    }
    Ok(())
}

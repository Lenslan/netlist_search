//! The whole design: lazily parsed modules, cell classification, and
//! resolution of hierarchical instance paths and wire names.

use std::sync::OnceLock;

use anyhow::{Result, anyhow, bail};
use rayon::prelude::*;

use super::index::ModuleIndex;
use super::parser::{BitId, Module};
use crate::liberty::{CellDef, CellLib, Dir, PinDef};

/// Verilog gate primitives. The first terminal is the output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    And,
    Or,
    Nand,
    Nor,
    Xor,
    Xnor,
    Not,
    Buf,
}

impl Builtin {
    fn from_name(n: &[u8]) -> Option<Self> {
        Some(match n {
            b"and" => Builtin::And,
            b"or" => Builtin::Or,
            b"nand" => Builtin::Nand,
            b"nor" => Builtin::Nor,
            b"xor" => Builtin::Xor,
            b"xnor" => Builtin::Xnor,
            b"not" => Builtin::Not,
            b"buf" => Builtin::Buf,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            Builtin::And => "and",
            Builtin::Or => "or",
            Builtin::Nand => "nand",
            Builtin::Nor => "nor",
            Builtin::Xor => "xor",
            Builtin::Xnor => "xnor",
            Builtin::Not => "not",
            Builtin::Buf => "buf",
        }
    }
}

/// What an instantiated type name refers to.
#[derive(Debug)]
pub enum CellRef<'d> {
    Lib(&'d CellDef),
    Module(u32),
    Builtin(Builtin),
    /// Neither in the library nor a module of the netlist: a black box.
    Unknown,
}

/// What one connection of an instance attaches to.
#[derive(Debug)]
pub enum PinInfo<'d> {
    LibPin { cell: &'d CellDef, pin: &'d PinDef },
    ModulePort { module: u32, port: u32, dir: Dir },
    /// Terminal `index` of a gate primitive; 0 is the output.
    BuiltinPin { gate: Builtin, index: usize },
    /// Unknown cell, or a pin the cell does not have.
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    /// Module containing the instance.
    pub parent: u32,
    /// Instance index inside `parent`.
    pub inst: u32,
    /// Module the instance instantiates.
    pub module: u32,
}

/// A module instance, identified by its path from a top module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstPath {
    pub top: u32,
    pub steps: Vec<Step>,
}

impl InstPath {
    /// The module this path ends in.
    pub fn module(&self) -> u32 {
        self.steps.last().map_or(self.top, |s| s.module)
    }
}

pub struct Design<'a> {
    pub index: ModuleIndex<'a>,
    pub lib: &'a CellLib,
    modules: Vec<OnceLock<Result<Module<'a>, String>>>,
    headers: Vec<OnceLock<Result<Module<'a>, String>>>,
    children: Vec<OnceLock<Vec<(u32, u32)>>>,
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

impl<'a> Design<'a> {
    pub fn new(index: ModuleIndex<'a>, lib: &'a CellLib) -> Self {
        let n = index.modules.len();
        Design {
            index,
            lib,
            modules: (0..n).map(|_| OnceLock::new()).collect(),
            headers: (0..n).map(|_| OnceLock::new()).collect(),
            children: (0..n).map(|_| OnceLock::new()).collect(),
        }
    }

    pub fn module_name(&self, id: u32) -> String {
        text(self.index.modules[id as usize].name)
    }

    /// The fully parsed module, parsing it on first use.
    pub fn module(&self, id: u32) -> Result<&Module<'a>> {
        self.modules[id as usize]
            .get_or_init(|| {
                Module::parse(&self.index.modules[id as usize]).map_err(|e| format!("{e:#}"))
            })
            .as_ref()
            .map_err(|e| anyhow!("{e}"))
    }

    /// Number of modules parsed so far (for statistics).
    pub fn parsed_modules(&self) -> usize {
        self.modules.iter().filter(|m| m.get().is_some()).count()
    }

    /// Ports of a module without parsing its body, when possible.
    fn header(&self, id: u32) -> Result<&Module<'a>> {
        if let Some(Ok(m)) = self.modules[id as usize].get() {
            return Ok(m);
        }
        let h = self.headers[id as usize]
            .get_or_init(|| {
                Module::parse_header(&self.index.modules[id as usize])
                    .map_err(|e| format!("{e:#}"))
            })
            .as_ref()
            .map_err(|e| anyhow!("{e}"))?;
        // A port still marked inout may simply be declared after the first
        // instance; only the full parse can tell.
        if h.ports.iter().any(|p| p.dir == Dir::Inout) {
            return self.module(id);
        }
        Ok(h)
    }

    pub fn cell_ref(&self, cell: &[u8]) -> CellRef<'_> {
        if let Some(c) = self.lib.get(cell) {
            CellRef::Lib(c)
        } else if let Some(m) = self.index.find(cell) {
            CellRef::Module(m)
        } else if let Some(b) = Builtin::from_name(cell) {
            CellRef::Builtin(b)
        } else {
            CellRef::Unknown
        }
    }

    /// Classify connection `conn` of instance `inst` in module `m`.
    pub fn pin_info(&self, m: &Module<'a>, inst: u32, conn: u32) -> PinInfo<'_> {
        let pos = (conn - m.inst_conns(inst).start) as usize;
        let pin_name = m.conn_pin(conn);
        match self.cell_ref(m.inst_cell(inst)) {
            CellRef::Lib(cell) => {
                let pin = match pin_name {
                    Some(p) => cell.pin(p),
                    None => cell.pins.get(pos),
                };
                pin.map_or(PinInfo::Unknown, |pin| PinInfo::LibPin { cell, pin })
            }
            CellRef::Module(module) => {
                let Ok(h) = self.header(module) else {
                    return PinInfo::Unknown;
                };
                let port = match pin_name {
                    Some(p) => h.find_port(p),
                    None => (pos < h.ports.len()).then_some(pos as u32),
                };
                port.map_or(PinInfo::Unknown, |port| PinInfo::ModulePort {
                    module,
                    port,
                    dir: h.ports[port as usize].dir,
                })
            }
            CellRef::Builtin(gate) => PinInfo::BuiltinPin { gate, index: pos },
            CellRef::Unknown => PinInfo::Unknown,
        }
    }

    /// Instances of `id` that instantiate other modules: `(inst, child module)`.
    fn children(&self, id: u32) -> &[(u32, u32)] {
        self.children[id as usize].get_or_init(|| {
            let Ok(m) = self.module(id) else {
                return Vec::new();
            };
            (0..m.num_insts())
                .filter_map(|i| self.index.find(m.inst_cell(i)).map(|c| (i, c)))
                .filter(|&(i, _)| self.lib.get(m.inst_cell(i)).is_none())
                .collect()
        })
    }

    // ---- instance paths ----------------------------------------------------

    pub fn path_string(&self, p: &InstPath) -> String {
        let mut s = String::new();
        for step in &p.steps {
            if !s.is_empty() {
                s.push('/');
            }
            if let Ok(m) = self.module(step.parent) {
                s.push_str(&text(m.inst_name(step.inst)));
            }
        }
        s
    }

    /// Follow `rest` down from `module`. Instance names may themselves
    /// contain '/', so every split point is tried, longest name first.
    fn walk(&self, module: u32, rest: &str, why: &mut Option<String>) -> Result<Option<Vec<Step>>> {
        if rest.is_empty() {
            return Ok(Some(Vec::new()));
        }
        let m = self.module(module)?;
        let mut cuts: Vec<usize> = rest.match_indices('/').map(|(i, _)| i).collect();
        cuts.push(rest.len());
        for &cut in cuts.iter().rev() {
            let name = &rest[..cut];
            let Some(inst) = m.find_inst(name.as_bytes()) else {
                continue;
            };
            let tail = rest.get(cut + 1..).unwrap_or("");
            let cell = m.inst_cell(inst);
            match self.cell_ref(cell) {
                CellRef::Module(child) => {
                    if let Some(mut steps) = self.walk(child, tail, why)? {
                        steps.insert(
                            0,
                            Step {
                                parent: module,
                                inst,
                                module: child,
                            },
                        );
                        return Ok(Some(steps));
                    }
                }
                other => {
                    let what = match other {
                        CellRef::Lib(_) => "library cell",
                        CellRef::Builtin(_) => "gate primitive",
                        _ => "unknown cell",
                    };
                    *why = Some(format!(
                        "'{name}' is an instance of {what} {}, not of a module; \
                         give the path of the module instance that contains the wire",
                        text(cell)
                    ));
                }
            }
        }
        Ok(None)
    }

    /// Resolve an instance path. `path` may start with the top module's name,
    /// use '/' or '.' as separator, or be a unique suffix of a full path.
    pub fn resolve(&self, top: Option<&str>, path: &str) -> Result<InstPath> {
        let path = path.trim().trim_matches('/');
        let tops: Vec<u32> = match top {
            Some(t) => vec![
                self.index
                    .find(t.as_bytes())
                    .ok_or_else(|| anyhow!("top module '{t}' not found in the netlist"))?,
            ],
            None => self.index.top_candidates(),
        };
        if tops.is_empty() {
            bail!("no top-level module found (every module is instantiated somewhere); use --top");
        }
        let mut variants = vec![path.to_string()];
        if path.contains('.') {
            variants.push(path.replace('.', "/"));
        }
        let mut why = None;

        // 1. Exact path from a top module.
        let mut found: Vec<InstPath> = Vec::new();
        for v in &variants {
            for &t in &tops {
                let tname = self.module_name(t);
                let mut tries = vec![v.as_str()];
                if v == &tname {
                    tries.push("");
                } else if let Some(rest) = v.strip_prefix(&format!("{tname}/")) {
                    tries.push(rest);
                }
                for rest in tries {
                    if let Some(steps) = self.walk(t, rest, &mut why)? {
                        let p = InstPath { top: t, steps };
                        if !found.contains(&p) {
                            found.push(p);
                        }
                    }
                }
            }
            if !found.is_empty() {
                break;
            }
        }
        // 2. The first segment names some other module: use it as the root.
        if found.is_empty() && top.is_none() {
            for v in &variants {
                let (first, rest) = v.split_once('/').unwrap_or((v, ""));
                if let Some(m) = self.index.find(first.as_bytes())
                    && let Some(steps) = self.walk(m, rest, &mut why)?
                {
                    found.push(InstPath { top: m, steps });
                    break;
                }
            }
        }
        // 3. Unique suffix anywhere in the hierarchy.
        if found.is_empty() && !path.is_empty() {
            for v in &variants {
                found = self.suffix_matches(&tops, v);
                if !found.is_empty() {
                    break;
                }
            }
            if found.len() > 1 {
                let list: Vec<String> = found
                    .iter()
                    .take(20)
                    .map(|p| format!("  {}", self.path_string(p)))
                    .collect();
                bail!(
                    "instance '{path}' is ambiguous: {} instances end with that name; \
                     give a longer path. Candidates:\n{}",
                    found.len(),
                    list.join("\n")
                );
            }
        }
        match found.len() {
            1 => Ok(found.pop().unwrap()),
            0 => Err(self.explain_missing(tops[0], &variants[variants.len() - 1], why)),
            _ => {
                let names: Vec<String> = found.iter().map(|p| self.module_name(p.top)).collect();
                bail!(
                    "'{path}' resolves in several top-level modules ({}); choose one with --top",
                    names.join(", ")
                )
            }
        }
    }

    /// Every module instance whose path ends with `suffix`.
    fn suffix_matches(&self, tops: &[u32], suffix: &str) -> Vec<InstPath> {
        // This needs the whole hierarchy: parse every module, in parallel.
        (0..self.modules.len() as u32).into_par_iter().for_each(|i| {
            let _ = self.module(i);
        });
        let tail = format!("/{suffix}");
        let mut out = Vec::new();
        let mut budget = 5_000_000usize;
        for &t in tops {
            let mut steps = Vec::new();
            let mut path = String::new();
            self.suffix_dfs(t, t, suffix, &tail, &mut steps, &mut path, &mut out, &mut budget);
        }
        out
    }

    #[allow(clippy::too_many_arguments)]
    fn suffix_dfs(
        &self,
        top: u32,
        module: u32,
        suffix: &str,
        tail: &str,
        steps: &mut Vec<Step>,
        path: &mut String,
        out: &mut Vec<InstPath>,
        budget: &mut usize,
    ) {
        let Ok(m) = self.module(module) else { return };
        for &(inst, child) in self.children(module) {
            if *budget == 0 || out.len() >= 50 {
                return;
            }
            *budget -= 1;
            let len = path.len();
            if len > 0 {
                path.push('/');
            }
            path.push_str(&String::from_utf8_lossy(m.inst_name(inst)));
            steps.push(Step {
                parent: module,
                inst,
                module: child,
            });
            if path == suffix || path.ends_with(tail) {
                out.push(InstPath {
                    top,
                    steps: steps.clone(),
                });
            }
            self.suffix_dfs(top, child, suffix, tail, steps, path, out, budget);
            steps.pop();
            path.truncate(len);
        }
    }

    fn explain_missing(&self, top: u32, path: &str, why: Option<String>) -> anyhow::Error {
        if let Some(w) = why {
            return anyhow!("cannot resolve instance path '{path}': {w}");
        }
        // Walk as deep as the path allows, then suggest names at that level.
        let mut module = top;
        let mut done = String::new();
        let mut rest = path;
        'descend: loop {
            let Ok(m) = self.module(module) else { break };
            let mut cuts: Vec<usize> = rest.match_indices('/').map(|(i, _)| i).collect();
            cuts.push(rest.len());
            for &cut in cuts.iter().rev() {
                if let Some(inst) = m.find_inst(rest[..cut].as_bytes())
                    && let CellRef::Module(child) = self.cell_ref(m.inst_cell(inst))
                {
                    if !done.is_empty() {
                        done.push('/');
                    }
                    done.push_str(&rest[..cut]);
                    rest = rest.get(cut + 1..).unwrap_or("");
                    module = child;
                    if rest.is_empty() {
                        break 'descend;
                    }
                    continue 'descend;
                }
            }
            break;
        }
        let want = rest.split('/').next().unwrap_or(rest);
        let mut names: Vec<String> = match self.module(module) {
            Ok(m) => self
                .children(module)
                .iter()
                .map(|&(i, _)| text(m.inst_name(i)))
                .collect(),
            Err(_) => Vec::new(),
        };
        names.sort_by_key(|n| edit_distance(n.as_bytes(), want.as_bytes()));
        names.truncate(6);
        let place = if done.is_empty() {
            format!("module {}", self.module_name(module))
        } else {
            format!("module {} (instance {done})", self.module_name(module))
        };
        if names.is_empty() {
            anyhow!("cannot resolve instance path '{path}': {place} has no module instance named '{want}' (it contains no module instances)")
        } else {
            anyhow!(
                "cannot resolve instance path '{path}': {place} has no module instance named '{want}'; closest: {}",
                names.join(", ")
            )
        }
    }

    // ---- wires -------------------------------------------------------------

    /// Bits named by `wire` in module `m`, MSB first. Accepts `name`,
    /// `name[i]`, `name[m:l]`, and names that literally contain brackets.
    pub fn find_wire_bits(&self, m: &Module<'a>, wire: &str) -> Result<Vec<BitId>> {
        let w = wire.trim();
        let w = w.strip_prefix('\\').unwrap_or(w);
        if let Some(n) = m.find_net(w.as_bytes()) {
            return Ok(m.net_bits(n).collect());
        }
        let mname = text(m.name);
        if let Some(open) = w.rfind('[').filter(|_| w.ends_with(']')) {
            let base = &w[..open];
            let sel = &w[open + 1..w.len() - 1];
            if let Some(n) = m.find_net(base.as_bytes()) {
                let net = &m.nets[n as usize];
                let parse = |s: &str| {
                    s.trim()
                        .parse::<i32>()
                        .map_err(|_| anyhow!("bad index in wire name '{wire}'"))
                };
                let (from, to) = match sel.split_once(':') {
                    Some((a, b)) => (parse(a)?, parse(b)?),
                    None => {
                        let i = parse(sel)?;
                        (i, i)
                    }
                };
                let range = if net.is_vec {
                    format!("range [{}:{}]", net.msb, net.lsb)
                } else {
                    "no range (it is a scalar)".to_string()
                };
                let step = if from <= to { 1 } else { -1 };
                let mut bits = Vec::new();
                let mut i = from;
                loop {
                    let bit = m.bit_of(n, i).filter(|_| net.is_vec).ok_or_else(|| {
                        anyhow!("wire '{wire}': net {base} in module {mname} has {range}; index {i} is outside it")
                    })?;
                    bits.push(bit);
                    if i == to {
                        break;
                    }
                    i += step;
                }
                return Ok(bits);
            }
        }
        // Not found: suggest the closest net names.
        let key = w.as_bytes();
        let mut best: Vec<(usize, &[u8])> = Vec::new();
        for net in &m.nets {
            if net.name.len().abs_diff(key.len()) > 3 {
                continue;
            }
            let d = edit_distance(net.name, key);
            if d <= 3 {
                best.push((d, net.name));
                if best.len() > 4096 {
                    best.sort();
                    best.truncate(8);
                }
            }
        }
        best.sort();
        best.truncate(8);
        if best.is_empty() {
            bail!("wire '{wire}' not found in module {mname}")
        }
        let names: Vec<String> = best.iter().map(|(_, n)| text(n)).collect();
        bail!(
            "wire '{wire}' not found in module {mname}; closest names: {}",
            names.join(", ")
        )
    }
}

/// Levenshtein distance, on at most the first 64 bytes of each string.
fn edit_distance(a: &[u8], b: &[u8]) -> usize {
    let a = &a[..a.len().min(64)];
    let b = &b[..b.len().min(64)];
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for (i, &ca) in a.iter().enumerate() {
        let mut cur = vec![i + 1];
        for (j, &cb) in b.iter().enumerate() {
            let sub = prev[j] + usize::from(ca != cb);
            cur.push(sub.min(prev[j + 1] + 1).min(cur[j] + 1));
        }
        prev = cur;
    }
    prev[b.len()]
}

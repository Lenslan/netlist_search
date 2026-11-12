//! Boolean analysis of a traced cone: naming, BDDs and expression lifting.

pub mod bdd;
pub mod bus;
pub mod expr;
pub mod isop;
pub mod lift;
pub mod sim;
pub mod words;

#[cfg(test)]
mod tests_lift;

use rustc_hash::FxHashMap;

use crate::liberty::BoolExpr;
use crate::trace::{Cone, NodeId, NodeKind};
use bdd::{BResult, Bd, Bdd, FALSE, TRUE};
use bus::VarInfo;
use expr::{Arith, Expr, Radix, Word};
use lift::{LiftOpts, Lifter};

#[derive(Debug, Clone)]
pub struct AnalyzeOpts {
    pub radix: Radix,
    /// Print endpoint forms however large they are.
    pub expand: bool,
    /// Show `(bus + K)[k]` rather than the equivalent range test.
    pub prefer_arith: bool,
    /// Never report a form that is not proven (no simulation matching).
    pub strict: bool,
    /// Total BDD nodes allowed for one cone.
    pub node_limit: usize,
    /// BDD nodes one gate may add before its output is cut.
    pub gate_budget: usize,
    /// Endpoint forms are computed for this many wires, nearest the target first.
    pub max_lift: usize,
    /// Effort (BDD steps) spent on the endpoint form of one wire.
    pub lift_effort: u64,
    /// Effort spent on the endpoint forms of the whole cone.
    pub total_effort: u64,
    /// Endpoint forms larger than this are omitted unless `expand`.
    pub max_size: usize,
}

impl Default for AnalyzeOpts {
    fn default() -> Self {
        AnalyzeOpts {
            radix: Radix::Dec,
            expand: false,
            prefer_arith: false,
            strict: false,
            node_limit: 4_000_000,
            gate_budget: 200_000,
            max_lift: 5_000,
            lift_effort: 3_000_000,
            total_effort: 150_000_000,
            max_size: 64,
        }
    }
}

impl AnalyzeOpts {
    /// Scale the effort limits by `factor` (the `--effort` option).
    pub fn with_effort(mut self, factor: u32) -> Self {
        let f = factor.max(1) as u64;
        self.max_lift = self.max_lift.saturating_mul(f as usize);
        self.lift_effort = self.lift_effort.saturating_mul(f);
        self.total_effort = self.total_effort.saturating_mul(f);
        self
    }
}

/// After a gate was too large, later gates get a smaller budget, down to this.
const MIN_GATE_BUDGET: usize = 10_000;
/// At most this many wires are tried for a simulation match.
const MAX_SIM_CANDIDATES: usize = 512;

/// What the analysis found out about one wire of the cone.
#[derive(Debug, Clone, Default)]
pub struct WireInfo {
    /// The wire as an expression of the cone's endpoints.
    pub endpoint_form: Option<String>,
    /// `endpoint_form` matched in simulation only; it is not proven.
    pub unproven: bool,
    /// Why there is no endpoint form, when there is none.
    pub omitted: Option<String>,
    /// Number of endpoints (and cut wires) the wire depends on.
    pub support: usize,
    /// The function was too large to compute: the wire is treated as an input.
    pub cut: bool,
    /// Other wires of the cone with the same (or the inverted) function.
    pub aliases: Vec<String>,
}

/// Result of analysing a cone, indexed by node id.
#[derive(Debug, Default)]
pub struct Analysis {
    pub wires: Vec<Option<WireInfo>>,
    pub notes: Vec<String>,
}

fn eval_func(b: &mut Bdd, e: &BoolExpr, pin: &dyn Fn(&str) -> Bd) -> BResult {
    Ok(match e {
        BoolExpr::Const(c) => b.constant(*c),
        BoolExpr::Var(v) => pin(v),
        BoolExpr::Not(x) => {
            let f = eval_func(b, x, pin)?;
            b.not(f)?
        }
        BoolExpr::And(xs) => {
            let mut f = TRUE;
            for x in xs {
                let g = eval_func(b, x, pin)?;
                f = b.and(f, g)?;
            }
            f
        }
        BoolExpr::Or(xs) => {
            let mut f = FALSE;
            for x in xs {
                let g = eval_func(b, x, pin)?;
                f = b.or(f, g)?;
            }
            f
        }
        BoolExpr::Xor(x, y) => {
            let f = eval_func(b, x, pin)?;
            let g = eval_func(b, y, pin)?;
            b.xor(f, g)?
        }
    })
}

/// The function of node `id`, given the functions of its inputs.
fn node_func(
    bdd: &mut Bdd,
    cone: &Cone,
    id: NodeId,
    func: &[Bd],
    level_of_ep: &[u32],
    budget: usize,
) -> BResult {
    match &cone.node(id).kind {
        NodeKind::Const(c) => Ok(bdd.constant(*c)),
        NodeKind::Endpoint { ep, inv } => {
            let v = bdd.var(level_of_ep[*ep as usize])?;
            if *inv { bdd.not(v) } else { Ok(v) }
        }
        NodeKind::Alias { src, inv, .. } => {
            let f = func[*src as usize];
            if *inv { bdd.not(f) } else { Ok(f) }
        }
        NodeKind::Gate { func: g, inputs, .. } => {
            bdd.set_budget(budget);
            let r = eval_func(bdd, g, &|pin| {
                inputs
                    .iter()
                    .find(|(p, _)| p == pin)
                    .map_or(FALSE, |(_, i)| func[*i as usize])
            });
            bdd.clear_budget();
            r
        }
    }
}

/// Node count at which collecting garbage is worth it: when half of the room
/// left above the live nodes has been used.
fn gc_threshold(bdd: &Bdd, limit: usize) -> usize {
    let live = bdd.node_count();
    live + (limit.saturating_sub(live) / 2).max(200_000)
}

/// The functions of all nodes of a cone under one variable order.
struct Built {
    bdd: Bdd,
    /// Variables by level: endpoint and sibling bits, then one per cut wire.
    vars: Vec<VarInfo>,
    level_of_ep: Vec<u32>,
    /// Levels from here on are cut wires.
    named: u32,
    func: Vec<Bd>,
    cut: Vec<bool>,
    cuts: usize,
}

/// Compute the function of every node, inputs first. A wire whose function is
/// too large becomes a variable of its own (a cut).
fn build(cone: &Cone, mut vars: Vec<VarInfo>, level_of_ep: Vec<u32>, opts: &AnalyzeOpts) -> Built {
    let named = vars.len() as u32;
    let mut bdd = Bdd::new(opts.node_limit);
    for _ in 0..named {
        bdd.new_var();
    }
    let mut next_bus = vars.iter().map(|v| v.bus + 1).max().unwrap_or(0);
    let n = cone.nodes.len();
    let mut func: Vec<Bd> = vec![FALSE; n];
    let mut cut = vec![false; n];
    let mut cuts = 0usize;
    let mut budget = opts.gate_budget;
    let mut gc_at = gc_threshold(&bdd, opts.node_limit);
    for &id in &cone.topo {
        let mut r = node_func(&mut bdd, cone, id, &func, &level_of_ep, budget);
        if r.is_err() && bdd.node_count() > gc_at {
            // Possibly just out of room: reclaim garbage and try once more.
            bdd.gc(&mut func);
            gc_at = gc_threshold(&bdd, opts.node_limit);
            r = node_func(&mut bdd, cone, id, &func, &level_of_ep, budget);
        }
        func[id as usize] = match r {
            Ok(f) => f,
            Err(_) => {
                cut[id as usize] = true;
                cuts += 1;
                budget = (budget / 2).max(MIN_GATE_BUDGET);
                let name = cone.node(id).name.clone();
                let level = bdd.new_var();
                vars.push(VarInfo {
                    base: name.clone(),
                    name,
                    index: None,
                    bus: next_bus,
                });
                next_bus += 1;
                bdd.var(level).unwrap_or(FALSE)
            }
        };
    }
    Built {
        bdd,
        vars,
        level_of_ep,
        named,
        func,
        cut,
        cuts,
    }
}

/// An alternative variable order: endpoints in the order a depth-first walk
/// from the target first meets them, which follows the structure of the logic
/// instead of the names. Within a bus the most significant bit still comes
/// first. Returns, per level, the index into `names`.
fn fanin_order(cone: &Cone, info: &[VarInfo]) -> Vec<usize> {
    let n_ep = cone.endpoints.len();
    let mut seen = vec![false; cone.nodes.len()];
    let mut placed = vec![false; info.len()];
    let mut order: Vec<usize> = Vec::with_capacity(info.len());
    let mut stack = vec![cone.target];
    while let Some(n) = stack.pop() {
        if std::mem::replace(&mut seen[n as usize], true) {
            continue;
        }
        match &cone.node(n).kind {
            NodeKind::Endpoint { ep, .. } => {
                if !std::mem::replace(&mut placed[*ep as usize], true) {
                    order.push(*ep as usize);
                }
            }
            _ => stack.extend(cone.inputs(n).into_iter().rev()),
        }
    }
    debug_assert!(order.iter().all(|&p| p < n_ep));
    order.extend((0..info.len()).filter(|&p| !placed[p]));
    // Keep the levels each bus occupies, but hand them out MSB first.
    let mut levels_of_bus: FxHashMap<u32, Vec<usize>> = FxHashMap::default();
    for (level, &pos) in order.iter().enumerate() {
        if info[pos].index.is_some() {
            levels_of_bus.entry(info[pos].bus).or_default().push(level);
        }
    }
    for levels in levels_of_bus.values() {
        let mut bits: Vec<usize> = levels.iter().map(|&l| order[l]).collect();
        bits.sort_by_key(|&pos| std::cmp::Reverse(info[pos].index));
        for (&level, pos) in levels.iter().zip(bits) {
            order[level] = pos;
        }
    }
    order
}

/// 64 random input vectors per variable, for function signatures.
fn patterns(n: usize) -> Vec<u64> {
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    (0..n)
        .map(|_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        })
        .collect()
}

fn signature(bdd: &Bdd, f: Bd, pat: &[u64]) -> u64 {
    (0..64).fold(0u64, |acc, k| {
        acc | u64::from(bdd.eval(f, &|v| pat[v as usize] >> k & 1 == 1)) << k
    })
}

/// Compute the function of every wire of the cone and lift it to an expression.
///
/// `wanted`, if given, selects the wires (by node id) that get an entry.
pub fn analyze(cone: &Cone, wanted: Option<&[bool]>, opts: &AnalyzeOpts) -> Analysis {
    let mut notes = Vec::new();
    let n = cone.nodes.len();
    let is_wanted = |id: NodeId| wanted.is_none_or(|w| w[id as usize]);

    // One variable per endpoint, plus the bits that complete their buses.
    let n_ep = cone.endpoints.len();
    let mut names: Vec<String> = cone.endpoints.iter().map(|e| e.name.clone()).collect();
    names.extend(cone.siblings.iter().cloned());
    let (vars, order) = bus::order_vars(&names);
    let levels = |order: &[usize]| {
        let mut level_of_ep = vec![0u32; n_ep];
        for (level, &pos) in order.iter().enumerate() {
            if pos < n_ep {
                level_of_ep[pos] = level as u32;
            }
        }
        level_of_ep
    };

    // Phase 1: the function of every node.
    let mut built = build(cone, vars.clone(), levels(&order), opts);
    if built.cuts > 0 {
        // The name-based order did not fit this logic: try the structural one.
        let mut info: Vec<Option<&VarInfo>> = vec![None; names.len()];
        for (level, &pos) in order.iter().enumerate() {
            info[pos] = Some(&vars[level]);
        }
        let info: Vec<VarInfo> = info.into_iter().map(|v| v.unwrap().clone()).collect();
        let order2 = fanin_order(cone, &info);
        if order2 != order {
            let vars2 = order2.iter().map(|&pos| info[pos].clone()).collect();
            let other = build(cone, vars2, levels(&order2), opts);
            if other.cuts < built.cuts {
                built = other;
            }
        }
    }
    let Built {
        mut bdd,
        vars,
        level_of_ep,
        named,
        mut func,
        cut,
        cuts,
    } = built;
    if cuts > 0 {
        notes.push(format!(
            "the logic of {cuts} wire(s) is too large to compute exactly; they are marked [CUT] and \
             appear under their own names in the endpoint forms of the wires after them"
        ));
    }

    let is_wire = |id: NodeId| {
        matches!(
            cone.node(id).kind,
            NodeKind::Gate { .. } | NodeKind::Alias { .. }
        )
    };
    let wire_ids: Vec<NodeId> = cone.order.iter().copied().filter(|&id| is_wire(id)).collect();

    // Wires with the same function, or the inverted one. Inverted pairs are
    // found by signature first, so complements are only built for candidates.
    let pat = patterns(vars.len());
    let mut by_func: FxHashMap<Bd, Vec<NodeId>> = FxHashMap::default();
    let mut by_sig: FxHashMap<u64, Vec<NodeId>> = FxHashMap::default();
    let mut sig = vec![0u64; n];
    for &id in &wire_ids {
        let f = func[id as usize];
        if f > TRUE {
            sig[id as usize] = signature(&bdd, f, &pat);
            by_func.entry(f).or_default().push(id);
            by_sig.entry(sig[id as usize]).or_default().push(id);
        }
    }
    let mut aliases: Vec<Vec<String>> = vec![Vec::new(); n];
    for &id in &wire_ids {
        let f = func[id as usize];
        if f <= TRUE || !is_wanted(id) {
            continue;
        }
        let name = &cone.node(id).name;
        let mut list: Vec<String> = by_func[&f]
            .iter()
            .filter(|&&o| o != id && cone.node(o).name != *name)
            .map(|&o| format!("== {}", cone.node(o).name))
            .collect();
        if let Some(cands) = by_sig.get(&!sig[id as usize])
            && let Ok(nf) = bdd.not(f)
        {
            list.extend(
                cands
                    .iter()
                    .filter(|&&o| func[o as usize] == nf)
                    .map(|&o| format!("== !{}", cone.node(o).name)),
            );
        }
        if list.len() > 8 {
            let more = list.len() - 8;
            list.truncate(8);
            list.push(format!("... and {more} more"));
        }
        aliases[id as usize] = list;
    }
    drop((by_func, by_sig));

    // Phase 2: endpoint forms, nearest the target first.
    let mut wires: Vec<Option<WireInfo>> = vec![None; n];
    let lift_opts = LiftOpts {
        prefer_arith: opts.prefer_arith,
        ..LiftOpts::default()
    };
    let mut lifter = Lifter::new(&mut bdd, &vars, lift_opts);
    let total_end = lifter.bdd.ops().saturating_add(opts.total_effort);
    let mut gc_at = gc_threshold(lifter.bdd, opts.node_limit);
    let mut lifted = 0usize;
    let mut skipped = 0usize;
    let mut gave_up = 0usize;
    // Wires without an exact form over the endpoints: tried in simulation.
    let mut sim_cands: Vec<NodeId> = Vec::new();
    for &id in &wire_ids {
        if !is_wanted(id) {
            continue;
        }
        let mut info = WireInfo {
            cut: cut[id as usize],
            aliases: std::mem::take(&mut aliases[id as usize]),
            ..WireInfo::default()
        };
        if info.cut {
            sim_cands.push(id);
            wires[id as usize] = Some(info);
            continue;
        }
        if lifted >= opts.max_lift || lifter.bdd.ops() >= total_end {
            skipped += 1;
            info.omitted = Some("not computed: analysis limit reached, see Notes".into());
            wires[id as usize] = Some(info);
            continue;
        }
        lifted += 1;
        let f = func[id as usize];
        let support = lifter.bdd.support(f);
        info.support = support.len();
        let over_cuts = support.last().is_some_and(|&v| v >= named);
        lifter
            .bdd
            .set_ops_limit(lifter.bdd.ops().saturating_add(opts.lift_effort).min(total_end));
        let e = lifter.lift(f);
        let exhausted = lifter.bdd.ops_exhausted();
        lifter.bdd.clear_ops_limit();
        if lifter.take_mismatch() {
            notes.push(format!(
                "INTERNAL: lifted expression mismatch for {}; only its local form is shown \
                 (this is a bug in the tool, please report it)",
                cone.node(id).name
            ));
        }
        match e {
            Some(e) if opts.expand || e.size() <= opts.max_size => {
                info.endpoint_form = Some(e.render(&vars, opts.radix));
            }
            Some(e) => {
                info.omitted = Some(format!(
                    "omitted: {} terms over {} inputs; use --expand to print it",
                    e.size(),
                    info.support
                ));
            }
            None if exhausted => {
                gave_up += 1;
                info.omitted = Some(format!(
                    "not computed: too complex ({} inputs); see the local form",
                    info.support
                ));
            }
            None => {
                info.omitted = Some(format!(
                    "no compact form ({} inputs); see the local form",
                    info.support
                ));
            }
        }
        if info.endpoint_form.is_none() || over_cuts {
            sim_cands.push(id);
        }
        wires[id as usize] = Some(info);
        if lifter.bdd.node_count() > gc_at {
            lifter.gc(&mut func);
            gc_at = gc_threshold(lifter.bdd, opts.node_limit);
        }
    }
    if skipped > 0 {
        notes.push(format!(
            "endpoint forms were computed for the {lifted} wires nearest the target; {skipped} farther \
             wires only have their local form. Narrow the report with --filter, or raise the limit \
             with --effort"
        ));
    }
    if gave_up > 0 {
        notes.push(format!(
            "{gave_up} wire(s) were too complex for an endpoint form within the effort limit \
             (raise it with --effort)"
        ));
    }

    // Wide products cannot be proven with BDDs; match them in simulation.
    if !opts.strict && !sim_cands.is_empty() {
        sim_cands.truncate(MAX_SIM_CANDIDATES);
        let found = sim::match_products(cone, &sim_cands, &vars, &level_of_ep);
        for m in &found {
            let e = Expr::ArithBit {
                op: Arith::Mul,
                a: Word::vars(&m.a, m.signed),
                b: Word::vars(&m.b, m.signed),
                cin: None,
                bit: m.bit,
            };
            if let Some(info) = wires[m.node as usize].as_mut() {
                info.endpoint_form = Some(e.render(&vars, opts.radix));
                info.unproven = true;
                info.omitted = None;
            }
        }
        if !found.is_empty() {
            notes.push(format!(
                "{} endpoint form(s) are marked [simulation-matched, unproven]: the gates agree with \
                 the product on {} random input vectors, but a multiplier of this width cannot be \
                 proven by this tool. Use --strict to suppress such results",
                found.len(),
                sim::VECTORS
            ));
        }
    }
    Analysis { wires, notes }
}

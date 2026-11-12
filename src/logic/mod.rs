//! Boolean analysis of a traced cone: naming, BDDs and expression lifting.

pub mod bdd;
pub mod bus;
pub mod expr;
pub mod isop;
pub mod lift;
pub mod words;

#[cfg(test)]
mod tests_lift;

use rustc_hash::FxHashMap;

use crate::liberty::BoolExpr;
use crate::trace::{Cone, NodeId, NodeKind};
use bdd::{BResult, Bd, Bdd, FALSE, TRUE};
use bus::VarInfo;
use expr::Radix;
use lift::{LiftOpts, Lifter};

#[derive(Debug, Clone)]
pub struct AnalyzeOpts {
    pub radix: Radix,
    /// Print endpoint forms however large they are.
    pub expand: bool,
    /// Show `(bus + K)[k]` rather than the equivalent range test.
    pub prefer_arith: bool,
    /// Total BDD nodes allowed for one cone.
    pub node_limit: usize,
    /// BDD nodes one gate may add before its output is cut.
    pub gate_budget: usize,
    /// Endpoint forms are computed for this many wires, nearest the target first.
    pub max_lift: usize,
    /// Endpoint forms larger than this are omitted unless `expand`.
    pub max_size: usize,
}

impl Default for AnalyzeOpts {
    fn default() -> Self {
        AnalyzeOpts {
            radix: Radix::Dec,
            expand: false,
            prefer_arith: false,
            node_limit: 4_000_000,
            gate_budget: 200_000,
            max_lift: 5_000,
            max_size: 64,
        }
    }
}

/// What the analysis found out about one wire of the cone.
#[derive(Debug, Clone, Default)]
pub struct WireInfo {
    /// The wire as an expression of the cone's endpoints.
    pub endpoint_form: Option<String>,
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

/// Compute the function of every wire of the cone and lift it to an expression.
pub fn analyze(cone: &Cone, opts: &AnalyzeOpts) -> Analysis {
    let mut notes = Vec::new();
    let names: Vec<String> = cone.endpoints.iter().map(|e| e.name.clone()).collect();
    let (mut vars, order) = bus::order_vars(&names);
    let mut level_of_ep = vec![0u32; names.len()];
    for (level, &ep) in order.iter().enumerate() {
        level_of_ep[ep] = level as u32;
    }
    let mut bdd = Bdd::new(opts.node_limit);
    for _ in 0..vars.len() {
        bdd.new_var();
    }
    let mut next_bus = vars.iter().map(|v| v.bus + 1).max().unwrap_or(0);

    // Phase 1: the BDD of every node, inputs first.
    let n = cone.nodes.len();
    let mut func: Vec<Bd> = vec![FALSE; n];
    let mut cut = vec![false; n];
    let mut cuts = 0usize;
    for &id in &cone.topo {
        let node = cone.node(id);
        let r: BResult = match &node.kind {
            NodeKind::Const(c) => Ok(bdd.constant(*c)),
            NodeKind::Endpoint { ep, inv } => match bdd.var(level_of_ep[*ep as usize]) {
                Ok(v) if *inv => bdd.not(v),
                other => other,
            },
            NodeKind::Alias { src, inv, .. } => {
                let f = func[*src as usize];
                if *inv { bdd.not(f) } else { Ok(f) }
            }
            NodeKind::Gate { func: g, inputs, .. } => {
                bdd.set_budget(opts.gate_budget);
                let r = eval_func(&mut bdd, g, &|pin| {
                    inputs
                        .iter()
                        .find(|(p, _)| p == pin)
                        .map_or(FALSE, |(_, i)| func[*i as usize])
                });
                bdd.clear_budget();
                r
            }
        };
        func[id as usize] = match r {
            Ok(f) => f,
            Err(_) => {
                // Too large: from here on this wire is an input of its own.
                cut[id as usize] = true;
                cuts += 1;
                let level = bdd.new_var();
                vars.push(VarInfo {
                    name: node.name.clone(),
                    base: node.name.clone(),
                    index: None,
                    bus: next_bus,
                });
                next_bus += 1;
                bdd.var(level).unwrap_or(FALSE)
            }
        };
    }
    if cuts > 0 {
        notes.push(format!(
            "the logic of {cuts} wire(s) was too large to compute exactly; they are marked [CUT] and \
             appear as inputs in the endpoint forms of the wires after them"
        ));
    }

    // Wires with equal or complementary functions.
    let is_wire = |id: NodeId| {
        matches!(
            cone.node(id).kind,
            NodeKind::Gate { .. } | NodeKind::Alias { .. }
        )
    };
    let mut by_func: FxHashMap<Bd, Vec<NodeId>> = FxHashMap::default();
    for &id in &cone.order {
        if is_wire(id) && func[id as usize] > TRUE {
            by_func.entry(func[id as usize]).or_default().push(id);
        }
    }

    // Phase 2: lift, nearest the target first.
    let mut wires: Vec<Option<WireInfo>> = vec![None; n];
    let lift_opts = LiftOpts {
        prefer_arith: opts.prefer_arith,
        ..LiftOpts::default()
    };
    let mut lifter = Lifter::new(&mut bdd, &vars, lift_opts);
    let mut lifted = 0usize;
    let mut skipped = 0usize;
    for &id in &cone.order {
        if !is_wire(id) {
            continue;
        }
        let f = func[id as usize];
        let mut info = WireInfo {
            cut: cut[id as usize],
            ..WireInfo::default()
        };
        if info.cut {
            wires[id as usize] = Some(info);
            continue;
        }
        info.support = lifter.bdd.support(f).len();
        if lifted >= opts.max_lift {
            skipped += 1;
            info.omitted = Some("not computed: too far from the target (see Notes)".into());
        } else {
            lifted += 1;
            match lifter.lift(f) {
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
                None => {
                    info.omitted = Some(format!(
                        "no compact form found ({} inputs); see the local form",
                        info.support
                    ));
                }
            }
        }
        let name = &cone.node(id).name;
        let mut aliases = Vec::new();
        if f > TRUE {
            if let Some(same) = by_func.get(&f) {
                aliases.extend(
                    same.iter()
                        .filter(|&&o| o != id && cone.node(o).name != *name)
                        .map(|&o| format!("== {}", cone.node(o).name)),
                );
            }
            if let Ok(nf) = lifter.bdd.not(f)
                && let Some(inv) = by_func.get(&nf)
            {
                aliases.extend(inv.iter().map(|&o| format!("== !{}", cone.node(o).name)));
            }
        }
        if aliases.len() > 8 {
            let more = aliases.len() - 8;
            aliases.truncate(8);
            aliases.push(format!("... and {more} more"));
        }
        info.aliases = aliases;
        wires[id as usize] = Some(info);
    }
    if skipped > 0 {
        notes.push(format!(
            "endpoint forms were computed for the {} wires nearest the target; {skipped} farther wires \
             only have their local form",
            opts.max_lift
        ));
    }
    notes.append(&mut lifter.notes);
    Analysis { wires, notes }
}

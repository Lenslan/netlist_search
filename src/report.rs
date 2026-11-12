//! Text report of one traced cone.

use std::fmt::Write;

use crate::liberty::BoolExpr;
use crate::logic::Analysis;
use crate::logic::bus::split_index;
use crate::netlist::design::{Design, InstPath};
use crate::trace::{Cone, EndpointKind, NodeId, NodeKind};

pub use crate::logic::expr::Radix;

/// Does the signal called `name` match the `--filter` pattern?
///
/// A pattern names a signal: `state` matches every bit of the bus `state`,
/// `state[2]` one bit. A pattern without a path also matches the signal in
/// any instance (`mode` matches `/u_core/u_cfg/mode`).
pub fn filter_matches(name: &str, pattern: &str) -> bool {
    let pattern = pattern.trim();
    let one = |n: &str| n == pattern || split_index(n).0 == pattern;
    if one(name) {
        return true;
    }
    if !pattern.contains('/')
        && let Some(i) = name.rfind('/')
    {
        return one(&name[i + 1..]);
    }
    false
}

/// Which nodes are wires to print. With a filter, only the wires whose logic
/// depends on a signal matching it. The flag is false for non-wire nodes.
pub fn wires_to_show(cone: &Cone, filter: Option<&str>) -> Vec<bool> {
    let is_wire = |n: usize| {
        matches!(
            cone.nodes[n].kind,
            NodeKind::Gate { .. } | NodeKind::Alias { .. }
        )
    };
    let Some(pattern) = filter else {
        return (0..cone.nodes.len()).map(is_wire).collect();
    };
    let mut marked: Vec<bool> = cone
        .nodes
        .iter()
        .map(|n| filter_matches(&n.name, pattern))
        .collect();
    // `topo` lists inputs before their users: one forward pass propagates.
    for &n in &cone.topo {
        if !marked[n as usize] && cone.inputs(n).iter().any(|&d| marked[d as usize]) {
            marked[n as usize] = true;
        }
    }
    (0..cone.nodes.len()).map(|n| marked[n] && is_wire(n)).collect()
}

fn kind_rank(k: EndpointKind) -> u8 {
    match k {
        EndpointKind::Reg => 0,
        EndpointKind::Latch => 1,
        EndpointKind::PortIn => 2,
        EndpointKind::SubmoduleOut => 3,
        EndpointKind::Unknown => 4,
        EndpointKind::BlackBox => 5,
        EndpointKind::Inout => 6,
        EndpointKind::ComplexAssign => 7,
        EndpointKind::ConstX => 8,
        EndpointKind::Undriven => 9,
        EndpointKind::MultiDriver => 10,
        EndpointKind::Loop => 11,
        EndpointKind::Truncated => 12,
    }
}

/// Render the report for one traced bit. `shown` is from `wires_to_show`.
pub fn render(
    design: &Design,
    path: &InstPath,
    cone: &Cone,
    analysis: Option<&Analysis>,
    shown: &[bool],
    filter: Option<&str>,
) -> String {
    let mut s = String::new();
    let module = design.module_name(path.module());
    let inst = design.path_string(path);
    let (target, place) = if inst.is_empty() {
        (cone.node(cone.target).name.clone(), format!("module {module}"))
    } else {
        (
            format!("{inst}/{}", cone.node(cone.target).name),
            format!("module {module}, instance {inst}"),
        )
    };
    let _ = writeln!(s, "=== Cone of {target}   ({place}) ===");
    let _ = writeln!(s);

    // ---- endpoints ---------------------------------------------------------
    if cone.endpoints.is_empty() {
        let _ = writeln!(s, "Endpoints: none (the cone is constant)");
    } else {
        let mut order: Vec<usize> = (0..cone.endpoints.len()).collect();
        let key = |i: usize| {
            let e = &cone.endpoints[i];
            let (base, idx) = split_index(&e.name);
            (kind_rank(e.kind), base, -idx.unwrap_or(0))
        };
        order.sort_by_cached_key(|&i| key(i));
        let mut counts: Vec<(EndpointKind, usize)> = Vec::new();
        for &i in &order {
            let k = cone.endpoints[i].kind;
            match counts.last_mut() {
                Some((last, n)) if *last == k => *n += 1,
                _ => counts.push((k, 1)),
            }
        }
        let summary: Vec<String> = counts
            .iter()
            .map(|(k, n)| format!("{n} {}", k.label()))
            .collect();
        let _ = writeln!(s, "Endpoints ({}): {}", order.len(), summary.join(", "));
        let width = order
            .iter()
            .map(|&i| cone.endpoints[i].kind.label().len() + cone.endpoints[i].name.len())
            .max()
            .unwrap_or(0)
            .min(48);
        for i in order {
            let e = &cone.endpoints[i];
            let head = format!("[{}] {}", e.kind.label(), e.name);
            let mut line = format!("  {head:<w$}", w = width + 3);
            if let Some(inst) = &e.inst {
                let _ = write!(line, "  inst {inst}");
            }
            if let Some(cell) = &e.cell {
                let _ = write!(line, "  {cell}");
            }
            let _ = writeln!(s, "{}", line.trim_end());
        }
    }
    let _ = writeln!(s);

    // ---- wires -------------------------------------------------------------
    let wires: Vec<NodeId> = cone
        .order
        .iter()
        .copied()
        .filter(|&n| shown[n as usize])
        .collect();
    match filter {
        Some(f) => {
            let total = wires_to_show(cone, None).iter().filter(|&&b| b).count();
            let _ = writeln!(
                s,
                "Wires ({} of {total} depend on '{f}'), by distance from the target:",
                wires.len()
            );
            if wires.is_empty() {
                let _ = writeln!(s, "  (no signal of this cone is called '{f}')");
            }
        }
        None => {
            let _ = writeln!(s, "Wires ({}), by distance from the target:", wires.len());
        }
    }
    let name_width = wires
        .iter()
        .map(|&n| cone.node(n).name.len())
        .max()
        .unwrap_or(0)
        .min(40);
    for n in wires {
        let node = cone.node(n);
        let head = format!("d{} {:<w$}", node.depth, node.name, w = name_width);
        match &node.kind {
            NodeKind::Gate {
                cell,
                inst,
                inputs,
                func,
                ..
            } => {
                let _ = writeln!(s, "  {head}  {cell} {inst}");
                let local = render_bool(func, &|var| {
                    inputs
                        .iter()
                        .find(|(p, _)| p == var)
                        .map(|(_, i)| cone.node(*i).name.clone())
                        .unwrap_or_else(|| var.to_string())
                });
                let _ = writeln!(s, "        local:    {local}");
            }
            NodeKind::Alias { src, inv, via } => {
                let _ = writeln!(s, "  {head}  ({via})");
                let bang = if *inv { "!" } else { "" };
                let _ = writeln!(s, "        local:    {bang}{}", cone.node(*src).name);
            }
            _ => continue,
        }
        if let Some(a) = analysis
            && let Some(info) = &a.wires[n as usize]
        {
            if let Some(form) = &info.endpoint_form {
                let mark = if info.unproven {
                    "   [simulation-matched, unproven]"
                } else {
                    ""
                };
                let _ = writeln!(s, "        endpoint: {form}{mark}");
            } else if info.cut {
                let _ = writeln!(s, "        endpoint: [CUT] too large to compute; see the local form");
            } else if let Some(why) = &info.omitted {
                let _ = writeln!(s, "        endpoint: <{why}>");
            }
            if !info.aliases.is_empty() {
                let _ = writeln!(s, "        aliases:  {}", info.aliases.join(", "));
            }
        }
    }
    let _ = writeln!(s);

    // ---- notes -------------------------------------------------------------
    // Everything uncertain goes here: what the tracer assumed, what the
    // analysis could not do, and what each unusual endpoint is.
    let mut notes: Vec<String> = cone.notes.clone();
    if let Some(a) = analysis {
        notes.extend(a.notes.iter().cloned());
    }
    let mut order: Vec<&crate::trace::Endpoint> = cone
        .endpoints
        .iter()
        .filter(|e| !e.detail.is_empty())
        .collect();
    order.sort_by_key(|e| kind_rank(e.kind));
    const MAX_DETAILS: usize = 50;
    notes.extend(
        order
            .iter()
            .take(MAX_DETAILS)
            .map(|e| format!("[{}] {}: {}", e.kind.label(), e.name, e.detail)),
    );
    if order.len() > MAX_DETAILS {
        notes.push(format!(
            "... and {} more endpoints of the kinds above",
            order.len() - MAX_DETAILS
        ));
    }
    if !notes.is_empty() {
        let _ = writeln!(s, "Notes:");
        for n in &notes {
            let _ = writeln!(s, "  - {n}");
        }
    }
    s
}

/// Render a library function with its pins replaced by net names.
///
/// The only precedence the output relies on is `&` over `|`; every other
/// nesting is parenthesised.
pub fn render_bool(e: &BoolExpr, name: &dyn Fn(&str) -> String) -> String {
    render_prec(e, name, LOOSE)
}

const LOOSE: u8 = 0;
const OR: u8 = 1;
const AND: u8 = 2;
const ATOM: u8 = 3;

fn xor_operands<'e>(e: &'e BoolExpr, out: &mut Vec<&'e BoolExpr>) {
    match e {
        BoolExpr::Xor(a, b) => {
            xor_operands(a, out);
            xor_operands(b, out);
        }
        other => out.push(other),
    }
}

fn render_prec(e: &BoolExpr, name: &dyn Fn(&str) -> String, min: u8) -> String {
    let join = |xs: &[&BoolExpr], sep: &str, child_min: u8| {
        xs.iter()
            .map(|x| render_prec(x, name, child_min))
            .collect::<Vec<_>>()
            .join(sep)
    };
    let (body, prec) = match e {
        BoolExpr::Const(true) => ("1'b1".to_string(), ATOM),
        BoolExpr::Const(false) => ("1'b0".to_string(), ATOM),
        BoolExpr::Var(v) => (name(v), ATOM),
        BoolExpr::Not(x) => (format!("!{}", render_prec(x, name, ATOM)), ATOM),
        BoolExpr::And(xs) => (join(&xs.iter().collect::<Vec<_>>(), " & ", ATOM), AND),
        BoolExpr::Or(xs) => (join(&xs.iter().collect::<Vec<_>>(), " | ", AND), OR),
        BoolExpr::Xor(..) => {
            let mut ops = Vec::new();
            xor_operands(e, &mut ops);
            (join(&ops, " ^ ", ATOM), LOOSE)
        }
    };
    if prec < min {
        format!("({body})")
    } else {
        body
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liberty::func::parse_function;

    fn local(func: &str) -> String {
        render_bool(&parse_function(func).unwrap(), &|v| v.to_lowercase())
    }

    #[test]
    fn and_terms_inside_or_need_no_parentheses() {
        assert_eq!(local("(S&B)|(!S&A)"), "s & b | !s & a");
        assert_eq!(local("A|B|C"), "a | b | c");
    }

    #[test]
    fn every_other_nesting_is_parenthesised() {
        assert_eq!(local("(A|B)&C"), "(a | b) & c");
        assert_eq!(local("!((A0&A1)|B0)"), "!(a0 & a1 | b0)");
        assert_eq!(local("!(A|B|C|D)"), "!(a | b | c | d)");
        assert_eq!(local("(A^B)&C"), "(a ^ b) & c");
        assert_eq!(local("(A&B)^C"), "(a & b) ^ c");
        assert_eq!(local("(A^B)|C"), "(a ^ b) | c");
        assert_eq!(local("!(A^B)"), "!(a ^ b)");
    }

    #[test]
    fn xor_chains_are_flat() {
        assert_eq!(local("A^B^CI"), "a ^ b ^ ci");
    }

    #[test]
    fn filter_matches_whole_signal_names_only() {
        assert!(filter_matches("state[3]", "state"));
        assert!(filter_matches("state[3]", "state[3]"));
        assert!(!filter_matches("state[3]", "state[2]"));
        assert!(!filter_matches("nstate[3]", "state"));
        assert!(filter_matches("mode", "mode"));
        assert!(filter_matches("cnt_3_", "cnt"));
    }

    #[test]
    fn filter_without_a_path_matches_in_any_instance() {
        assert!(filter_matches("/u_core/u_cfg/mode", "mode"));
        assert!(filter_matches("/u_core/u_cfg/mode[1]", "mode"));
        assert!(filter_matches("/u_core/u_cfg/mode", "/u_core/u_cfg/mode"));
        assert!(!filter_matches("/u_core/u_cfg/mode", "/u_x/mode"));
        assert!(!filter_matches("/u_core/u_cfg/mode", "u_cfg"));
    }
}

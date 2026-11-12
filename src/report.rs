//! Text report of one traced cone.

use std::fmt::Write;

use crate::logic::Analysis;
use crate::netlist::design::{Design, InstPath};
use crate::liberty::BoolExpr;
use crate::trace::{Cone, NodeId, NodeKind};

pub use crate::logic::expr::Radix;

#[derive(Debug, Clone)]
pub struct ReportOpts {
    pub radix: Radix,
    /// Only show wires whose logic depends on an endpoint whose name contains this.
    pub filter: Option<String>,
    /// Print endpoint forms even when they exceed the size budget.
    pub expand: bool,
    pub dump_cone: bool,
}

impl Default for ReportOpts {
    fn default() -> Self {
        ReportOpts {
            radix: Radix::Dec,
            filter: None,
            expand: false,
            dump_cone: false,
        }
    }
}

/// Render the whole report for one traced bit.
pub fn render(
    design: &Design,
    path: &InstPath,
    cone: &Cone,
    analysis: Option<&Analysis>,
    opts: &ReportOpts,
) -> String {
    let mut s = String::new();
    let module = design.module_name(path.module());
    let inst = design.path_string(path);
    let target = format!(
        "{}{}",
        if inst.is_empty() { String::new() } else { format!("{inst}/") },
        cone.node(cone.target).name
    );
    let _ = writeln!(
        s,
        "=== Cone of {target}   (module {module}{}) ===",
        if inst.is_empty() { String::new() } else { format!(", instance {inst}") }
    );
    let _ = writeln!(s);

    if cone.endpoints.is_empty() {
        let _ = writeln!(s, "Endpoints: none (the whole cone is constant or unconnected)");
    } else {
        let _ = writeln!(s, "Endpoints ({}):", cone.endpoints.len());
        for e in &cone.endpoints {
            let mut line = format!("  [{}] {} ", e.kind.label(), e.name);
            if line.len() < 34 {
                line.push_str(&" ".repeat(34 - line.len()));
            } else {
                line.push(' ');
            }
            if let Some(inst) = &e.inst {
                let _ = write!(line, "inst {inst} ");
            }
            if let Some(cell) = &e.cell {
                let _ = write!(line, "{cell}");
            }
            let _ = writeln!(s, "{}", line.trim_end());
        }
    }
    let _ = writeln!(s);

    let marked = opts.filter.as_ref().map(|f| depended_on(cone, analysis, f));
    let wires: Vec<NodeId> = cone
        .order
        .iter()
        .copied()
        .filter(|&n| {
            matches!(cone.node(n).kind, NodeKind::Gate { .. } | NodeKind::Alias { .. })
                && marked.as_ref().is_none_or(|m| m[n as usize])
        })
        .collect();
    let _ = writeln!(s, "Wires ({}), by distance from the target:", wires.len());
    for n in wires {
        let node = cone.node(n);
        let _ = write!(s, "  d{} {}", node.depth, node.name);
        match &node.kind {
            NodeKind::Gate {
                cell, inst, inputs, func, ..
            } => {
                let mut pad = 30usize.saturating_sub(node.name.len());
                if pad < 2 {
                    pad = 2;
                }
                let _ = write!(s, "{}{cell}", " ".repeat(pad));
                if !inst.is_empty() {
                    let _ = write!(s, " {inst}");
                }
                let local = render_bool(func, &|var| {
                    inputs
                        .iter()
                        .find(|(p, _)| p == var)
                        .map(|(_, i)| cone.node(*i).name.clone())
                        .unwrap_or_else(|| var.to_string())
                });
                let _ = writeln!(s, "\n        local:    {local}");
            }
            NodeKind::Alias { src, inv, via } => {
                let _ = writeln!(
                    s,
                    "\n        local:    {}{}  ({via})",
                    if *inv { "!" } else { "" },
                    cone.node(*src).name
                );
            }
            _ => {}
        }
        if let Some(a) = analysis
            && let Some(info) = &a.wires[n as usize]
        {
            if let Some(form) = &info.endpoint_form {
                let _ = writeln!(s, "        endpoint: {form}");
            } else if info.cut {
                let _ = writeln!(s, "        endpoint: [CUT] logic too large to compute");
            } else if let Some(why) = &info.omitted {
                let _ = writeln!(s, "        endpoint: <{why}>");
            }
            if !info.aliases.is_empty() {
                let _ = writeln!(s, "        aliases:  {}", info.aliases.join(", "));
            }
        }
    }
    let _ = writeln!(s);

    // Everything uncertain goes here: trace notes, analysis notes, and what
    // each non-obvious endpoint is.
    let mut notes: Vec<String> = cone.notes.clone();
    if let Some(a) = analysis {
        notes.extend(a.notes.iter().cloned());
    }
    notes.extend(
        cone.endpoints
            .iter()
            .filter(|e| !e.detail.is_empty())
            .map(|e| format!("[{}] {}: {}", e.kind.label(), e.name, e.detail)),
    );
    if !notes.is_empty() {
        let _ = writeln!(s, "Notes:");
        for n in &notes {
            let _ = writeln!(s, "  - {n}");
        }
    }
    if opts.dump_cone {
        let _ = writeln!(s, "\nCone dump:\n{}", cone.dump());
    }
    s
}

/// Nodes whose logic depends on an endpoint whose name contains `pat`.
fn depended_on(cone: &Cone, analysis: Option<&Analysis>, pat: &str) -> Vec<bool> {
    let mut marked = vec![false; cone.nodes.len()];
    for (n, node) in cone.nodes.iter().enumerate() {
        let own = match &node.kind {
            NodeKind::Endpoint { ep, .. } => cone.endpoints[*ep as usize].name.contains(pat),
            _ => false,
        };
        // An endpoint form mentioning the signal also counts.
        let lifted = analysis
            .and_then(|a| a.wires[n].as_ref())
            .and_then(|w| w.endpoint_form.as_ref())
            .is_some_and(|f| f.contains(pat));
        marked[n] = own || lifted;
    }
    // topo lists inputs before their users, so one forward pass suffices.
    for &n in cone.topo.iter() {
        let deps: Vec<NodeId> = cone.inputs(n);
        if deps.iter().any(|&d| marked[d as usize]) {
            marked[n as usize] = true;
        }
    }
    marked
}

/// Render a library function, substituting its variables.
pub fn render_bool(e: &BoolExpr, name: &dyn Fn(&str) -> String) -> String {
    render_prec(e, name, 0)
}

/// Precedence: or < and < xor < not.
fn prec(e: &BoolExpr) -> u8 {
    match e {
        BoolExpr::Or(_) => 0,
        BoolExpr::And(_) => 1,
        BoolExpr::Xor(..) => 2,
        BoolExpr::Not(_) | BoolExpr::Var(_) | BoolExpr::Const(_) => 3,
    }
}

fn render_prec(e: &BoolExpr, name: &dyn Fn(&str) -> String, min: u8) -> String {
    let op = |xs: &[BoolExpr], sep: &str| {
        xs.iter()
            .map(|x| render_prec(x, name, prec(e) + 1))
            .collect::<Vec<_>>()
            .join(sep)
    };
    let body = match e {
        BoolExpr::Const(true) => "1'b1".to_string(),
        BoolExpr::Const(false) => "1'b0".to_string(),
        BoolExpr::Var(v) => name(v),
        BoolExpr::Not(x) => match &**x {
            BoolExpr::Var(v) => format!("!{}", name(v)),
            other => format!("!{}", render_prec(other, name, prec(e))),
        },
        BoolExpr::And(xs) => op(xs, " & "),
        BoolExpr::Or(xs) => op(xs, " | "),
        BoolExpr::Xor(a, b) => format!(
            "{} ^ {}",
            render_prec(a, name, prec(e)),
            render_prec(b, name, prec(e) + 1)
        ),
    };
    if prec(e) < min {
        format!("({body})")
    } else {
        body
    }
}

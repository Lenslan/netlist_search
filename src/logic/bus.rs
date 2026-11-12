//! Names: splitting `base[index]`, deriving a signal name from a register
//! instance name, and choosing a BDD variable order from bus structure.

/// Split a bit name into its bus base and index.
///
/// `cnt[3]` → (`cnt`, 3); `cnt_3_` (the form some tools write buses in) →
/// (`cnt`, 3); `n12` → (`n12`, None).
pub fn split_index(name: &str) -> (String, Option<i64>) {
    if let Some(body) = name.strip_suffix(']')
        && let Some(open) = body.rfind('[')
        && open > 0
        && let Ok(i) = body[open + 1..].parse::<i64>()
    {
        return (name[..open].to_string(), Some(i));
    }
    if let Some(body) = name.strip_suffix('_') {
        let digits = body.len() - body.trim_end_matches(|c: char| c.is_ascii_digit()).len();
        if digits > 0 {
            let head = &body[..body.len() - digits];
            if let Some(base) = head.strip_suffix('_')
                && !base.is_empty()
                && !base.ends_with('/')
                && let Ok(i) = body[body.len() - digits..].parse::<i64>()
            {
                return (base.to_string(), Some(i));
            }
        }
    }
    (name.to_string(), None)
}

/// The RTL signal a register instance most likely holds, from its name:
/// `cnt_reg[3]` → `cnt[3]`, `cnt_reg_3_` → `cnt[3]`, `cnt_reg` → `cnt`.
/// Returns `None` if the name does not follow the `<signal>_reg<index>` form.
pub fn reg_signal_name(inst: &str) -> Option<String> {
    let at = inst.rfind("_reg")?;
    let base = &inst[..at];
    if base.is_empty() || base.ends_with('/') {
        return None;
    }
    let mut rest = &inst[at + 4..];
    let mut out = base.to_string();
    while !rest.is_empty() {
        if let Some(r) = rest.strip_prefix('[') {
            let close = r.find(']')?;
            r[..close].parse::<i64>().ok()?;
            out.push('[');
            out.push_str(&r[..close]);
            out.push(']');
            rest = &r[close + 1..];
        } else if let Some(r) = rest.strip_prefix('_') {
            let n = r.len() - r.trim_start_matches(|c: char| c.is_ascii_digit()).len();
            if n == 0 || !r[n..].starts_with('_') {
                return None;
            }
            out.push('[');
            out.push_str(&r[..n]);
            out.push(']');
            rest = &r[n + 1..];
        } else {
            return None;
        }
    }
    Some(out)
}

/// A BDD variable: one endpoint bit, with its place in a bus.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarInfo {
    /// Display name, e.g. `state[3]`.
    pub name: String,
    /// Bus the bit belongs to (`state`), or the whole name for a scalar.
    pub base: String,
    pub index: Option<i64>,
    /// Bits with the same `bus` id belong to the same bus.
    pub bus: u32,
}

/// Buses up to this width are ordered before scalars: they are the likely
/// selects, indexes and state registers.
const NARROW: usize = 12;

/// Choose a BDD variable order for the endpoints called `names`.
///
/// Returns the variables in level order, and for each level the index into
/// `names` it came from. The order is a heuristic that keeps the common
/// structures small:
///   * narrow buses first (selects before the data they select),
///   * buses of equal width interleaved bit by bit, MSB first (operands of
///     comparators and adders),
///   * then scalars, then wide buses.
pub fn order_vars(names: &[String]) -> (Vec<VarInfo>, Vec<usize>) {
    use std::collections::BTreeMap;
    // base -> [(index, position in names)]
    let mut buses: BTreeMap<String, Vec<(i64, usize)>> = BTreeMap::new();
    let mut scalars: Vec<(String, usize)> = Vec::new();
    for (i, n) in names.iter().enumerate() {
        match split_index(n) {
            (base, Some(idx)) => buses.entry(base).or_default().push((idx, i)),
            (base, None) => scalars.push((base, i)),
        }
    }
    // A bus with a single bit in the cone behaves like a scalar.
    let mut by_width: BTreeMap<usize, Vec<(String, Vec<(i64, usize)>)>> = BTreeMap::new();
    for (base, bits) in buses {
        if bits.len() == 1 {
            scalars.push((names[bits[0].1].clone(), bits[0].1));
        } else {
            by_width.entry(bits.len()).or_default().push((base, bits));
        }
    }
    scalars.sort();

    let mut order: Vec<usize> = Vec::with_capacity(names.len());
    let mut bus_of: Vec<u32> = vec![0; names.len()];
    let mut next_bus = 0u32;
    let mut emit_width = |group: &[(String, Vec<(i64, usize)>)], order: &mut Vec<usize>| {
        // (index descending, bus rank) interleaves equal-width buses MSB first.
        let mut all: Vec<(i64, usize, usize)> = Vec::new();
        for (rank, (_, bits)) in group.iter().enumerate() {
            for &(idx, pos) in bits {
                bus_of[pos] = next_bus + rank as u32;
                all.push((-idx, rank, pos));
            }
        }
        next_bus += group.len() as u32;
        all.sort();
        order.extend(all.into_iter().map(|(_, _, pos)| pos));
    };
    for (_, group) in by_width.range(..=NARROW) {
        emit_width(group, &mut order);
    }
    let scalar_start = order.len();
    order.extend(scalars.iter().map(|(_, pos)| *pos));
    for (_, group) in by_width.range(NARROW + 1..) {
        emit_width(group, &mut order);
    }
    for &pos in &order[scalar_start..scalar_start + scalars.len()] {
        bus_of[pos] = next_bus;
        next_bus += 1;
    }

    let vars = order
        .iter()
        .map(|&pos| {
            let (base, index) = split_index(&names[pos]);
            VarInfo {
                name: names[pos].clone(),
                base,
                index,
                bus: bus_of[pos],
            }
        })
        .collect();
    (vars, order)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn split(n: &str) -> (String, Option<i64>) {
        split_index(n)
    }

    #[test]
    fn bracket_index() {
        assert_eq!(split("cnt[3]"), ("cnt".into(), Some(3)));
        assert_eq!(split("/u_a/cnt[12]"), ("/u_a/cnt".into(), Some(12)));
        assert_eq!(split("mem[3][2]"), ("mem[3]".into(), Some(2)));
    }

    #[test]
    fn underscore_index() {
        assert_eq!(split("cnt_3_"), ("cnt".into(), Some(3)));
        assert_eq!(split("mem_3__2_"), ("mem_3_".into(), Some(2)));
    }

    #[test]
    fn scalars_have_no_index() {
        assert_eq!(split("n12"), ("n12".into(), None));
        assert_eq!(split("valid"), ("valid".into(), None));
        assert_eq!(split("a_"), ("a_".into(), None));
        assert_eq!(split("_3_"), ("_3_".into(), None));
        assert_eq!(split("x[a]"), ("x[a]".into(), None));
        assert_eq!(split("[3]"), ("[3]".into(), None));
    }

    #[test]
    fn register_instance_names() {
        assert_eq!(reg_signal_name("cnt_reg[3]").as_deref(), Some("cnt[3]"));
        assert_eq!(reg_signal_name("cnt_reg_3_").as_deref(), Some("cnt[3]"));
        assert_eq!(reg_signal_name("cnt_reg").as_deref(), Some("cnt"));
        assert_eq!(reg_signal_name("mem_reg[3][2]").as_deref(), Some("mem[3][2]"));
        assert_eq!(reg_signal_name("mem_reg_3__2_").as_deref(), Some("mem[3][2]"));
        assert_eq!(reg_signal_name("u_a/u_b/st_reg[0]").as_deref(), Some("u_a/u_b/st[0]"));
    }

    #[test]
    fn names_that_are_not_register_style() {
        assert_eq!(reg_signal_name("U123"), None);
        assert_eq!(reg_signal_name("cnt_regs"), None);
        assert_eq!(reg_signal_name("_reg"), None);
        assert_eq!(reg_signal_name("cnt_reg_3"), None);
        assert_eq!(reg_signal_name("cnt_reg[x]"), None);
    }

    fn ordered(names: &[&str]) -> Vec<String> {
        let names: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        let (vars, order) = order_vars(&names);
        assert_eq!(vars.len(), names.len());
        for (v, &pos) in vars.iter().zip(&order) {
            assert_eq!(v.name, names[pos]);
        }
        vars.into_iter().map(|v| v.name).collect()
    }

    #[test]
    fn narrow_buses_then_scalars_then_wide_buses() {
        let mut names = vec!["en".to_string()];
        names.extend((0..16).map(|i| format!("bitmap[{i}]")));
        names.extend((0..4).map(|i| format!("idx[{i}]")));
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let got = ordered(&refs);
        assert_eq!(&got[..4], ["idx[3]", "idx[2]", "idx[1]", "idx[0]"]);
        assert_eq!(got[4], "en");
        assert_eq!(got[5], "bitmap[15]");
        assert_eq!(got[20], "bitmap[0]");
    }

    #[test]
    fn equal_width_buses_interleave_msb_first() {
        let got = ordered(&["a[0]", "b[1]", "a[2]", "b[0]", "a[1]", "b[2]"]);
        assert_eq!(got, ["a[2]", "b[2]", "a[1]", "b[1]", "a[0]", "b[0]"]);
    }

    #[test]
    fn narrower_bus_comes_first() {
        let got = ordered(&["d[0]", "d[1]", "d[2]", "s[0]", "s[1]"]);
        assert_eq!(got, ["s[1]", "s[0]", "d[2]", "d[1]", "d[0]"]);
    }

    #[test]
    fn a_lone_bus_bit_is_treated_as_a_scalar() {
        let got = ordered(&["x[5]", "c[1]", "c[0]", "sel"]);
        assert_eq!(got, ["c[1]", "c[0]", "sel", "x[5]"]);
    }

    #[test]
    fn bus_ids_group_bits_of_one_bus() {
        let names: Vec<String> = ["a[1]", "a[0]", "b[1]", "b[0]", "s", "/u/a[1]", "/u/a[0]"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let (vars, _) = order_vars(&names);
        let bus = |n: &str| vars.iter().find(|v| v.name == n).unwrap().bus;
        assert_eq!(bus("a[1]"), bus("a[0]"));
        assert_ne!(bus("a[1]"), bus("b[1]"));
        assert_ne!(bus("a[1]"), bus("/u/a[1]"));
        assert_ne!(bus("s"), bus("a[0]"));
        let a1 = vars.iter().find(|v| v.name == "a[1]").unwrap();
        assert_eq!((a1.base.as_str(), a1.index), ("a", Some(1)));
    }
}

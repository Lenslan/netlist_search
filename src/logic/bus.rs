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
}

//! The expressions the report prints, with rendering and a BDD evaluator used
//! for the self-check: every rendered expression is converted back to a BDD and
//! compared with the function of the wire it came from.

use std::rc::Rc;

use super::bdd::{BResult, Bd, Bdd, Blowup, FALSE, TRUE};
use super::bus::VarInfo;
use super::words;
use super::words::VResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Radix {
    Dec,
    Hex,
    Bin,
}

impl Radix {
    pub fn parse(s: &str) -> Option<Radix> {
        Some(match s {
            "dec" | "d" | "decimal" => Radix::Dec,
            "hex" | "h" | "hexadecimal" => Radix::Hex,
            "bin" | "b" | "binary" => Radix::Bin,
            _ => return None,
        })
    }
}

/// One bit of a word: an endpoint bit or a constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitSrc {
    Var(u32),
    Const(bool),
}

/// A little-endian bit vector (`bits[0]` is the LSB).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Word {
    pub bits: Vec<BitSrc>,
    pub signed: bool,
}

impl Word {
    pub fn width(&self) -> usize {
        self.bits.len()
    }

    /// A word from variable levels, least significant first.
    pub fn vars(vars: &[u32], signed: bool) -> Word {
        Word {
            bits: vars.iter().map(|&v| BitSrc::Var(v)).collect(),
            signed,
        }
    }

    /// A word holding one value.
    pub fn constant(value: u128, width: usize) -> Word {
        Word {
            bits: (0..width)
                .map(|i| BitSrc::Const(value >> i & 1 == 1))
                .collect(),
            signed: false,
        }
    }

    fn bdds(&self, b: &mut Bdd) -> VResult {
        let mut out = Vec::with_capacity(self.bits.len());
        for bit in &self.bits {
            out.push(match *bit {
                BitSrc::Var(v) => b.var(v)?,
                BitSrc::Const(true) => TRUE,
                BitSrc::Const(false) => FALSE,
            });
        }
        Ok(out)
    }

    fn value(&self) -> Option<u128> {
        let mut v = 0u128;
        for (i, bit) in self.bits.iter().enumerate() {
            match bit {
                BitSrc::Const(true) => v |= 1 << i,
                BitSrc::Const(false) => {}
                BitSrc::Var(_) => return None,
            }
        }
        Some(v)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CmpOp {
    pub fn text(self) -> &'static str {
        match self {
            CmpOp::Eq => "==",
            CmpOp::Ne => "!=",
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arith {
    Add,
    Sub,
    Mul,
}

impl Arith {
    fn text(self) -> &'static str {
        match self {
            Arith::Add => "+",
            Arith::Sub => "-",
            Arith::Mul => "*",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelKind {
    /// `data[sel]`, zero outside the data.
    Index,
    Shr,
    Ashr,
    Shl,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Const(bool),
    Var(u32),
    Not(Rc<Expr>),
    And(Vec<Rc<Expr>>),
    Or(Vec<Rc<Expr>>),
    Xor(Vec<Rc<Expr>>),
    /// `sel ? t : e`
    Mux(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Cmp {
        op: CmpOp,
        a: Word,
        b: Word,
    },
    /// `a inside {vals}`
    Inside {
        a: Word,
        vals: Vec<u128>,
    },
    /// Bit `bit` of `a op b (+ cin)`.
    ArithBit {
        op: Arith,
        a: Word,
        b: Word,
        cin: Option<u32>,
        bit: u32,
    },
    /// `items[sel]`: a multiplexer with one entry per value of `sel`.
    Case {
        sel: Word,
        items: Vec<Rc<Expr>>,
    },
    /// Bit `off` of `data >> sel` / `data << sel`; `Index` is `data[sel]`.
    Select {
        kind: SelKind,
        data: Word,
        sel: Word,
        off: u32,
    },
}

impl Expr {
    pub fn atom(e: Expr) -> Rc<Expr> {
        Rc::new(e)
    }

    /// Rough size in atoms and operators; used to pick the most readable form.
    pub fn size(&self) -> usize {
        match self {
            Expr::Const(_) | Expr::Var(_) => 1,
            Expr::Not(x) => 1 + x.size(),
            Expr::And(xs) | Expr::Or(xs) | Expr::Xor(xs) => {
                1 + xs.iter().map(|x| x.size()).sum::<usize>()
            }
            Expr::Mux(c, t, e) => 1 + c.size() + t.size() + e.size(),
            Expr::Cmp { .. } => 3,
            Expr::Inside { vals, .. } => 1 + vals.len(),
            Expr::ArithBit { .. } => 3,
            Expr::Select { .. } => 3,
            Expr::Case { items, .. } => 1 + items.iter().map(|x| x.size()).sum::<usize>(),
        }
    }

    pub fn to_bdd(&self, b: &mut Bdd) -> BResult {
        match self {
            Expr::Const(v) => Ok(b.constant(*v)),
            Expr::Var(v) => b.var(*v),
            Expr::Not(x) => {
                let f = x.to_bdd(b)?;
                b.not(f)
            }
            Expr::And(xs) => {
                let mut f = TRUE;
                for x in xs {
                    let g = x.to_bdd(b)?;
                    f = b.and(f, g)?;
                }
                Ok(f)
            }
            Expr::Or(xs) => {
                let mut f = FALSE;
                for x in xs {
                    let g = x.to_bdd(b)?;
                    f = b.or(f, g)?;
                }
                Ok(f)
            }
            Expr::Xor(xs) => {
                let mut f = FALSE;
                for x in xs {
                    let g = x.to_bdd(b)?;
                    f = b.xor(f, g)?;
                }
                Ok(f)
            }
            Expr::Mux(c, t, e) => {
                let c = c.to_bdd(b)?;
                let t = t.to_bdd(b)?;
                let e = e.to_bdd(b)?;
                b.ite(c, t, e)
            }
            Expr::Cmp { op, a, b: rhs } => {
                let signed = a.signed || rhs.signed;
                let w = a.width().max(rhs.width());
                let x = words::extend(&a.bdds(b)?, w, signed);
                let y = words::extend(&rhs.bdds(b)?, w, signed);
                match op {
                    CmpOp::Eq => words::eq(b, &x, &y),
                    CmpOp::Ne => {
                        let e = words::eq(b, &x, &y)?;
                        b.not(e)
                    }
                    CmpOp::Lt => {
                        if signed {
                            words::slt(b, &x, &y)
                        } else {
                            words::ult(b, &x, &y)
                        }
                    }
                    CmpOp::Gt => {
                        if signed {
                            words::slt(b, &y, &x)
                        } else {
                            words::ult(b, &y, &x)
                        }
                    }
                    CmpOp::Le => {
                        let l = if signed {
                            words::slt(b, &y, &x)?
                        } else {
                            words::ult(b, &y, &x)?
                        };
                        b.not(l)
                    }
                    CmpOp::Ge => {
                        let l = if signed {
                            words::slt(b, &x, &y)?
                        } else {
                            words::ult(b, &x, &y)?
                        };
                        b.not(l)
                    }
                }
            }
            Expr::Inside { a, vals } => {
                let w = a.width();
                let x = a.bdds(b)?;
                let mut f = FALSE;
                for &v in vals {
                    let c = Word::constant(v, w);
                    let y = words::extend(&c.bdds(b)?, w, false);
                    let e = words::eq(b, &x, &y)?;
                    f = b.or(f, e)?;
                }
                Ok(f)
            }
            Expr::ArithBit {
                op,
                a,
                b: rhs,
                cin,
                bit,
            } => {
                let target = *bit as usize;
                let w = a.width().max(rhs.width()).max(target + 1);
                let x = words::extend(&a.bdds(b)?, w, a.signed);
                let y = words::extend(&rhs.bdds(b)?, w, rhs.signed);
                let cin = match cin {
                    Some(v) => b.var(*v)?,
                    None => FALSE,
                };
                let vec = match op {
                    Arith::Add => words::add(b, &x, &y, cin),
                    Arith::Sub => words::sub(b, &x, &y),
                    Arith::Mul => {
                        b.set_budget(200_000);
                        let r = words::mul(b, &x, &y);
                        b.clear_budget();
                        r
                    }
                };
                let vec = match vec {
                    Ok(v) => v,
                    Err(Blowup) => return Err(Blowup),
                };
                Ok(vec.get(target).copied().unwrap_or(FALSE))
            }
            Expr::Case { sel, items } => {
                let s = sel.bdds(b)?;
                let mut table = Vec::with_capacity(items.len());
                for it in items {
                    table.push(it.to_bdd(b)?);
                }
                words::dynamic_select(b, &table, &s, FALSE)
            }
            Expr::Select {
                kind,
                data,
                sel,
                off,
            } => {
                let d = data.bdds(b)?;
                let s = sel.bdds(b)?;
                let k = *off as usize;
                match kind {
                    SelKind::Index => {
                        let table = d.get(k..).unwrap_or(&[]);
                        words::dynamic_select(b, table, &s, FALSE)
                    }
                    SelKind::Shr => {
                        let table = d.get(k..).unwrap_or(&[]);
                        words::dynamic_select(b, table, &s, FALSE)
                    }
                    SelKind::Ashr => {
                        let table = d.get(k..).unwrap_or(&[]);
                        let sign = d.last().copied().unwrap_or(FALSE);
                        words::dynamic_select(b, table, &s, sign)
                    }
                    SelKind::Shl => words::shl_bit(b, &d, &s, k),
                }
            }
        }
    }

    // ---- rendering ---------------------------------------------------------

    pub fn render(&self, vars: &[VarInfo], radix: Radix) -> String {
        self.render_prec(vars, radix, 0)
    }

    fn render_prec(&self, vars: &[VarInfo], radix: Radix, min: u8) -> String {
        let joins = |xs: &[Rc<Expr>], sep: &str, p: u8| {
            xs.iter()
                .map(|x| x.render_prec(vars, radix, p))
                .collect::<Vec<_>>()
                .join(sep)
        };
        let (body, p) = match self {
            Expr::Const(true) => ("1'b1".to_string(), PREC_ATOM),
            Expr::Const(false) => ("1'b0".to_string(), PREC_ATOM),
            Expr::Var(v) => (vars[*v as usize].name.clone(), PREC_ATOM),
            Expr::Not(x) => (
                match &**x {
                    Expr::Var(v) => format!("!{}", vars[*v as usize].name),
                    _ => format!("!{}", x.render_prec(vars, radix, PREC_ATOM)),
                },
                PREC_ATOM,
            ),
            Expr::And(xs) => (joins(xs, " & ", PREC_AND), PREC_AND),
            Expr::Or(xs) => (joins(xs, " | ", PREC_OR), PREC_OR),
            Expr::Xor(xs) => (joins(xs, " ^ ", PREC_XOR), PREC_XOR),
            Expr::Mux(c, t, e) => (
                format!(
                    "{} ? {} : {}",
                    c.render_prec(vars, radix, PREC_MUX + 1),
                    t.render_prec(vars, radix, PREC_MUX + 1),
                    e.render_prec(vars, radix, PREC_MUX + 1)
                ),
                PREC_MUX,
            ),
            Expr::Cmp { op, a, b } => (
                format!(
                    "{} {} {}",
                    word_text(a, vars, radix),
                    op.text(),
                    word_text(b, vars, radix)
                ),
                PREC_CMP,
            ),
            Expr::Inside { a, vals } => {
                let list: Vec<String> = vals
                    .iter()
                    .map(|&v| number(v, a.width(), radix))
                    .collect();
                (
                    format!("{} inside {{{}}}", word_text(a, vars, radix), list.join(", ")),
                    PREC_MUX,
                )
            }
            Expr::ArithBit {
                op,
                a,
                b,
                cin,
                bit,
            } => {
                let mut s = format!("{} {} {}", word_text(a, vars, radix), op.text(), word_text(b, vars, radix));
                if let Some(c) = cin {
                    s.push_str(&format!(" + {}", vars[*c as usize].name));
                }
                (format!("({s})[{bit}]"), PREC_ATOM)
            }
            Expr::Case { sel, items } => {
                let arms: Vec<String> = items
                    .iter()
                    .enumerate()
                    .map(|(i, it)| format!("{i}: {}", it.render_prec(vars, radix, 0)))
                    .collect();
                (
                    format!("case ({}) {{{}}}", word_text(sel, vars, radix), arms.join(", ")),
                    PREC_ATOM,
                )
            }
            Expr::Select {
                kind,
                data,
                sel,
                off,
            } => {
                let d = word_text(data, vars, radix);
                let s = word_text(sel, vars, radix);
                // Bit `lo` of `bus[hi:0] >> s` is `bus[lo + s]`: show a slice that
                // starts above bit 0 as the shift of the whole bus.
                let slice = as_slice(data, vars);
                let text = match (kind, &slice) {
                    (SelKind::Index, Some((base, 0, _))) if *off == 0 => format!("{base}[{s}]"),
                    (SelKind::Index | SelKind::Shr, Some((base, lo, hi))) => {
                        format!("({base}[{hi}:0] >> {s})[{}]", lo + *off as i64)
                    }
                    (SelKind::Ashr, Some((base, lo, hi))) => {
                        format!("($signed({base}[{hi}:0]) >>> {s})[{}]", lo + *off as i64)
                    }
                    (SelKind::Index | SelKind::Shr, None) => format!("({d} >> {s})[{off}]"),
                    (SelKind::Ashr, None) => format!("($signed({d}) >>> {s})[{off}]"),
                    (SelKind::Shl, _) => format!("({d} << {s})[{off}]"),
                };
                (text, PREC_ATOM)
            }
        };
        if p < min {
            format!("({body})")
        } else {
            body
        }
    }
}

// Verilog precedence, loosest first. `inside` is given the loosest level so
// that it is always parenthesised inside another operator.
const PREC_MUX: u8 = 0;
const PREC_OR: u8 = 1;
const PREC_XOR: u8 = 2;
const PREC_AND: u8 = 3;
const PREC_CMP: u8 = 4;
const PREC_ATOM: u8 = 5;

/// A number as a literal: plain decimal, or sized in hex/binary.
pub fn number(value: u128, width: usize, radix: Radix) -> String {
    match radix {
        Radix::Dec => format!("{value}"),
        Radix::Hex => format!("{width}'h{value:x}"),
        Radix::Bin => format!("{width}'b{value:0width$b}", width = width.max(1)),
    }
}

/// If the word is a contiguous slice of one bus, `(base, lo, hi)`.
pub fn as_slice(w: &Word, vars: &[VarInfo]) -> Option<(String, i64, i64)> {
    if w.bits.is_empty() {
        return None;
    }
    let mut bus = 0;
    let mut idxs = Vec::with_capacity(w.bits.len());
    for (i, bit) in w.bits.iter().enumerate() {
        let BitSrc::Var(v) = *bit else { return None };
        let vi = &vars[v as usize];
        if i == 0 {
            bus = vi.bus;
        } else if vi.bus != bus {
            return None;
        }
        idxs.push(vi.index?);
    }
    if idxs.iter().enumerate().any(|(i, &x)| x != idxs[0] + i as i64) {
        return None;
    }
    let BitSrc::Var(v0) = w.bits[0] else { unreachable!() };
    let base = vars[v0 as usize].base.clone();
    Some((base, idxs[0], idxs[idxs.len() - 1]))
}

/// Like `number`, always with an explicit width (used inside concatenations).
pub fn sized_number(value: u128, width: usize, radix: Radix) -> String {
    match radix {
        Radix::Dec => format!("{width}'d{value}"),
        Radix::Hex => format!("{width}'h{value:x}"),
        Radix::Bin => format!("{width}'b{value:0width$b}", width = width.max(1)),
    }
}

/// Render a word: a bus slice, a constant, or a concatenation.
pub fn word_text(w: &Word, vars: &[VarInfo], radix: Radix) -> String {
    if let Some(v) = w.value() {
        return number(v, w.width(), radix);
    }
    let body = match as_slice(w, vars) {
        Some(_) if w.bits.len() == 1 => match w.bits[0] {
            BitSrc::Var(v) => vars[v as usize].name.clone(),
            BitSrc::Const(_) => unreachable!(),
        },
        Some((base, lo, hi)) => format!("{base}[{hi}:{lo}]"),
        None => {
        // Concatenation, MSB first, grouping runs of constant bits.
        let mut parts: Vec<String> = Vec::new();
        let mut i = w.bits.len();
        while i > 0 {
            match w.bits[i - 1] {
                BitSrc::Const(_) => {
                    let mut bits: Vec<bool> = Vec::new();
                    while i > 0 {
                        match w.bits[i - 1] {
                            BitSrc::Const(c) => {
                                bits.push(c);
                                i -= 1;
                            }
                            BitSrc::Var(_) => break,
                        }
                    }
                    let value: u128 = bits
                        .iter()
                        .fold(0u128, |acc, &b| acc << 1 | u128::from(b));
                    parts.push(sized_number(value, bits.len(), radix));
                }
                BitSrc::Var(_) => {
                    // Longest run of bits of one bus with consecutive indices.
                    let start = i;
                    let mut end = i;
                    let bus = match w.bits[i - 1] {
                        BitSrc::Var(v) => vars[v as usize].bus,
                        _ => unreachable!(),
                    };
                    let mut hi = match w.bits[i - 1] {
                        BitSrc::Var(v) => vars[v as usize].index.unwrap_or(0),
                        _ => unreachable!(),
                    };
                    while end > 0 {
                        match w.bits[end - 1] {
                            BitSrc::Var(v)
                                if vars[v as usize].bus == bus
                                    && vars[v as usize].index == Some(hi) =>
                            {
                                end -= 1;
                                hi -= 1;
                            }
                            _ => break,
                        }
                    }
                    if start == end {
                        parts.push(match w.bits[i - 1] {
                            BitSrc::Var(v) => vars[v as usize].name.clone(),
                            _ => unreachable!(),
                        });
                        i -= 1;
                    } else {
                        let (base, lo) = match w.bits[end] {
                            BitSrc::Var(v) => (
                                vars[v as usize].base.clone(),
                                vars[v as usize].index.unwrap_or(0),
                            ),
                            _ => unreachable!(),
                        };
                        let hi = lo + (start - end) as i64 - 1;
                        parts.push(if start - end == 1 {
                            vars[match w.bits[end] {
                                BitSrc::Var(v) => v as usize,
                                _ => unreachable!(),
                            }]
                            .name
                            .clone()
                        } else {
                            format!("{base}[{hi}:{lo}]")
                        });
                        i = end;
                    }
                }
            }
        }
        format!("{{{}}}", parts.join(", "))
        }
    };
    if w.signed {
        format!("$signed({body})")
    } else {
        body
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vars(names: &[&str]) -> Vec<VarInfo> {
        let names: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        super::super::bus::order_vars(&names).0
    }

    /// Variable levels for the bus vars of `v`, level = position in the input.
    fn levels(v: &[VarInfo]) -> Vec<u32> {
        (0..v.len() as u32).collect()
    }

    fn level_of(v: &[VarInfo], name: &str) -> u32 {
        v.iter().position(|x| x.name == name).unwrap() as u32
    }

    /// Little-endian word of the given variable names.
    fn word(v: &[VarInfo], names: &[&str]) -> Word {
        Word::vars(
            &names.iter().map(|n| level_of(v, n)).collect::<Vec<_>>(),
            false,
        )
    }

    fn bus_word(v: &[VarInfo], base: &str, width: usize) -> Word {
        let names: Vec<String> = (0..width).map(|i| format!("{base}[{i}]")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        word(v, &refs)
    }

    #[test]
    fn equality_with_a_constant() {
        let v = vars(&["state[0]", "state[1]", "state[2]", "state[3]"]);
        let w = bus_word(&v, "state", 4);
        let e = Expr::Cmp {
            op: CmpOp::Eq,
            a: w,
            b: Word::constant(5, 4),
        };
        assert_eq!(e.render(&v, Radix::Dec), "state[3:0] == 5");
        assert_eq!(e.render(&v, Radix::Bin), "state[3:0] == 4'b0101");
        assert_eq!(e.render(&v, Radix::Hex), "state[3:0] == 4'h5");
    }

    #[test]
    fn ternary_mux() {
        let v = vars(&["sel", "a", "b"]);
        let e = Expr::Mux(
            Expr::atom(Expr::Var(level_of(&v, "sel"))),
            Expr::atom(Expr::Var(level_of(&v, "a"))),
            Expr::atom(Expr::Var(level_of(&v, "b"))),
        );
        assert_eq!(e.render(&v, Radix::Dec), "sel ? a : b");
    }

    #[test]
    fn nested_mux_and_boolean_operators_get_parentheses() {
        let v = vars(&["rst", "en", "x", "y", "a", "b", "c"]);
        let var = |n: &str| Expr::atom(Expr::Var(level_of(&v, n)));
        let inner = Expr::Mux(var("en"), var("x"), var("y"));
        let outer = Expr::Mux(var("rst"), Expr::atom(Expr::Const(false)), Expr::atom(inner));
        assert_eq!(outer.render(&v, Radix::Dec), "rst ? 1'b0 : (en ? x : y)");
        let and = Expr::And(vec![
            Expr::atom(Expr::Or(vec![var("a"), var("b")])),
            Expr::atom(Expr::Not(var("c"))),
        ]);
        assert_eq!(and.render(&v, Radix::Dec), "(a | b) & !c");
    }

    #[test]
    fn concatenation_of_scattered_bits() {
        let v = vars(&["x[0]", "x[2]", "x[3]"]);
        let w = Word {
            bits: vec![
                BitSrc::Var(level_of(&v, "x[0]")),
                BitSrc::Const(false),
                BitSrc::Var(level_of(&v, "x[2]")),
                BitSrc::Var(level_of(&v, "x[3]")),
            ],
            signed: false,
        };
        assert_eq!(word_text(&w, &v, Radix::Bin), "{x[3:2], 1'b0, x[0]}");
        assert_eq!(word_text(&w, &v, Radix::Hex), "{x[3:2], 1'h0, x[0]}");
    }

    #[test]
    fn set_membership() {
        let v = vars(&["state[0]", "state[1]", "state[2]", "state[3]"]);
        let e = Expr::Inside {
            a: bus_word(&v, "state", 4),
            vals: vec![5, 9],
        };
        assert_eq!(e.render(&v, Radix::Dec), "state[3:0] inside {5, 9}");
    }

    #[test]
    fn arithmetic_bits() {
        let v = vars(&["cnt[0]", "cnt[1]", "cnt[2]", "cnt[3]", "a[0]", "a[1]", "b[0]", "b[1]", "c"]);
        let cnt = bus_word(&v, "cnt", 4);
        let e = Expr::ArithBit {
            op: Arith::Add,
            a: cnt.clone(),
            b: Word::constant(1, 1),
            cin: None,
            bit: 3,
        };
        assert_eq!(e.render(&v, Radix::Dec), "(cnt[3:0] + 1)[3]");
        let e = Expr::ArithBit {
            op: Arith::Sub,
            a: cnt.clone(),
            b: Word::constant(1, 1),
            cin: None,
            bit: 2,
        };
        assert_eq!(e.render(&v, Radix::Dec), "(cnt[3:0] - 1)[2]");
        let a = bus_word(&v, "a", 2);
        let b = bus_word(&v, "b", 2);
        let e = Expr::ArithBit {
            op: Arith::Mul,
            a: a.clone(),
            b: b.clone(),
            cin: None,
            bit: 2,
        };
        assert_eq!(e.render(&v, Radix::Dec), "(a[1:0] * b[1:0])[2]");
        let e = Expr::ArithBit {
            op: Arith::Add,
            a: a.clone(),
            b: b.clone(),
            cin: Some(level_of(&v, "c")),
            bit: 2,
        };
        assert_eq!(e.render(&v, Radix::Dec), "(a[1:0] + b[1:0] + c)[2]");
    }

    #[test]
    fn index_and_shift_forms() {
        let mut names: Vec<String> = (0..8).map(|i| format!("bitmap[{i}]")).collect();
        names.push("idx[0]".into());
        names.push("idx[1]".into());
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let v = vars(&refs);
        let data = bus_word(&v, "bitmap", 8);
        let sel = bus_word(&v, "idx", 2);
        let e = Expr::Select {
            kind: SelKind::Index,
            data,
            sel: sel.clone(),
            off: 0,
        };
        assert_eq!(e.render(&v, Radix::Dec), "bitmap[idx[1:0]]");
        let data = bus_word(&v, "bitmap", 8);
        let e = Expr::Select {
            kind: SelKind::Shr,
            data,
            sel: sel.clone(),
            off: 2,
        };
        assert_eq!(e.render(&v, Radix::Dec), "(bitmap[7:0] >> idx[1:0])[2]");
        let e = Expr::Select {
            kind: SelKind::Ashr,
            data: bus_word(&v, "bitmap", 8),
            sel,
            off: 1,
        };
        assert_eq!(
            e.render(&v, Radix::Dec),
            "($signed(bitmap[7:0]) >>> idx[1:0])[1]"
        );
    }

    #[test]
    fn signed_comparison_shows_signedness() {
        let v = vars(&["a[0]", "a[1]", "a[2]", "a[3]", "b[0]", "b[1]", "b[2]", "b[3]"]);
        let mut a = bus_word(&v, "a", 4);
        a.signed = true;
        let e = Expr::Cmp {
            op: CmpOp::Lt,
            a,
            b: bus_word(&v, "b", 4),
        };
        assert_eq!(e.render(&v, Radix::Dec), "$signed(a[3:0]) < b[3:0]");
    }

    #[test]
    fn comparison_is_smaller_than_its_sop() {
        let v = vars(&["state[0]", "state[1]", "state[2]", "state[3]"]);
        let mut sop: Vec<Rc<Expr>> = Vec::new();
        for (i, name) in ["state[0]", "state[2]"].iter().enumerate() {
            let _ = i;
            sop.push(Expr::atom(Expr::Var(level_of(&v, name))));
        }
        for name in ["state[1]", "state[3]"] {
            sop.push(Expr::atom(Expr::Not(Expr::atom(Expr::Var(level_of(&v, name))))));
        }
        let cmp = Expr::Cmp {
            op: CmpOp::Eq,
            a: bus_word(&v, "state", 4),
            b: Word::constant(5, 4),
        };
        assert!(cmp.size() < Expr::And(sop).size());
    }

    #[test]
    fn to_bdd_matches_hand_built_functions() {
        let names: Vec<String> = ["a[0]", "a[1]", "b[0]", "b[1]", "s"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let v = super::super::bus::order_vars(&names).0;
        let mut b = Bdd::new(1 << 16);
        for _ in 0..v.len() {
            b.new_var();
        }
        let a = bus_word(&v, "a", 2);
        let bwd = bus_word(&v, "b", 2);
        let eq = Expr::Cmp {
            op: CmpOp::Eq,
            a: a.clone(),
            b: bwd.clone(),
        };
        let got = eq.to_bdd(&mut b).unwrap();
        // Manual: (a0 == b0) & (a1 == b1)
        let lvl = levels(&v);
        let av: Vec<Bd> = (0..2).map(|i| b.var(lvl[level_of(&v, &format!("a[{i}]")) as usize]).unwrap()).collect();
        let bv: Vec<Bd> = (0..2).map(|i| b.var(lvl[level_of(&v, &format!("b[{i}]")) as usize]).unwrap()).collect();
        let want = words::eq(&mut b, &av, &bv).unwrap();
        assert_eq!(got, want);

        let mux = Expr::Mux(
            Expr::atom(Expr::Var(level_of(&v, "s"))),
            Expr::atom(Expr::Var(level_of(&v, "a[1]"))),
            Expr::atom(Expr::Var(level_of(&v, "a[0]"))),
        );
        let got = mux.to_bdd(&mut b).unwrap();
        let s = b.var(level_of(&v, "s")).unwrap();
        let x = b.var(level_of(&v, "a[1]")).unwrap();
        let y = b.var(level_of(&v, "a[0]")).unwrap();
        assert_eq!(got, b.ite(s, x, y).unwrap());
    }

    #[test]
    fn arithmetic_bit_to_bdd_matches_the_adder() {
        let names: Vec<String> = ["a[0]", "a[1]", "b[0]", "b[1]"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let v = super::super::bus::order_vars(&names).0;
        let mut b = Bdd::new(1 << 16);
        for _ in 0..v.len() {
            b.new_var();
        }
        let a = bus_word(&v, "a", 2);
        let bwd = bus_word(&v, "b", 2);
        for bit in 0..3 {
            let e = Expr::ArithBit {
                op: Arith::Add,
                a: a.clone(),
                b: bwd.clone(),
                cin: None,
                bit,
            };
            let got = e.to_bdd(&mut b).unwrap();
            let av = [b.var(level_of(&v, "a[0]")).unwrap(), b.var(level_of(&v, "a[1]")).unwrap()];
            let bv = [b.var(level_of(&v, "b[0]")).unwrap(), b.var(level_of(&v, "b[1]")).unwrap()];
            let want = words::add(&mut b, &av, &bv, FALSE).unwrap()[bit as usize];
            assert_eq!(got, want, "bit {bit}");
        }
    }

    #[test]
    fn select_to_bdd_matches_dynamic_select() {
        let names: Vec<String> = ["d[0]", "d[1]", "d[2]", "i[0]", "i[1]"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let v = super::super::bus::order_vars(&names).0;
        let mut b = Bdd::new(1 << 16);
        for _ in 0..v.len() {
            b.new_var();
        }
        let d = bus_word(&v, "d", 3);
        let i = bus_word(&v, "i", 2);
        let e = Expr::Select {
            kind: SelKind::Index,
            data: d.clone(),
            sel: i.clone(),
            off: 0,
        };
        let got = e.to_bdd(&mut b).unwrap();
        let dv: Vec<Bd> = (0..3).map(|k| b.var(level_of(&v, &format!("d[{k}]"))).unwrap()).collect();
        let iv: Vec<Bd> = (0..2).map(|k| b.var(level_of(&v, &format!("i[{k}]"))).unwrap()).collect();
        let want = words::dynamic_select(&mut b, &dv, &iv, FALSE).unwrap();
        assert_eq!(got, want);
    }
}

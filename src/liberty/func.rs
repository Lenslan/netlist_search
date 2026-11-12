//! Parser for Liberty `function` / `next_state` boolean expressions.
//!
//! Operators, highest precedence first (Liberty convention):
//!   `!x`, `x'`          NOT (prefix or postfix)
//!   `x ^ y`             XOR
//!   `x & y`, `x * y`, `x y`   AND (juxtaposition is AND)
//!   `x | y`, `x + y`    OR
//! plus parentheses and the constants `0` and `1`.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    Const(bool),
    Var(String),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Xor(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    /// Append every variable name used by the expression (with duplicates removed).
    pub fn vars(&self, out: &mut Vec<String>) {
        match self {
            BoolExpr::Const(_) => {}
            BoolExpr::Var(v) => {
                if !out.iter().any(|o| o == v) {
                    out.push(v.clone());
                }
            }
            BoolExpr::Not(a) => a.vars(out),
            BoolExpr::And(xs) | BoolExpr::Or(xs) => xs.iter().for_each(|x| x.vars(out)),
            BoolExpr::Xor(a, b) => {
                a.vars(out);
                b.vars(out);
            }
        }
    }

    /// Evaluate with `f` supplying the value of each variable.
    pub fn eval(&self, f: &dyn Fn(&str) -> bool) -> bool {
        match self {
            BoolExpr::Const(c) => *c,
            BoolExpr::Var(v) => f(v),
            BoolExpr::Not(a) => !a.eval(f),
            BoolExpr::And(xs) => xs.iter().all(|x| x.eval(f)),
            BoolExpr::Or(xs) => xs.iter().any(|x| x.eval(f)),
            BoolExpr::Xor(a, b) => a.eval(f) ^ b.eval(f),
        }
    }

    /// Evaluate 64 input vectors at once; `f` supplies one word per variable.
    pub fn eval64(&self, f: &dyn Fn(&str) -> u64) -> u64 {
        match self {
            BoolExpr::Const(c) => {
                if *c {
                    !0
                } else {
                    0
                }
            }
            BoolExpr::Var(v) => f(v),
            BoolExpr::Not(a) => !a.eval64(f),
            BoolExpr::And(xs) => xs.iter().fold(!0, |acc, x| acc & x.eval64(f)),
            BoolExpr::Or(xs) => xs.iter().fold(0, |acc, x| acc | x.eval64(f)),
            BoolExpr::Xor(a, b) => a.eval64(f) ^ b.eval64(f),
        }
    }
}

/// Parse a Liberty boolean function string such as `"(A1 A2 + B1')"`.
pub fn parse_function(s: &str) -> Result<BoolExpr, String> {
    let s = s.trim().trim_matches('"').trim();
    let mut p = Parser {
        src: s.as_bytes(),
        pos: 0,
    };
    let e = p.or()?;
    p.skip_ws();
    if p.pos != p.src.len() {
        return Err(format!(
            "unexpected '{}' at column {} in function \"{}\"",
            p.src[p.pos] as char,
            p.pos + 1,
            s
        ));
    }
    Ok(e)
}

struct Parser<'a> {
    src: &'a [u8],
    pos: usize,
}

fn is_name_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, b'_' | b'[' | b']' | b'.' | b'$')
}

impl Parser<'_> {
    fn skip_ws(&mut self) {
        while self.pos < self.src.len() && self.src[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.src.get(self.pos).copied()
    }

    fn or(&mut self) -> Result<BoolExpr, String> {
        let mut terms = vec![self.and()?];
        while matches!(self.peek(), Some(b'|' | b'+')) {
            self.pos += 1;
            terms.push(self.and()?);
        }
        Ok(if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            BoolExpr::Or(terms)
        })
    }

    fn and(&mut self) -> Result<BoolExpr, String> {
        let mut terms = vec![self.xor()?];
        loop {
            match self.peek() {
                Some(b'&' | b'*') => {
                    self.pos += 1;
                    terms.push(self.xor()?);
                }
                // Juxtaposition: the start of another operand means AND.
                Some(c) if c == b'(' || c == b'!' || is_name_byte(c) => terms.push(self.xor()?),
                _ => break,
            }
        }
        Ok(if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            BoolExpr::And(terms)
        })
    }

    fn xor(&mut self) -> Result<BoolExpr, String> {
        let mut e = self.unary()?;
        while self.peek() == Some(b'^') {
            self.pos += 1;
            let r = self.unary()?;
            e = BoolExpr::Xor(Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn unary(&mut self) -> Result<BoolExpr, String> {
        if self.peek() == Some(b'!') {
            self.pos += 1;
            let e = self.unary()?;
            return Ok(negate(e));
        }
        let mut e = self.primary()?;
        while self.peek() == Some(b'\'') {
            self.pos += 1;
            e = negate(e);
        }
        Ok(e)
    }

    fn primary(&mut self) -> Result<BoolExpr, String> {
        match self.peek() {
            Some(b'(') => {
                self.pos += 1;
                let e = self.or()?;
                if self.peek() != Some(b')') {
                    return Err("missing ')' in function".into());
                }
                self.pos += 1;
                Ok(e)
            }
            Some(c) if is_name_byte(c) => {
                let start = self.pos;
                while self.pos < self.src.len() && is_name_byte(self.src[self.pos]) {
                    self.pos += 1;
                }
                let name = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
                Ok(match name {
                    "0" => BoolExpr::Const(false),
                    "1" => BoolExpr::Const(true),
                    _ => BoolExpr::Var(name.to_string()),
                })
            }
            Some(c) => Err(format!("unexpected '{}' in function", c as char)),
            None => Err("unexpected end of function".into()),
        }
    }
}

fn negate(e: BoolExpr) -> BoolExpr {
    match e {
        BoolExpr::Not(inner) => *inner,
        BoolExpr::Const(c) => BoolExpr::Const(!c),
        other => BoolExpr::Not(Box::new(other)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Truth table of `s` over `vars` (bit i of the row number is vars[i]).
    fn tt(s: &str, vars: &[&str]) -> Vec<bool> {
        let e = parse_function(s).unwrap_or_else(|m| panic!("parse {s:?}: {m}"));
        (0..1usize << vars.len())
            .map(|row| {
                e.eval(&|name| {
                    let i = vars
                        .iter()
                        .position(|v| *v == name)
                        .unwrap_or_else(|| panic!("unexpected var {name}"));
                    row >> i & 1 == 1
                })
            })
            .collect()
    }

    fn expect(vars: &[&str], f: impl Fn(&[bool]) -> bool) -> Vec<bool> {
        (0..1usize << vars.len())
            .map(|row| {
                let bits: Vec<bool> = (0..vars.len()).map(|i| row >> i & 1 == 1).collect();
                f(&bits)
            })
            .collect()
    }

    #[test]
    fn and_has_three_spellings() {
        let v = ["A", "B"];
        let want = expect(&v, |b| b[0] & b[1]);
        assert_eq!(tt("A&B", &v), want);
        assert_eq!(tt("A*B", &v), want);
        assert_eq!(tt("A B", &v), want);
    }

    #[test]
    fn or_has_two_spellings() {
        let v = ["A", "B"];
        let want = expect(&v, |b| b[0] | b[1]);
        assert_eq!(tt("A|B", &v), want);
        assert_eq!(tt("A+B", &v), want);
    }

    #[test]
    fn not_is_prefix_or_postfix() {
        let v = ["A", "B"];
        assert_eq!(tt("!A", &["A"]), expect(&["A"], |b| !b[0]));
        assert_eq!(tt("A'", &["A"]), expect(&["A"], |b| !b[0]));
        assert_eq!(tt("A''", &["A"]), expect(&["A"], |b| b[0]));
        assert_eq!(tt("(A B)'", &v), expect(&v, |b| !(b[0] & b[1])));
        assert_eq!(tt("!(A+B)", &v), expect(&v, |b| !(b[0] | b[1])));
    }

    #[test]
    fn and_binds_tighter_than_or() {
        let v = ["A", "B", "C"];
        assert_eq!(tt("A+B*C", &v), expect(&v, |b| b[0] | (b[1] & b[2])));
        assert_eq!(tt("A B + C", &v), expect(&v, |b| (b[0] & b[1]) | b[2]));
    }

    #[test]
    fn xor_binds_tighter_than_and() {
        let v = ["A", "B", "C"];
        assert_eq!(tt("!A^B&C", &v), expect(&v, |b| ((!b[0]) ^ b[1]) & b[2]));
        assert_eq!(tt("A^B+C", &v), expect(&v, |b| (b[0] ^ b[1]) | b[2]));
        assert_eq!(tt("A&B^C", &v), expect(&v, |b| b[0] & (b[1] ^ b[2])));
    }

    #[test]
    fn juxtaposition_with_postfix_not() {
        let v = ["A1", "A2", "B1"];
        assert_eq!(
            tt("A1 A2 + B1'", &v),
            expect(&v, |b| (b[0] & b[1]) | !b[2])
        );
        assert_eq!(
            tt("(A1 A2)' B1", &v),
            expect(&v, |b| !(b[0] & b[1]) & b[2])
        );
    }

    #[test]
    fn constants() {
        assert_eq!(parse_function("0").unwrap(), BoolExpr::Const(false));
        assert_eq!(parse_function("1").unwrap(), BoolExpr::Const(true));
        assert_eq!(tt("A+1", &["A"]), vec![true, true]);
    }

    #[test]
    fn names_may_contain_brackets_and_underscores() {
        let v = ["D[0]", "D[1]", "S_n"];
        assert_eq!(
            tt("D[0] & D[1] | S_n", &v),
            expect(&v, |b| (b[0] & b[1]) | b[2])
        );
    }

    #[test]
    fn surrounding_quotes_and_space_are_ignored() {
        assert_eq!(tt(" \"A&B\" ", &["A", "B"]), expect(&["A", "B"], |b| b[0] & b[1]));
    }

    #[test]
    fn vars_are_listed_once() {
        let mut out = Vec::new();
        parse_function("A&B | A&IQ").unwrap().vars(&mut out);
        assert_eq!(out, vec!["A", "B", "IQ"]);
    }

    #[test]
    fn malformed_input_is_an_error() {
        for bad in ["", "A &", "(A", "A ) B", "&A", "A ^"] {
            assert!(parse_function(bad).is_err(), "{bad:?} should fail");
        }
    }
}

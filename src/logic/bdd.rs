//! A small reduced ordered BDD package.
//!
//! Variables are identified by their level: variable 0 is tested first. A
//! function has exactly one node, so two functions are equal iff their ids are.
//! Every operation that can create nodes returns `Err(Blowup)` once the node
//! limit (or the per-operation budget) is hit; the manager stays usable.

use rustc_hash::{FxHashMap, FxHashSet};

pub type Bd = u32;
pub const FALSE: Bd = 0;
pub const TRUE: Bd = 1;

/// The BDD grew past its limit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Blowup;

pub type BResult = Result<Bd, Blowup>;

#[derive(Clone, Copy)]
struct BNode {
    var: u32,
    lo: Bd,
    hi: Bd,
}

const TERMINAL: u32 = u32::MAX;

const OP_AND: u8 = 0;
const OP_OR: u8 = 1;
const OP_XOR: u8 = 2;
const OP_NOT: u8 = 3;
const OP_R0: u8 = 4;
const OP_R1: u8 = 5;
const OP_ITE: u8 = 6;

pub struct Bdd {
    nodes: Vec<BNode>,
    unique: FxHashMap<(u32, Bd, Bd), Bd>,
    cache: FxHashMap<(u8, Bd, Bd, Bd), Bd>,
    nvars: u32,
    limit: usize,
    budget_end: usize,
}

impl Bdd {
    pub fn new(node_limit: usize) -> Self {
        let t = BNode {
            var: TERMINAL,
            lo: 0,
            hi: 0,
        };
        Bdd {
            nodes: vec![t, t],
            unique: FxHashMap::default(),
            cache: FxHashMap::default(),
            nvars: 0,
            limit: node_limit.max(2),
            budget_end: usize::MAX,
        }
    }

    /// Add a variable below all existing ones; returns its index.
    pub fn new_var(&mut self) -> u32 {
        self.nvars += 1;
        self.nvars - 1
    }

    pub fn num_vars(&self) -> u32 {
        self.nvars
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Allow at most `extra` new nodes until `clear_budget`.
    pub fn set_budget(&mut self, extra: usize) {
        self.budget_end = self.nodes.len().saturating_add(extra);
    }

    pub fn clear_budget(&mut self) {
        self.budget_end = usize::MAX;
    }

    fn mk(&mut self, var: u32, lo: Bd, hi: Bd) -> BResult {
        if lo == hi {
            return Ok(lo);
        }
        if let Some(&n) = self.unique.get(&(var, lo, hi)) {
            return Ok(n);
        }
        if self.nodes.len() >= self.limit.min(self.budget_end) {
            return Err(Blowup);
        }
        let id = self.nodes.len() as Bd;
        self.nodes.push(BNode { var, lo, hi });
        self.unique.insert((var, lo, hi), id);
        Ok(id)
    }

    /// The function "variable `v` is 1".
    pub fn var(&mut self, v: u32) -> BResult {
        debug_assert!(v < self.nvars);
        self.mk(v, FALSE, TRUE)
    }

    pub fn constant(&self, value: bool) -> Bd {
        if value { TRUE } else { FALSE }
    }

    /// Variable tested at the root, or `None` for a constant.
    pub fn top_var(&self, f: Bd) -> Option<u32> {
        let v = self.nodes[f as usize].var;
        (v != TERMINAL).then_some(v)
    }

    fn level(&self, f: Bd) -> u32 {
        self.nodes[f as usize].var
    }

    /// Cofactors of `f` for `v`, where `v` is at or above the root of `f`.
    fn split(&self, f: Bd, v: u32) -> (Bd, Bd) {
        let n = self.nodes[f as usize];
        if n.var == v { (n.lo, n.hi) } else { (f, f) }
    }

    fn cached(&mut self, key: (u8, Bd, Bd, Bd)) -> Option<Bd> {
        self.cache.get(&key).copied()
    }

    fn remember(&mut self, key: (u8, Bd, Bd, Bd), r: Bd) {
        if self.cache.len() > 8_000_000 {
            self.cache.clear();
        }
        self.cache.insert(key, r);
    }

    pub fn not(&mut self, f: Bd) -> BResult {
        if f <= TRUE {
            return Ok(f ^ 1);
        }
        let key = (OP_NOT, f, 0, 0);
        if let Some(r) = self.cached(key) {
            return Ok(r);
        }
        let n = self.nodes[f as usize];
        let lo = self.not(n.lo)?;
        let hi = self.not(n.hi)?;
        let r = self.mk(n.var, lo, hi)?;
        self.remember(key, r);
        self.remember((OP_NOT, r, 0, 0), f);
        Ok(r)
    }

    pub fn and(&mut self, a: Bd, b: Bd) -> BResult {
        if a == b || b == TRUE {
            return Ok(a);
        }
        if a == TRUE {
            return Ok(b);
        }
        if a == FALSE || b == FALSE {
            return Ok(FALSE);
        }
        self.apply(OP_AND, a, b)
    }

    pub fn or(&mut self, a: Bd, b: Bd) -> BResult {
        if a == b || b == FALSE {
            return Ok(a);
        }
        if a == FALSE {
            return Ok(b);
        }
        if a == TRUE || b == TRUE {
            return Ok(TRUE);
        }
        self.apply(OP_OR, a, b)
    }

    pub fn xor(&mut self, a: Bd, b: Bd) -> BResult {
        if a == b {
            return Ok(FALSE);
        }
        if a == FALSE {
            return Ok(b);
        }
        if b == FALSE {
            return Ok(a);
        }
        if a == TRUE {
            return self.not(b);
        }
        if b == TRUE {
            return self.not(a);
        }
        self.apply(OP_XOR, a, b)
    }

    fn apply(&mut self, op: u8, a: Bd, b: Bd) -> BResult {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        let key = (op, a, b, 0);
        if let Some(r) = self.cached(key) {
            return Ok(r);
        }
        let v = self.level(a).min(self.level(b));
        let (a0, a1) = self.split(a, v);
        let (b0, b1) = self.split(b, v);
        let (lo, hi) = match op {
            OP_AND => (self.and(a0, b0)?, self.and(a1, b1)?),
            OP_OR => (self.or(a0, b0)?, self.or(a1, b1)?),
            _ => (self.xor(a0, b0)?, self.xor(a1, b1)?),
        };
        let r = self.mk(v, lo, hi)?;
        self.remember(key, r);
        Ok(r)
    }

    /// `c ? t : e`
    pub fn ite(&mut self, c: Bd, t: Bd, e: Bd) -> BResult {
        if c == TRUE {
            return Ok(t);
        }
        if c == FALSE {
            return Ok(e);
        }
        if t == e {
            return Ok(t);
        }
        if t == TRUE && e == FALSE {
            return Ok(c);
        }
        let key = (OP_ITE, c, t, e);
        if let Some(r) = self.cached(key) {
            return Ok(r);
        }
        let v = self.level(c).min(self.level(t)).min(self.level(e));
        let (c0, c1) = self.split(c, v);
        let (t0, t1) = self.split(t, v);
        let (e0, e1) = self.split(e, v);
        let lo = self.ite(c0, t0, e0)?;
        let hi = self.ite(c1, t1, e1)?;
        let r = self.mk(v, lo, hi)?;
        self.remember(key, r);
        Ok(r)
    }

    /// `f` with variable `v` fixed to `value`.
    pub fn restrict(&mut self, f: Bd, v: u32, value: bool) -> BResult {
        let n = self.nodes[f as usize];
        if n.var == TERMINAL || n.var > v {
            return Ok(f);
        }
        if n.var == v {
            return Ok(if value { n.hi } else { n.lo });
        }
        let key = (if value { OP_R1 } else { OP_R0 }, f, v, 0);
        if let Some(r) = self.cached(key) {
            return Ok(r);
        }
        let lo = self.restrict(n.lo, v, value)?;
        let hi = self.restrict(n.hi, v, value)?;
        let r = self.mk(n.var, lo, hi)?;
        self.remember(key, r);
        Ok(r)
    }

    /// `f` with several variables fixed.
    pub fn restrict_all(&mut self, mut f: Bd, assign: &[(u32, bool)]) -> BResult {
        for &(v, value) in assign {
            f = self.restrict(f, v, value)?;
        }
        Ok(f)
    }

    /// Existential quantification of `vars` (any order).
    pub fn exists(&mut self, f: Bd, vars: &[u32]) -> BResult {
        let set: FxHashSet<u32> = vars.iter().copied().collect();
        let max = vars.iter().copied().max().unwrap_or(0);
        let mut memo = FxHashMap::default();
        self.exists_rec(f, &set, max, &mut memo)
    }

    fn exists_rec(
        &mut self,
        f: Bd,
        set: &FxHashSet<u32>,
        max: u32,
        memo: &mut FxHashMap<Bd, Bd>,
    ) -> BResult {
        let n = self.nodes[f as usize];
        if n.var == TERMINAL || n.var > max {
            return Ok(f);
        }
        if let Some(&r) = memo.get(&f) {
            return Ok(r);
        }
        let lo = self.exists_rec(n.lo, set, max, memo)?;
        let hi = self.exists_rec(n.hi, set, max, memo)?;
        let r = if set.contains(&n.var) {
            self.or(lo, hi)?
        } else {
            self.mk(n.var, lo, hi)?
        };
        memo.insert(f, r);
        Ok(r)
    }

    /// Universal quantification of `vars`.
    pub fn forall(&mut self, f: Bd, vars: &[u32]) -> BResult {
        let nf = self.not(f)?;
        let e = self.exists(nf, vars)?;
        self.not(e)
    }

    /// Variables `f` depends on, ascending.
    pub fn support(&self, f: Bd) -> Vec<u32> {
        let mut seen = FxHashSet::default();
        let mut vars = FxHashSet::default();
        let mut stack = vec![f];
        while let Some(x) = stack.pop() {
            if x <= TRUE || !seen.insert(x) {
                continue;
            }
            let n = self.nodes[x as usize];
            vars.insert(n.var);
            stack.push(n.lo);
            stack.push(n.hi);
        }
        let mut v: Vec<u32> = vars.into_iter().collect();
        v.sort_unstable();
        v
    }

    /// Number of internal nodes of `f`.
    pub fn size(&self, f: Bd) -> usize {
        let mut seen = FxHashSet::default();
        let mut stack = vec![f];
        while let Some(x) = stack.pop() {
            if x <= TRUE || !seen.insert(x) {
                continue;
            }
            let n = self.nodes[x as usize];
            stack.push(n.lo);
            stack.push(n.hi);
        }
        seen.len()
    }

    pub fn eval(&self, mut f: Bd, assign: &dyn Fn(u32) -> bool) -> bool {
        while f > TRUE {
            let n = self.nodes[f as usize];
            f = if assign(n.var) { n.hi } else { n.lo };
        }
        f == TRUE
    }

    /// Number of assignments of `vars` that satisfy `f`. `vars` must be in
    /// ascending order, hold at most 120 variables and include the support of `f`.
    pub fn sat_count(&self, f: Bd, vars: &[u32]) -> Option<u128> {
        if vars.len() > 120 || vars.windows(2).any(|w| w[0] >= w[1]) {
            return None;
        }
        let pos: FxHashMap<u32, usize> = vars.iter().enumerate().map(|(i, &v)| (v, i)).collect();
        let mut memo: FxHashMap<Bd, u128> = FxHashMap::default();
        // count(f, i): assignments of vars[i..] satisfying f.
        fn count(
            b: &Bdd,
            f: Bd,
            i: usize,
            n: usize,
            pos: &FxHashMap<u32, usize>,
            memo: &mut FxHashMap<Bd, u128>,
        ) -> Option<u128> {
            if f == FALSE {
                return Some(0);
            }
            if f == TRUE {
                return Some(1u128 << (n - i));
            }
            let node = b.nodes[f as usize];
            let p = *pos.get(&node.var)?;
            if p < i {
                return None;
            }
            // Memo holds count(f, p): from f's own variable on.
            let own = match memo.get(&f) {
                Some(&c) => c,
                None => {
                    let c = count(b, node.lo, p + 1, n, pos, memo)?
                        + count(b, node.hi, p + 1, n, pos, memo)?;
                    memo.insert(f, c);
                    c
                }
            };
            Some(own << (p - i))
        }
        count(self, f, 0, vars.len(), &pos, &mut memo)
    }

    /// Smallest and largest value of the number formed by `vars_msb_first`
    /// among the assignments satisfying `f`. The variables must appear in
    /// ascending level order (true for one bus under `order_vars`), number at
    /// most 127, and include the support of `f`. `None` if `f` is unsatisfiable.
    pub fn min_max(&self, f: Bd, vars_msb_first: &[u32]) -> Option<(u128, u128)> {
        let vars = vars_msb_first;
        if f == FALSE || vars.len() > 127 || vars.windows(2).any(|w| w[0] >= w[1]) {
            return None;
        }
        let walk = |prefer_one: bool| -> Option<u128> {
            let mut value = 0u128;
            let mut x = f;
            for &v in vars {
                value <<= 1;
                let n = self.nodes[x as usize];
                let bit = if n.var == v {
                    // A reduced BDD has no unsatisfiable node except FALSE.
                    let (first, second) = if prefer_one { (n.hi, n.lo) } else { (n.lo, n.hi) };
                    if first != FALSE {
                        x = first;
                        prefer_one
                    } else {
                        x = second;
                        !prefer_one
                    }
                } else {
                    if n.var != TERMINAL && n.var < v {
                        return None; // support outside `vars`
                    }
                    prefer_one
                };
                value |= bit as u128;
            }
            (x == TRUE).then_some(value)
        };
        Some((walk(false)?, walk(true)?))
    }

    /// All values of the number formed by `vars_msb_first` that satisfy `f`,
    /// ascending; `None` if there are more than `max` (or the preconditions of
    /// `min_max` do not hold).
    pub fn sat_values(&self, f: Bd, vars_msb_first: &[u32], max: usize) -> Option<Vec<u128>> {
        let vars = vars_msb_first;
        if vars.len() > 127 || vars.windows(2).any(|w| w[0] >= w[1]) {
            return None;
        }
        let mut out = Vec::new();
        fn go(b: &Bdd, f: Bd, i: usize, vars: &[u32], acc: u128, max: usize, out: &mut Vec<u128>) -> bool {
            if f == FALSE {
                return true;
            }
            if i == vars.len() {
                if f != TRUE || out.len() >= max {
                    return false;
                }
                out.push(acc);
                return true;
            }
            let n = b.nodes[f as usize];
            let (lo, hi) = if n.var == vars[i] { (n.lo, n.hi) } else { (f, f) };
            if n.var != TERMINAL && n.var < vars[i] {
                return false;
            }
            go(b, lo, i + 1, vars, acc << 1, max, out)
                && go(b, hi, i + 1, vars, acc << 1 | 1, max, out)
        }
        go(self, f, 0, vars, 0, max, &mut out).then_some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mgr(n: u32) -> (Bdd, Vec<Bd>) {
        let mut b = Bdd::new(1 << 20);
        let vars = (0..n)
            .map(|_| {
                let v = b.new_var();
                b.var(v).unwrap()
            })
            .collect();
        (b, vars)
    }

    #[test]
    fn equal_functions_are_the_same_node() {
        let (mut b, v) = mgr(3);
        let ab = b.and(v[0], v[1]).unwrap();
        let ba = b.and(v[1], v[0]).unwrap();
        assert_eq!(ab, ba);
        let na = b.not(v[0]).unwrap();
        assert_eq!(b.or(v[0], na).unwrap(), TRUE);
        assert_eq!(b.and(v[0], na).unwrap(), FALSE);
        assert_eq!(b.xor(v[2], v[2]).unwrap(), FALSE);
        assert_eq!(b.not(na).unwrap(), v[0]);
    }

    #[test]
    fn de_morgan() {
        let (mut b, v) = mgr(2);
        let ab = b.and(v[0], v[1]).unwrap();
        let lhs = b.not(ab).unwrap();
        let na = b.not(v[0]).unwrap();
        let nb = b.not(v[1]).unwrap();
        assert_eq!(lhs, b.or(na, nb).unwrap());
    }

    #[test]
    fn ite_matches_its_definition() {
        let (mut b, v) = mgr(3);
        let i = b.ite(v[0], v[1], v[2]).unwrap();
        let t = b.and(v[0], v[1]).unwrap();
        let nc = b.not(v[0]).unwrap();
        let e = b.and(nc, v[2]).unwrap();
        assert_eq!(i, b.or(t, e).unwrap());
        assert_eq!(b.ite(TRUE, v[1], v[2]).unwrap(), v[1]);
        assert_eq!(b.ite(v[0], TRUE, FALSE).unwrap(), v[0]);
    }

    #[test]
    fn restrict_fixes_a_variable() {
        let (mut b, v) = mgr(3);
        let f = b.ite(v[1], v[0], v[2]).unwrap();
        assert_eq!(b.restrict(f, 1, true).unwrap(), v[0]);
        assert_eq!(b.restrict(f, 1, false).unwrap(), v[2]);
        assert_eq!(b.restrict(v[0], 2, true).unwrap(), v[0]);
        assert_eq!(b.restrict_all(f, &[(1, true), (0, true)]).unwrap(), TRUE);
    }

    #[test]
    fn quantification() {
        let (mut b, v) = mgr(3);
        let f = b.and(v[0], v[1]).unwrap();
        assert_eq!(b.exists(f, &[1]).unwrap(), v[0]);
        assert_eq!(b.forall(f, &[1]).unwrap(), FALSE);
        let g = b.or(v[0], v[1]).unwrap();
        assert_eq!(b.forall(g, &[1]).unwrap(), v[0]);
        assert_eq!(b.exists(g, &[0, 1]).unwrap(), TRUE);
        assert_eq!(b.exists(f, &[2]).unwrap(), f);
    }

    #[test]
    fn support_and_size() {
        let (mut b, v) = mgr(4);
        let f = b.xor(v[0], v[3]).unwrap();
        assert_eq!(b.support(f), [0, 3]);
        assert_eq!(b.size(f), 3);
        assert_eq!(b.support(TRUE), Vec::<u32>::new());
        assert_eq!(b.size(FALSE), 0);
        assert_eq!(b.top_var(f), Some(0));
        assert_eq!(b.top_var(TRUE), None);
    }

    #[test]
    fn sat_count_over_a_variable_set() {
        let (mut b, v) = mgr(4);
        let f = b.and(v[1], v[3]).unwrap();
        assert_eq!(b.sat_count(f, &[1, 3]), Some(1));
        assert_eq!(b.sat_count(f, &[0, 1, 2, 3]), Some(4));
        assert_eq!(b.sat_count(TRUE, &[0, 1, 2]), Some(8));
        assert_eq!(b.sat_count(FALSE, &[0, 1, 2]), Some(0));
        assert_eq!(b.sat_count(f, &[1]), None, "support not covered");
    }

    /// Function "the number v[0..n] (v[0] = MSB) is in `values`".
    fn set_of(b: &mut Bdd, v: &[Bd], values: &[u32]) -> Bd {
        let mut f = FALSE;
        for &val in values {
            let mut cube = TRUE;
            for (i, &x) in v.iter().enumerate() {
                let bit = val >> (v.len() - 1 - i) & 1 == 1;
                let lit = if bit { x } else { b.not(x).unwrap() };
                cube = b.and(cube, lit).unwrap();
            }
            f = b.or(f, cube).unwrap();
        }
        f
    }

    #[test]
    fn min_max_and_enumeration_of_a_number() {
        let (mut b, v) = mgr(4);
        let f = set_of(&mut b, &v, &[3, 5, 6, 12]);
        assert_eq!(b.min_max(f, &[0, 1, 2, 3]), Some((3, 12)));
        assert_eq!(b.sat_values(f, &[0, 1, 2, 3], 8), Some(vec![3, 5, 6, 12]));
        assert_eq!(b.sat_values(f, &[0, 1, 2, 3], 3), None, "more than max");
        assert_eq!(b.min_max(FALSE, &[0, 1]), None);
        assert_eq!(b.min_max(TRUE, &[0, 1, 2]), Some((0, 7)));
        // A function that ignores the low bits: don't-care bits fill with 0 / 1.
        assert_eq!(b.min_max(v[0], &[0, 1, 2, 3]), Some((8, 15)));
    }

    #[test]
    fn interval_is_detected_by_count_and_bounds() {
        let (mut b, v) = mgr(4);
        let vals: Vec<u32> = (3..11).collect();
        let f = set_of(&mut b, &v, &vals);
        let (lo, hi) = b.min_max(f, &[0, 1, 2, 3]).unwrap();
        assert_eq!((lo, hi), (3, 10));
        assert_eq!(b.sat_count(f, &[0, 1, 2, 3]), Some(hi - lo + 1));
    }

    #[test]
    fn eval_follows_the_assignment() {
        let (mut b, v) = mgr(3);
        let f = b.ite(v[0], v[1], v[2]).unwrap();
        assert!(b.eval(f, &|x| x == 0 || x == 1));
        assert!(!b.eval(f, &|x| x == 0));
        assert!(b.eval(f, &|x| x == 2));
    }

    #[test]
    fn random_formulas_match_their_truth_tables() {
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let (mut b, v) = mgr(6);
            // Stack machine over (bdd, truth table).
            let mut stack: Vec<(Bd, u64)> = Vec::new();
            for _ in 0..40 {
                let r = rnd();
                match r % 5 {
                    0 | 1 => {
                        let i = (r >> 8) as usize % 6;
                        let mut tt = 0u64;
                        for row in 0..64u64 {
                            if row >> i & 1 == 1 {
                                tt |= 1 << row;
                            }
                        }
                        stack.push((v[i], tt));
                    }
                    2 if !stack.is_empty() => {
                        let (f, t) = stack.pop().unwrap();
                        stack.push((b.not(f).unwrap(), !t));
                    }
                    _ if stack.len() >= 2 => {
                        let (f, t) = stack.pop().unwrap();
                        let (g, u) = stack.pop().unwrap();
                        stack.push(match (r >> 16) % 3 {
                            0 => (b.and(f, g).unwrap(), t & u),
                            1 => (b.or(f, g).unwrap(), t | u),
                            _ => (b.xor(f, g).unwrap(), t ^ u),
                        });
                    }
                    _ => {}
                }
            }
            for (f, tt) in stack {
                for row in 0..64u64 {
                    assert_eq!(b.eval(f, &|x| row >> x & 1 == 1), tt >> row & 1 == 1);
                }
            }
        }
    }

    #[test]
    fn node_limit_reports_blowup_and_leaves_the_manager_usable() {
        let mut b = Bdd::new(40);
        let vars: Vec<Bd> = (0..16)
            .map(|_| {
                let v = b.new_var();
                b.var(v).unwrap()
            })
            .collect();
        // x0&x8 | x1&x9 | ... needs an exponential BDD in this order.
        let mut f = FALSE;
        let mut blew = false;
        for i in 0..8 {
            let r = b.and(vars[i], vars[i + 8]).and_then(|t| b.or(f, t));
            match r {
                Ok(x) => f = x,
                Err(Blowup) => {
                    blew = true;
                    break;
                }
            }
        }
        assert!(blew);
        assert_eq!(b.and(vars[0], vars[0]).unwrap(), vars[0]);
        assert!(b.node_count() <= 40);
    }

    #[test]
    fn per_operation_budget() {
        let (mut b, v) = mgr(8);
        b.set_budget(2);
        let mut f = TRUE;
        let mut blew = false;
        for &x in &v {
            match b.and(f, x) {
                Ok(r) => f = r,
                Err(Blowup) => {
                    blew = true;
                    break;
                }
            }
        }
        assert!(blew);
        b.clear_budget();
        assert!(b.and(v[0], v[1]).is_ok());
    }
}

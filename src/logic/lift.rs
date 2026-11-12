//! Turning the boolean function of a wire into a readable expression.
//!
//! The function is canonical (a BDD), so "recognising" an operator means
//! building the BDD of that operator and comparing: a match is a proof, never a
//! guess. Recognition goes from the most specific shapes (bus predicates and
//! comparisons, index and shift, arithmetic bits) to the general ones (boolean
//! decomposition, multiplexers, product terms).
//!
//! Some single bits are genuinely ambiguous: the top bit of `cnt + K` is also
//! a range test on `cnt`. `LiftOpts::prefer_arith` chooses which one is shown.

use std::collections::BTreeMap;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::bdd::{Bd, Bdd, FALSE, TRUE};
use super::bus::VarInfo;
use super::expr::{Arith, CmpOp, Expr, SelKind, Word};
use super::isop;
use super::words;

#[derive(Debug, Clone)]
pub struct LiftOpts {
    /// Give up on the product-term form beyond this many cubes.
    pub max_cubes: usize,
    /// Do not try to lift functions of more endpoints than this.
    pub max_support: usize,
    /// Widest bus accepted as an index or shift amount.
    pub sel_width: usize,
    /// Largest total operand width for which `*` is tried.
    pub mul_width: usize,
    /// Recursion depth of the decomposition.
    pub depth: usize,
    /// Show `(cnt + K)[k]` rather than the equivalent range test whenever
    /// both describe the wire.
    pub prefer_arith: bool,
}

impl Default for LiftOpts {
    fn default() -> Self {
        LiftOpts {
            max_cubes: 64,
            max_support: 96,
            sel_width: 10,
            mul_width: 16,
            depth: 10,
            prefer_arith: false,
        }
    }
}

/// How many sub-functions one top-level `lift` may analyse.
const WORK: usize = 400;

/// The bits of one bus (or one scalar) inside the support of a function.
#[derive(Debug, Clone)]
struct Group {
    /// Variable levels, least significant bit first.
    vars: Vec<u32>,
    /// Declared index of `vars[0]`.
    lo: i64,
    scalar: bool,
    /// The declared indices are consecutive.
    contiguous: bool,
}

impl Group {
    fn width(&self) -> usize {
        self.vars.len()
    }

    fn word(&self) -> Word {
        Word::vars(&self.vars, false)
    }

    fn index_of(&self, var: u32) -> Option<i64> {
        self.vars
            .iter()
            .position(|&v| v == var)
            .map(|p| self.lo + p as i64)
    }
}

/// A cofactor that is a constant or a single literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Entry {
    Const(bool),
    Lit(u32, bool),
}

pub struct Lifter<'a> {
    pub bdd: &'a mut Bdd,
    pub vars: &'a [VarInfo],
    pub opts: LiftOpts,
    memo: FxHashMap<Bd, Option<Rc<Expr>>>,
    work: usize,
    mismatch: bool,
    level_of: FxHashMap<(u32, i64), u32>,
}

fn var(v: u32) -> Rc<Expr> {
    Rc::new(Expr::Var(v))
}

fn lit(v: u32, positive: bool) -> Rc<Expr> {
    if positive { var(v) } else { Rc::new(Expr::Not(var(v))) }
}

fn mk_and(parts: Vec<Rc<Expr>>) -> Rc<Expr> {
    let mut out = Vec::new();
    for p in parts {
        match &*p {
            Expr::And(xs) => out.extend(xs.iter().cloned()),
            _ => out.push(p),
        }
    }
    Rc::new(Expr::And(out))
}

fn mk_or(parts: Vec<Rc<Expr>>) -> Rc<Expr> {
    let mut out = Vec::new();
    for p in parts {
        match &*p {
            Expr::Or(xs) => out.extend(xs.iter().cloned()),
            _ => out.push(p),
        }
    }
    Rc::new(Expr::Or(out))
}

fn mk_xor(parts: Vec<Rc<Expr>>) -> Rc<Expr> {
    let mut out = Vec::new();
    for p in parts {
        match &*p {
            Expr::Xor(xs) => out.extend(xs.iter().cloned()),
            _ => out.push(p),
        }
    }
    Rc::new(Expr::Xor(out))
}

/// Shorter operand first; equal sizes keep their order.
fn by_size(mut parts: Vec<Rc<Expr>>) -> Vec<Rc<Expr>> {
    parts.sort_by_key(|p| p.size());
    parts
}

impl<'a> Lifter<'a> {
    pub fn new(bdd: &'a mut Bdd, vars: &'a [VarInfo], opts: LiftOpts) -> Self {
        Lifter {
            bdd,
            vars,
            opts,
            memo: FxHashMap::default(),
            work: 0,
            mismatch: false,
            level_of: vars
                .iter()
                .enumerate()
                .filter_map(|(l, v)| Some(((v.bus, v.index?), l as u32)))
                .collect(),
        }
    }

    /// The most readable expression found for `f`, or `None` if `f` is beyond
    /// the limits (size, or the effort limit set on the BDD). The result is
    /// always proven equal to `f`.
    pub fn lift(&mut self, f: Bd) -> Option<Rc<Expr>> {
        self.work = WORK;
        let e = self.lift_rec(f, self.opts.depth)?;
        // The final proof must not be cut short by the effort limit.
        let limit = self.bdd.take_ops_limit();
        let proven = self.equals(f, &e);
        self.bdd.set_ops_limit(limit);
        if proven {
            return Some(e);
        }
        // Should be unreachable; never print an expression that is not exact.
        self.mismatch = true;
        None
    }

    /// True if a lifted expression failed its final proof since the last call.
    pub fn take_mismatch(&mut self) -> bool {
        std::mem::take(&mut self.mismatch)
    }

    /// Drop every BDD node not reachable from `roots` (which are renumbered).
    pub fn gc(&mut self, roots: &mut [Bd]) {
        self.memo.clear();
        self.bdd.gc(roots);
    }

    fn equals(&mut self, f: Bd, e: &Expr) -> bool {
        matches!(e.to_bdd(self.bdd), Ok(g) if g == f)
    }

    /// `e` if it is exactly `f`.
    fn check(&mut self, f: Bd, e: Expr) -> Option<Rc<Expr>> {
        self.equals(f, &e).then(|| Rc::new(e))
    }

    fn lift_rec(&mut self, f: Bd, depth: usize) -> Option<Rc<Expr>> {
        if let Some(m) = self.memo.get(&f) {
            return m.clone();
        }
        let r = self.lift_inner(f, depth);
        // A result obtained after the effort ran out says nothing about `f`.
        if !self.bdd.ops_exhausted() {
            self.memo.insert(f, r.clone());
        }
        r
    }

    fn lift_inner(&mut self, f: Bd, depth: usize) -> Option<Rc<Expr>> {
        if f <= TRUE {
            return Some(Rc::new(Expr::Const(f == TRUE)));
        }
        let sup = self.bdd.support(f);
        if let [v] = sup[..] {
            return Some(lit(v, self.bdd.eval(f, &|x| x == v)));
        }
        if sup.len() > self.opts.max_support {
            return None;
        }
        if self.work == 0 || depth == 0 {
            return self.sop(f);
        }
        self.work -= 1;
        let groups = self.groups(&sup);
        if let Some(e) = self.leaf(f, &groups, sup.len()) {
            return Some(e);
        }
        let cands = [
            self.decompose(f, &groups, depth),
            self.mux_decompose(f, &sup, depth),
            self.case_shape(f, &groups, depth),
            self.sop(f),
            self.neg_sop(f),
        ];
        cands.into_iter().flatten().min_by_key(|e| e.size())
    }

    // ---- structure of the support ------------------------------------------

    fn groups(&self, sup: &[u32]) -> Vec<Group> {
        let mut buses: BTreeMap<u32, Vec<(i64, u32)>> = BTreeMap::new();
        let mut scalars: Vec<u32> = Vec::new();
        for &v in sup {
            let info = &self.vars[v as usize];
            match info.index {
                Some(i) => buses.entry(info.bus).or_default().push((i, v)),
                None => scalars.push(v),
            }
        }
        let mut out = Vec::new();
        for (_, mut bits) in buses {
            if bits.len() == 1 {
                scalars.push(bits[0].1);
                continue;
            }
            bits.sort_unstable();
            out.push(Group {
                contiguous: bits.windows(2).all(|w| w[1].0 == w[0].0 + 1),
                lo: bits[0].0,
                vars: bits.into_iter().map(|(_, v)| v).collect(),
                scalar: false,
            });
        }
        scalars.sort_unstable();
        out.extend(scalars.into_iter().map(|v| Group {
            vars: vec![v],
            lo: 0,
            scalar: true,
            contiguous: true,
        }));
        out
    }

    // ---- specific shapes ---------------------------------------------------

    fn leaf(&mut self, f: Bd, groups: &[Group], sup_len: usize) -> Option<Rc<Expr>> {
        if let [g] = groups
            && !g.scalar
            && g.contiguous
            && g.width() == sup_len
        {
            if self.opts.prefer_arith
                && let Some(e) = self.mul_const(f, g)
            {
                return Some(e);
            }
            if let Some(e) = self.predicate(f, g) {
                return Some(e);
            }
        }
        if let [a, b] = groups
            && !a.scalar
            && !b.scalar
            && a.contiguous
            && b.contiguous
            && let Some(e) = self.compare(f, a, b)
        {
            return Some(e);
        }
        if let Some(e) = self.select_shape(f, groups) {
            return Some(e);
        }
        self.arith_shape(f, groups)
    }

    /// A predicate over one bus: equality, range, set membership, or the top
    /// bit of the bus plus a constant.
    fn predicate(&mut self, f: Bd, g: &Group) -> Option<Rc<Expr>> {
        fn is_order(e: &Expr) -> bool {
            match e {
                Expr::Cmp { op, .. } => !matches!(op, CmpOp::Eq | CmpOp::Ne),
                Expr::And(xs) | Expr::Or(xs) => xs.iter().all(|x| is_order(x)),
                _ => false,
            }
        }
        let e = self.predicate_on(f, g)?;
        // `cnt[3:0] < 10` does not depend on cnt[0], so the function is only
        // over cnt[3:1], where it reads `cnt[3:1] < 5`. Order tests are shown
        // over the bus down to its lowest existing bit instead. Equality and
        // sets stay on the slice: `cnt[7:4] == 5` is the natural form.
        if is_order(&e) {
            let bus = self.vars[g.vars[0] as usize].bus;
            let mut ext = g.clone();
            while let Some(&v) = self.level_of.get(&(bus, ext.lo - 1)) {
                ext.vars.insert(0, v);
                ext.lo -= 1;
            }
            if ext.width() > g.width()
                && let Some(x) = self.predicate_on(f, &ext)
                && is_order(&x)
            {
                return Some(x);
            }
        }
        Some(e)
    }

    fn predicate_on(&mut self, f: Bd, g: &Group) -> Option<Rc<Expr>> {
        let w = g.width();
        if !(2..=64).contains(&w) {
            return None;
        }
        let msb_first: Vec<u32> = g.vars.iter().rev().copied().collect();
        let full = 1u128 << w;
        let word = g.word();
        let k = |v: u128| Word::constant(v, w);
        let cmp = |op: CmpOp, v: u128| {
            Rc::new(Expr::Cmp {
                op,
                a: word.clone(),
                b: k(v),
            })
        };
        let nf = self.bdd.not(f).ok()?;
        let count = self.bdd.sat_count(f, &msb_first)?;
        let ncount = full - count;
        let (lo, hi) = self.bdd.min_max(f, &msb_first)?;
        let (nlo, nhi) = self.bdd.min_max(nf, &msb_first)?;

        let e: Rc<Expr> = if count == 1 {
            cmp(CmpOp::Eq, lo)
        } else if ncount == 1 {
            cmp(CmpOp::Ne, nlo)
        } else if lo == 0 && count == hi + 1 {
            cmp(CmpOp::Lt, hi + 1)
        } else if hi == full - 1 && count == full - lo {
            cmp(CmpOp::Ge, lo)
        } else {
            // Exactly half of the values in one (cyclic) run: the top bit of
            // `bus + K`. Shown as arithmetic for small steps (counters).
            if count == full / 2
                && w >= 4
                && let Some((e, small)) = self.add_const(f, g)
                && (small || self.opts.prefer_arith)
            {
                return Some(e);
            }
            if count <= 8 {
                let vals = self.bdd.sat_values(f, &msb_first, 8)?;
                Rc::new(Expr::Inside { a: word.clone(), vals })
            } else if count == hi - lo + 1 {
                mk_and(vec![cmp(CmpOp::Ge, lo), cmp(CmpOp::Lt, hi + 1)])
            } else if ncount <= 8 {
                let vals = self.bdd.sat_values(nf, &msb_first, 8)?;
                Rc::new(Expr::Not(Rc::new(Expr::Inside { a: word.clone(), vals })))
            } else if ncount == nhi - nlo + 1 {
                mk_or(vec![cmp(CmpOp::Lt, nlo), cmp(CmpOp::Gt, nhi)])
            } else {
                return None;
            }
        };
        self.equals(f, &e).then_some(e)
    }

    /// Solve `f = top bit of (bus + K)` for `K`. Also says whether the step
    /// is small (at most 2 up or down).
    fn add_const(&mut self, f: Bd, g: &Group) -> Option<(Rc<Expr>, bool)> {
        let w = g.width();
        let top = w - 1;
        let zeros: Vec<(u32, bool)> = g.vars.iter().map(|&v| (v, false)).collect();
        let k_top = self.bdd.restrict_all(f, &zeros).ok()? == TRUE;
        // With the top bit of the bus at 0, f is K's top bit xor the carry.
        let mut carry = self.bdd.restrict(f, g.vars[top], false).ok()?;
        if k_top {
            carry = self.bdd.not(carry).ok()?;
        }
        let k_low = if carry == FALSE {
            0
        } else {
            let low: Vec<u32> = g.vars[..top].iter().rev().copied().collect();
            let (min, max) = self.bdd.min_max(carry, &low)?;
            if max != (1u128 << top) - 1 {
                return None;
            }
            (1u128 << top) - min
        };
        let k = (u128::from(k_top) << top) + k_low;
        let neg = (1u128 << w) - k;
        let (op, c) = if neg < k { (Arith::Sub, neg) } else { (Arith::Add, k) };
        let e = self.check(
            f,
            Expr::ArithBit {
                op,
                a: g.word(),
                b: Word::constant(c, w),
                cin: None,
                bit: top as u32,
            },
        )?;
        Some((e, c <= 2))
    }

    /// Solve `f = bit of (bus * K)` for a small constant `K`.
    fn mul_const(&mut self, f: Bd, g: &Group) -> Option<Rc<Expr>> {
        let w = g.width();
        if w > 8 {
            return None;
        }
        let a = self.var_bdds(&g.vars)?;
        for k in 3u128..256 {
            let kw = 128 - k.leading_zeros() as usize;
            let kb: Vec<Bd> = (0..kw).map(|i| if k >> i & 1 == 1 { TRUE } else { FALSE }).collect();
            self.bdd.set_budget(50_000);
            let p = words::mul(self.bdd, &a, &kb);
            self.bdd.clear_budget();
            let Ok(p) = p else { continue };
            if let Some(bit) = p.iter().position(|&x| x == f) {
                return self.check(
                    f,
                    Expr::ArithBit {
                        op: Arith::Mul,
                        a: g.word(),
                        b: Word::constant(k, kw),
                        cin: None,
                        bit: bit as u32,
                    },
                );
            }
        }
        None
    }

    fn var_bdds(&mut self, vars: &[u32]) -> Option<Vec<Bd>> {
        vars.iter().map(|&v| self.bdd.var(v).ok()).collect()
    }

    /// A comparison of two buses.
    fn compare(&mut self, f: Bd, a: &Group, b: &Group) -> Option<Rc<Expr>> {
        const OPS: [CmpOp; 6] = [CmpOp::Eq, CmpOp::Ne, CmpOp::Lt, CmpOp::Ge, CmpOp::Gt, CmpOp::Le];
        for signed in [false, true] {
            let x = Word::vars(&a.vars, signed);
            let y = Word::vars(&b.vars, signed);
            for op in OPS {
                let e = Expr::Cmp {
                    op,
                    a: x.clone(),
                    b: y.clone(),
                };
                if let Some(r) = self.check(f, e) {
                    return Some(r);
                }
            }
        }
        None
    }

    /// Cofactors of `f` for every value of `sel`, if each is a literal or constant.
    fn entries(&mut self, f: Bd, sel: &Group) -> Option<Vec<Entry>> {
        let n = 1usize << sel.width();
        let mut out = Vec::with_capacity(n);
        for val in 0..n {
            let assign: Vec<(u32, bool)> = sel
                .vars
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, val >> i & 1 == 1))
                .collect();
            let c = self.bdd.restrict_all(f, &assign).ok()?;
            out.push(match c {
                TRUE => Entry::Const(true),
                FALSE => Entry::Const(false),
                _ => match self.bdd.support(c)[..] {
                    [v] => Entry::Lit(v, self.bdd.eval(c, &|x| x == v)),
                    _ => return None,
                },
            });
        }
        Some(out)
    }

    /// Buses that may act as an index, narrowest first.
    fn select_candidates(&self, groups: &[Group], max_width: usize) -> Vec<usize> {
        let mut c: Vec<usize> = (0..groups.len())
            .filter(|&i| {
                let g = &groups[i];
                !g.scalar && g.contiguous && (2..=max_width).contains(&g.width())
            })
            .collect();
        c.sort_by_key(|&i| groups[i].width());
        c.truncate(3);
        c
    }

    /// `data[sel]`, `data >> sel`, `data >>> sel` or `data << sel`.
    fn select_shape(&mut self, f: Bd, groups: &[Group]) -> Option<Rc<Expr>> {
        if groups.len() != 2 {
            return None;
        }
        for si in self.select_candidates(groups, self.opts.sel_width) {
            let sel = &groups[si];
            let data = &groups[1 - si];
            if data.scalar || !data.contiguous {
                continue;
            }
            let Some(entries) = self.entries(f, sel) else {
                continue;
            };
            // Every entry is a positive bit of the data bus, or zero.
            let idx: Option<Vec<Option<i64>>> = entries
                .iter()
                .map(|e| match *e {
                    Entry::Lit(v, true) => data.index_of(v).map(Some),
                    Entry::Const(false) => Some(None),
                    _ => None,
                })
                .collect();
            let Some(idx) = idx else { continue };
            let Some(k) = idx[0] else { continue };
            let top = data.lo + data.width() as i64 - 1;
            let sel_word = sel.word();
            let from = |lo: i64| Word::vars(&data.vars[(lo - data.lo) as usize..], false);

            // data[k + s], zero past the top: index, or logical right shift.
            if idx.iter().enumerate().all(|(s, &i)| {
                let want = k + s as i64;
                i == (want <= top).then_some(want)
            }) {
                let e = Expr::Select {
                    kind: SelKind::Index,
                    data: from(k),
                    sel: sel_word,
                    off: 0,
                };
                return self.check(f, e);
            }
            // The top bit repeats past the top: arithmetic right shift.
            if idx
                .iter()
                .enumerate()
                .all(|(s, &i)| i == Some((k + s as i64).min(top)))
            {
                let e = Expr::Select {
                    kind: SelKind::Ashr,
                    data: from(k),
                    sel: sel_word,
                    off: 0,
                };
                return self.check(f, e);
            }
            // data[k - s], zero below the bottom: left shift.
            if idx.iter().enumerate().all(|(s, &i)| {
                let want = k - s as i64;
                i == (want >= data.lo).then_some(want)
            }) {
                let e = Expr::Select {
                    kind: SelKind::Shl,
                    data: data.word(),
                    sel: sel_word,
                    off: (k - data.lo) as u32,
                };
                return self.check(f, e);
            }
        }
        None
    }

    /// A multiplexer: one simple entry per value of a narrow bus.
    fn case_shape(&mut self, f: Bd, groups: &[Group], _depth: usize) -> Option<Rc<Expr>> {
        for si in self.select_candidates(groups, 4) {
            let sel = &groups[si];
            let Some(entries) = self.entries(f, sel) else {
                continue;
            };
            if entries.iter().all(|e| matches!(e, Entry::Const(_))) {
                continue;
            }
            let items = entries
                .iter()
                .map(|e| match *e {
                    Entry::Const(c) => Rc::new(Expr::Const(c)),
                    Entry::Lit(v, p) => lit(v, p),
                })
                .collect();
            let e = Expr::Case {
                sel: sel.word(),
                items,
            };
            if let Some(r) = self.check(f, e) {
                return Some(r);
            }
        }
        None
    }

    /// One bit of the sum, difference or product of two buses.
    fn arith_shape(&mut self, f: Bd, groups: &[Group]) -> Option<Rc<Expr>> {
        let buses: Vec<&Group> = groups.iter().filter(|g| !g.scalar).collect();
        let scalars: Vec<&Group> = groups.iter().filter(|g| g.scalar).collect();
        let [x, y] = buses[..] else { return None };
        if !x.contiguous || !y.contiguous || scalars.len() > 1 {
            return None;
        }
        let cin = scalars.first().map(|g| g.vars[0]);
        let a = self.var_bdds(&x.vars)?;
        let b = self.var_bdds(&y.vars)?;
        let cin_bdd = match cin {
            Some(v) => self.bdd.var(v).ok()?,
            None => FALSE,
        };
        let found = |bits: &[Bd]| bits.iter().position(|&bit| bit == f).map(|p| p as u32);
        let arith = |op: Arith, a: &Group, b: &Group, bit: u32| Expr::ArithBit {
            op,
            a: a.word(),
            b: b.word(),
            cin,
            bit,
        };

        let sum = words::add(self.bdd, &a, &b, cin_bdd).ok()?;
        if let Some(bit) = found(&sum) {
            return self.check(f, arith(Arith::Add, x, y, bit));
        }
        if cin.is_some() {
            return None;
        }
        let diff = words::sub(self.bdd, &a, &b).ok()?;
        if let Some(bit) = found(&diff) {
            return self.check(f, arith(Arith::Sub, x, y, bit));
        }
        let diff = words::sub(self.bdd, &b, &a).ok()?;
        if let Some(bit) = found(&diff) {
            return self.check(f, arith(Arith::Sub, y, x, bit));
        }
        if x.width() + y.width() <= self.opts.mul_width {
            self.bdd.set_budget(200_000);
            let prod = words::mul(self.bdd, &a, &b);
            self.bdd.clear_budget();
            if let Ok(prod) = prod
                && let Some(bit) = found(&prod)
            {
                return self.check(f, arith(Arith::Mul, x, y, bit));
            }
        }
        None
    }

    // ---- general decomposition ---------------------------------------------

    /// `f = g(X) op h(Y)`, where `X` is one bus of the support and `Y` the rest.
    fn decompose(&mut self, f: Bd, groups: &[Group], depth: usize) -> Option<Rc<Expr>> {
        if groups.len() < 2 {
            return None;
        }
        for gi in 0..groups.len() {
            let xv = groups[gi].vars.clone();
            let yv: Vec<u32> = groups
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != gi)
                .flat_map(|(_, g)| g.vars.iter().copied())
                .collect();

            let gx = self.bdd.exists(f, &yv).ok()?;
            let hy = self.bdd.exists(f, &xv).ok()?;
            if gx != TRUE && hy != TRUE && self.bdd.and(gx, hy).ok()? == f {
                let parts = vec![self.lift_rec(gx, depth - 1)?, self.lift_rec(hy, depth - 1)?];
                return Some(mk_and(by_size(parts)));
            }
            let gx = self.bdd.forall(f, &yv).ok()?;
            let hy = self.bdd.forall(f, &xv).ok()?;
            if gx != FALSE && hy != FALSE && self.bdd.or(gx, hy).ok()? == f {
                let parts = vec![self.lift_rec(gx, depth - 1)?, self.lift_rec(hy, depth - 1)?];
                return Some(mk_or(by_size(parts)));
            }
            // f = c ^ g(X) ^ h(Y), with g and h zero at the all-zero point.
            let x0: Vec<(u32, bool)> = xv.iter().map(|&v| (v, false)).collect();
            let y0: Vec<(u32, bool)> = yv.iter().map(|&v| (v, false)).collect();
            let gx = self.bdd.restrict_all(f, &y0).ok()?;
            let hy = self.bdd.restrict_all(f, &x0).ok()?;
            let c = self.bdd.restrict_all(gx, &x0).ok()?;
            let gx = self.bdd.xor(gx, c).ok()?;
            let hy = self.bdd.xor(hy, c).ok()?;
            let both = self.bdd.xor(gx, hy).ok()?;
            if gx > TRUE && hy > TRUE && self.bdd.xor(both, c).ok()? == f {
                let parts = vec![self.lift_rec(gx, depth - 1)?, self.lift_rec(hy, depth - 1)?];
                let e = mk_xor(by_size(parts));
                return Some(if c == TRUE { Rc::new(Expr::Not(e)) } else { e });
            }
        }
        None
    }

    /// Shannon expansion on one variable: `v ? f1 : f0` and its special cases.
    fn mux_decompose(&mut self, f: Bd, sup: &[u32], depth: usize) -> Option<Rc<Expr>> {
        // Scalars are the likely selects; then the highest variables.
        let mut cands: Vec<u32> = sup.to_vec();
        cands.sort_by_key(|&v| self.vars[v as usize].index.is_some());
        let mut best: Option<Rc<Expr>> = None;
        for &v in cands.iter().take(4) {
            let f0 = self.bdd.restrict(f, v, false).ok()?;
            let f1 = self.bdd.restrict(f, v, true).ok()?;
            let d = depth - 1;
            let e = if f1 == TRUE {
                self.lift_rec(f0, d).map(|e| mk_or(vec![var(v), e]))
            } else if f0 == FALSE {
                self.lift_rec(f1, d).map(|e| mk_and(vec![var(v), e]))
            } else if f1 == FALSE {
                self.lift_rec(f0, d).map(|e| mk_and(vec![lit(v, false), e]))
            } else if f0 == TRUE {
                self.lift_rec(f1, d).map(|e| mk_or(vec![lit(v, false), e]))
            } else if self.bdd.not(f1).ok()? == f0 {
                self.lift_rec(f0, d).map(|e| mk_xor(vec![var(v), e]))
            } else {
                match (self.lift_rec(f1, d), self.lift_rec(f0, d)) {
                    (Some(t), Some(e)) => Some(Rc::new(Expr::Mux(var(v), t, e))),
                    _ => None,
                }
            };
            if let Some(e) = e
                && best.as_ref().is_none_or(|b| e.size() < b.size())
            {
                best = Some(e);
            }
        }
        best
    }

    /// Sum of products.
    fn sop(&mut self, f: Bd) -> Option<Rc<Expr>> {
        let cubes = isop::isop(self.bdd, f, self.opts.max_cubes).ok()??;
        Some(self.cover_expr(&cubes))
    }

    /// Negated sum of products of the complement.
    fn neg_sop(&mut self, f: Bd) -> Option<Rc<Expr>> {
        let nf = self.bdd.not(f).ok()?;
        let cubes = isop::isop(self.bdd, nf, self.opts.max_cubes).ok()??;
        Some(Rc::new(Expr::Not(self.cover_expr(&cubes))))
    }

    fn cover_expr(&self, cubes: &[isop::Cube]) -> Rc<Expr> {
        match cubes {
            [] => Rc::new(Expr::Const(false)),
            [one] => self.cube_expr(one),
            _ => Rc::new(Expr::Or(cubes.iter().map(|c| self.cube_expr(c)).collect())),
        }
    }

    /// One product term. Literals on consecutive bits of one bus are merged
    /// into `bus[hi:lo] == value`.
    fn cube_expr(&self, cube: &isop::Cube) -> Rc<Expr> {
        if cube.is_empty() {
            return Rc::new(Expr::Const(true));
        }
        let mut terms: Vec<Rc<Expr>> = Vec::new();
        let mut i = 0;
        while i < cube.len() {
            // A cube is sorted by level, i.e. by descending index within a bus.
            let first = &self.vars[cube[i].0 as usize];
            let mut j = i + 1;
            while j < cube.len() {
                let next = &self.vars[cube[j].0 as usize];
                let want = first.index.map(|x| x - (j - i) as i64);
                if next.bus != first.bus || want.is_none() || next.index != want {
                    break;
                }
                j += 1;
            }
            if j - i >= 2 {
                let lsb_first: Vec<u32> = cube[i..j].iter().rev().map(|&(v, _)| v).collect();
                let value = cube[i..j]
                    .iter()
                    .fold(0u128, |acc, &(_, p)| acc << 1 | u128::from(p));
                terms.push(Rc::new(Expr::Cmp {
                    op: CmpOp::Eq,
                    a: Word::vars(&lsb_first, false),
                    b: Word::constant(value, j - i),
                }));
            } else {
                terms.push(lit(cube[i].0, cube[i].1));
            }
            i = j;
        }
        if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            Rc::new(Expr::And(terms))
        }
    }
}

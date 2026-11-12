//! Word-level operations over BDD bit vectors.
//!
//! Vectors are *little-endian*: `bits[0]` is the least significant bit. These
//! are the primitives the recognizers use to build the function of a
//! hypothesised operator, which is then compared with a wire's function.

use super::bdd::{BResult, Bd, Bdd, Blowup, FALSE, TRUE};

/// `Ok` vector of bits, or the BDD grew too large.
pub type VResult = Result<Vec<Bd>, Blowup>;

/// `a` padded to `width` bits: zero-extended, or sign-extended if `signed`.
pub fn extend(a: &[Bd], width: usize, signed: bool) -> Vec<Bd> {
    let fill = match a.last() {
        Some(&msb) if signed => msb,
        _ => FALSE,
    };
    let mut v = a.to_vec();
    if v.len() < width {
        v.resize(width, fill);
    }
    v
}

fn xnor(b: &mut Bdd, x: Bd, y: Bd) -> BResult {
    let d = b.xor(x, y)?;
    b.not(d)
}

/// `a + c + cin`. The result has `max(len) + 1` bits, so it never overflows.
pub fn add(b: &mut Bdd, a: &[Bd], c: &[Bd], cin: Bd) -> VResult {
    let w = a.len().max(c.len());
    let mut out = Vec::with_capacity(w + 1);
    let mut carry = cin;
    for i in 0..w {
        let x = a.get(i).copied().unwrap_or(FALSE);
        let y = c.get(i).copied().unwrap_or(FALSE);
        let half = b.xor(x, y)?;
        out.push(b.xor(half, carry)?);
        let generate = b.and(x, y)?;
        let propagate = b.and(half, carry)?;
        carry = b.or(generate, propagate)?;
    }
    out.push(carry);
    Ok(out)
}

/// `a - c` modulo `2^w`, where `w = max(len) + 1` (two's complement).
pub fn sub(b: &mut Bdd, a: &[Bd], c: &[Bd]) -> VResult {
    let w = a.len().max(c.len()) + 1;
    let a = extend(a, w, false);
    let mut nc = Vec::with_capacity(w);
    for x in extend(c, w, false) {
        nc.push(b.not(x)?);
    }
    let mut r = add(b, &a, &nc, TRUE)?;
    r.truncate(w);
    Ok(r)
}

/// `a * c`, `a.len() + c.len()` bits. BDDs of products grow exponentially:
/// callers must set a node budget first.
pub fn mul(b: &mut Bdd, a: &[Bd], c: &[Bd]) -> VResult {
    let w = a.len() + c.len();
    let mut acc = vec![FALSE; w];
    for (i, &y) in c.iter().enumerate() {
        let mut row = vec![FALSE; w];
        for (j, &x) in a.iter().enumerate() {
            row[i + j] = b.and(x, y)?;
        }
        acc = add(b, &acc, &row, FALSE)?;
        acc.truncate(w);
    }
    Ok(acc)
}

/// `a == c`; the shorter operand is zero-extended.
pub fn eq(b: &mut Bdd, a: &[Bd], c: &[Bd]) -> BResult {
    let w = a.len().max(c.len());
    let (a, c) = (extend(a, w, false), extend(c, w, false));
    let mut f = TRUE;
    // MSB first keeps intermediate results small under an MSB-first order.
    for i in (0..w).rev() {
        let same = xnor(b, a[i], c[i])?;
        f = b.and(f, same)?;
    }
    Ok(f)
}

/// Unsigned `a < c`; the shorter operand is zero-extended.
pub fn ult(b: &mut Bdd, a: &[Bd], c: &[Bd]) -> BResult {
    let w = a.len().max(c.len());
    let (a, c) = (extend(a, w, false), extend(c, w, false));
    // From the LSB up: less = (!a[i] & c[i]) | (a[i] == c[i]) & less_below
    let mut less = FALSE;
    for i in 0..w {
        let na = b.not(a[i])?;
        let here = b.and(na, c[i])?;
        let same = xnor(b, a[i], c[i])?;
        let below = b.and(same, less)?;
        less = b.or(here, below)?;
    }
    Ok(less)
}

/// Signed `a < c`; the shorter operand is sign-extended.
pub fn slt(b: &mut Bdd, a: &[Bd], c: &[Bd]) -> BResult {
    let w = a.len().max(c.len()).max(1);
    let (mut a, mut c) = (extend(a, w, true), extend(c, w, true));
    // Flipping the sign bits turns signed order into unsigned order.
    a[w - 1] = b.not(a[w - 1])?;
    c[w - 1] = b.not(c[w - 1])?;
    ult(b, &a, &c)
}

/// `table[index]` (both little-endian); positions past the table give `fill`.
pub fn dynamic_select(b: &mut Bdd, table: &[Bd], index: &[Bd], fill: Bd) -> BResult {
    let Some((&low_bit, rest)) = index.split_first() else {
        return Ok(table.first().copied().unwrap_or(fill));
    };
    if table.is_empty() {
        return Ok(fill);
    }
    // Mux on the lowest index bit between the even and the odd entries.
    let evens: Vec<Bd> = table.iter().step_by(2).copied().collect();
    let odds: Vec<Bd> = table.iter().skip(1).step_by(2).copied().collect();
    let even = dynamic_select(b, &evens, rest, fill)?;
    let odd = dynamic_select(b, &odds, rest, fill)?;
    b.ite(low_bit, odd, even)
}

/// Bit `k` of `data >> amount`; positions shifted in are `fill`.
pub fn shr_bit(b: &mut Bdd, data: &[Bd], amount: &[Bd], k: usize, fill: Bd) -> BResult {
    dynamic_select(b, data.get(k..).unwrap_or(&[]), amount, fill)
}

/// Bit `k` of `data << amount`.
pub fn shl_bit(b: &mut Bdd, data: &[Bd], amount: &[Bd], k: usize) -> BResult {
    // (data << s)[k] = data[k - s] for s <= k, else 0.
    let reversed: Vec<Bd> = (0..=k)
        .map(|s| data.get(k - s).copied().unwrap_or(FALSE))
        .collect();
    dynamic_select(b, &reversed, amount, FALSE)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mgr(n: u32) -> (Bdd, Vec<Bd>) {
        let mut b = Bdd::new(1 << 22);
        let vars = (0..n)
            .map(|_| {
                let v = b.new_var();
                b.var(v).unwrap()
            })
            .collect();
        (b, vars)
    }

    /// Value of a little-endian vector when variable `v` has the value of bit `v` of `row`.
    fn value(b: &Bdd, bits: &[Bd], row: u32) -> u128 {
        bits.iter()
            .enumerate()
            .map(|(i, &f)| u128::from(b.eval(f, &|v| row >> v & 1 == 1)) << i)
            .sum()
    }

    fn holds(b: &Bdd, f: Bd, row: u32) -> bool {
        b.eval(f, &|v| row >> v & 1 == 1)
    }

    fn signed(x: u128, w: usize) -> i128 {
        let x = x as i128;
        if x >> (w - 1) & 1 == 1 { x - (1 << w) } else { x }
    }

    #[test]
    fn addition() {
        for (wa, wc) in [(1, 1), (4, 4), (4, 2), (3, 5)] {
            let (mut b, v) = mgr((wa + wc) as u32);
            let (a, c) = (&v[..wa], &v[wa..]);
            let sum = add(&mut b, a, c, FALSE).unwrap();
            assert_eq!(sum.len(), wa.max(wc) + 1);
            for row in 0..1u32 << (wa + wc) {
                assert_eq!(value(&b, &sum, row), value(&b, a, row) + value(&b, c, row));
            }
        }
    }

    #[test]
    fn addition_with_carry_in() {
        let (mut b, v) = mgr(5);
        let (a, c) = (&v[..2], &v[2..4]);
        let sum = add(&mut b, a, c, v[4]).unwrap();
        for row in 0..32u32 {
            let want = value(&b, a, row) + value(&b, c, row) + u128::from(row >> 4 & 1);
            assert_eq!(value(&b, &sum, row), want);
        }
    }

    #[test]
    fn subtraction_is_modular() {
        for (wa, wc) in [(4, 4), (4, 2), (2, 4)] {
            let (mut b, v) = mgr((wa + wc) as u32);
            let (a, c) = (&v[..wa], &v[wa..]);
            let diff = sub(&mut b, a, c).unwrap();
            let w = wa.max(wc) + 1;
            assert_eq!(diff.len(), w);
            for row in 0..1u32 << (wa + wc) {
                let want = (value(&b, a, row) + (1 << w) - value(&b, c, row)) & ((1 << w) - 1);
                assert_eq!(value(&b, &diff, row), want);
            }
        }
    }

    #[test]
    fn multiplication() {
        for (wa, wc) in [(2, 2), (4, 3), (5, 5)] {
            let (mut b, v) = mgr((wa + wc) as u32);
            let (a, c) = (&v[..wa], &v[wa..]);
            let p = mul(&mut b, a, c).unwrap();
            assert_eq!(p.len(), wa + wc);
            for row in 0..1u32 << (wa + wc) {
                assert_eq!(value(&b, &p, row), value(&b, a, row) * value(&b, c, row));
            }
        }
    }

    #[test]
    fn equality_and_unsigned_less_than() {
        for (wa, wc) in [(3, 3), (4, 2), (2, 4)] {
            let (mut b, v) = mgr((wa + wc) as u32);
            let (a, c) = (&v[..wa], &v[wa..]);
            let e = eq(&mut b, a, c).unwrap();
            let l = ult(&mut b, a, c).unwrap();
            for row in 0..1u32 << (wa + wc) {
                let (x, y) = (value(&b, a, row), value(&b, c, row));
                assert_eq!(holds(&b, e, row), x == y);
                assert_eq!(holds(&b, l, row), x < y);
            }
        }
    }

    #[test]
    fn signed_less_than() {
        for (wa, wc) in [(3, 3), (4, 2)] {
            let (mut b, v) = mgr((wa + wc) as u32);
            let (a, c) = (&v[..wa], &v[wa..]);
            let l = slt(&mut b, a, c).unwrap();
            for row in 0..1u32 << (wa + wc) {
                let (x, y) = (signed(value(&b, a, row), wa), signed(value(&b, c, row), wc));
                assert_eq!(holds(&b, l, row), x < y, "{x} < {y}");
            }
        }
    }

    #[test]
    fn dynamic_select_picks_a_bit_or_the_fill() {
        // Index bits first: that is the order that keeps the BDD small.
        let (mut b, v) = mgr(5);
        let (idx, data) = (&v[..2], &v[2..]);
        let zero_fill = dynamic_select(&mut b, data, idx, FALSE).unwrap();
        let one_fill = dynamic_select(&mut b, data, idx, TRUE).unwrap();
        for row in 0..32u32 {
            let i = value(&b, idx, row) as usize;
            let bit = data.get(i).map(|&d| holds(&b, d, row));
            assert_eq!(holds(&b, zero_fill, row), bit.unwrap_or(false));
            assert_eq!(holds(&b, one_fill, row), bit.unwrap_or(true));
        }
    }

    #[test]
    fn shift_bits_match_arithmetic() {
        let (mut b, v) = mgr(7);
        let (amt, data) = (&v[..3], &v[3..]);
        for k in 0..4 {
            let r = shr_bit(&mut b, data, amt, k, FALSE).unwrap();
            let l = shl_bit(&mut b, data, amt, k).unwrap();
            let ar = shr_bit(&mut b, data, amt, k, data[3]).unwrap();
            for row in 0..128u32 {
                let (x, s) = (value(&b, data, row), value(&b, amt, row));
                assert_eq!(holds(&b, r, row), (x >> s) >> k & 1 == 1, "shr");
                assert_eq!(holds(&b, l, row), (x << s) >> k & 1 == 1, "shl");
                assert_eq!(holds(&b, ar, row), (signed(x, 4) >> s) >> k & 1 == 1, "ashr");
            }
        }
    }

    #[test]
    fn barrel_shifter_is_small_when_the_amount_comes_first() {
        let (mut b, v) = mgr(20);
        let (amt, data) = (&v[..4], &v[4..]);
        let before = b.node_count();
        for k in 0..16 {
            shr_bit(&mut b, data, amt, k, FALSE).unwrap();
        }
        let used = b.node_count() - before;
        assert!(used < 2000, "barrel shifter used {used} nodes");
    }

    #[test]
    fn wide_comparator_and_adder_are_small_when_operands_interleave() {
        let (mut b, v) = mgr(64);
        // a[31], c[31], a[30], c[30], ... : MSB first, interleaved.
        let a: Vec<Bd> = (0..32).map(|i| v[2 * (31 - i)]).collect();
        let c: Vec<Bd> = (0..32).map(|i| v[2 * (31 - i) + 1]).collect();
        let before = b.node_count();
        ult(&mut b, &a, &c).unwrap();
        eq(&mut b, &a, &c).unwrap();
        add(&mut b, &a, &c, FALSE).unwrap();
        let used = b.node_count() - before;
        assert!(used < 20_000, "32-bit compare and add used {used} nodes");
    }
}

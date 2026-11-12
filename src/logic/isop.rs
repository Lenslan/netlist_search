//! Irredundant sum of products (the Minato-Morreale algorithm), used whenever
//! no bus-level structure is recognised.
//!
//! The search stops as soon as the cover is known to need more cubes than the
//! caller allows, so asking for the cover of a carry chain or a parity tree
//! costs little: the answer is simply "too many terms".

use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::bdd::{BResult, Bd, Bdd, Blowup, FALSE, TRUE};

/// A product term: `(variable, is_positive)`, sorted by variable.
pub type Cube = Vec<(u32, bool)>;

/// The function of one cube.
pub fn cube_bdd(b: &mut Bdd, cube: &Cube) -> BResult {
    let mut f = TRUE;
    // Bottom variable first keeps every intermediate result a single chain.
    for &(v, positive) in cube.iter().rev() {
        let lit = b.var(v)?;
        let lit = if positive { lit } else { b.not(lit)? };
        f = b.and(f, lit)?;
    }
    Ok(f)
}

/// The disjunction of a cover.
pub fn cover_bdd(b: &mut Bdd, cover: &[Cube]) -> BResult {
    let mut f = FALSE;
    for c in cover {
        let g = cube_bdd(b, c)?;
        f = b.or(f, g)?;
    }
    Ok(f)
}

/// An irredundant cover of `f` by prime implicants; `Ok(None)` if it needs
/// more than `max_cubes` cubes.
pub fn isop(b: &mut Bdd, f: Bd, max_cubes: usize) -> Result<Option<Vec<Cube>>, Blowup> {
    let mut s = Isopper {
        b,
        max: max_cubes,
        memo: FxHashMap::default(),
    };
    match s.go(f, f) {
        Ok((cubes, cover)) => {
            // The cover of the interval [f, f] is f itself; never hand out
            // anything else.
            Ok((cover == f).then(|| cubes.to_vec()))
        }
        Err(Stop::TooMany) => Ok(None),
        Err(Stop::Blowup) => Err(Blowup),
    }
}

enum Stop {
    TooMany,
    Blowup,
}

impl From<Blowup> for Stop {
    fn from(_: Blowup) -> Self {
        Stop::Blowup
    }
}

type Cover = (Rc<Vec<Cube>>, Bd);

struct Isopper<'a> {
    b: &'a mut Bdd,
    max: usize,
    memo: FxHashMap<(Bd, Bd), Cover>,
}

impl Isopper<'_> {
    /// A cover `c` with `lower <= c <= upper`, as cubes and as a BDD.
    fn go(&mut self, lower: Bd, upper: Bd) -> Result<Cover, Stop> {
        if lower == FALSE {
            return Ok((Rc::new(Vec::new()), FALSE));
        }
        if upper == TRUE {
            return Ok((Rc::new(vec![Cube::new()]), TRUE));
        }
        if let Some(r) = self.memo.get(&(lower, upper)) {
            return Ok(r.clone());
        }
        // `lower` implies `upper`, so neither is a constant here.
        let v = match (self.b.top_var(lower), self.b.top_var(upper)) {
            (Some(a), Some(c)) => a.min(c),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => unreachable!("constants are handled above"),
        };
        let (l0, l1) = self.b.cofactors(lower, v);
        let (u0, u1) = self.b.cofactors(upper, v);

        // Cubes that need the literal !v: they cover what v = 1 must not.
        let nu1 = self.b.not(u1)?;
        let need0 = self.b.and(l0, nu1)?;
        let (c0, g0) = self.go(need0, u0)?;
        // Cubes that need the literal v.
        let nu0 = self.b.not(u0)?;
        let need1 = self.b.and(l1, nu0)?;
        let (c1, g1) = self.go(need1, u1)?;
        // What is left is covered by cubes that do not mention v.
        let ng0 = self.b.not(g0)?;
        let ng1 = self.b.not(g1)?;
        let rest0 = self.b.and(l0, ng0)?;
        let rest1 = self.b.and(l1, ng1)?;
        let rest = self.b.or(rest0, rest1)?;
        let both = self.b.and(u0, u1)?;
        let (cs, gs) = self.go(rest, both)?;

        if c0.len() + c1.len() + cs.len() > self.max {
            return Err(Stop::TooMany);
        }
        let mut cubes = Vec::with_capacity(c0.len() + c1.len() + cs.len());
        for (side, positive) in [(&c0, false), (&c1, true)] {
            for c in side.iter() {
                let mut cube = Vec::with_capacity(c.len() + 1);
                cube.push((v, positive));
                cube.extend_from_slice(c);
                cubes.push(cube);
            }
        }
        cubes.extend(cs.iter().cloned());

        let x = self.b.var(v)?;
        let with_v = self.b.ite(x, g1, g0)?;
        let cover = self.b.or(with_v, gs)?;
        let r = (Rc::new(cubes), cover);
        self.memo.insert((lower, upper), r.clone());
        Ok(r)
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

    fn cube_text(cube: &Cube) -> String {
        if cube.is_empty() {
            return "1".into();
        }
        cube.iter()
            .map(|&(x, p)| format!("{}{x}", if p { "" } else { "!" }))
            .collect::<Vec<_>>()
            .join("&")
    }

    fn cover_text(cover: &[Cube]) -> Vec<String> {
        let mut v: Vec<String> = cover.iter().map(cube_text).collect();
        v.sort();
        v
    }

    #[test]
    fn single_cubes() {
        let (mut b, v) = mgr(2);
        let f = b.and(v[0], v[1]).unwrap();
        assert_eq!(cover_text(&isop(&mut b, f, 8).unwrap().unwrap()), ["0&1"]);
        assert_eq!(cover_text(&isop(&mut b, TRUE, 8).unwrap().unwrap()), ["1"]);
        assert_eq!(isop(&mut b, FALSE, 8).unwrap().unwrap().len(), 0);
        assert_eq!(cover_text(&isop(&mut b, v[0], 8).unwrap().unwrap()), ["0"]);
    }

    #[test]
    fn an_or_is_one_literal_per_cube() {
        let (mut b, v) = mgr(3);
        let f = b.or(v[0], v[2]).unwrap();
        assert_eq!(cover_text(&isop(&mut b, f, 8).unwrap().unwrap()), ["0", "2"]);
    }

    #[test]
    fn a_mux_keeps_its_two_product_terms() {
        let (mut b, v) = mgr(3);
        let f = b.ite(v[0], v[1], v[2]).unwrap();
        assert_eq!(
            cover_text(&isop(&mut b, f, 8).unwrap().unwrap()),
            ["!0&2", "0&1"]
        );
    }

    #[test]
    fn a_bus_equality_is_one_cube_with_a_literal_per_bit() {
        let (mut b, v) = mgr(4);
        let mut f = TRUE;
        for (i, &x) in v.iter().enumerate() {
            let bit = (5u32 >> (3 - i)) & 1 == 1;
            let lit = if bit { x } else { b.not(x).unwrap() };
            f = b.and(f, lit).unwrap();
        }
        let cover = isop(&mut b, f, 8).unwrap().unwrap();
        assert_eq!(cover_text(&cover), ["!0&1&!2&3"]);
    }

    #[test]
    fn and_or_of_pairs_needs_one_cube_per_pair() {
        // ab | cd | ef | gh: a naive expansion doubles at every pair.
        let (mut b, v) = mgr(8);
        let mut f = FALSE;
        for pair in v.chunks(2) {
            let t = b.and(pair[0], pair[1]).unwrap();
            f = b.or(f, t).unwrap();
        }
        let cover = isop(&mut b, f, 8).unwrap().unwrap();
        assert_eq!(cover_text(&cover), ["0&1", "2&3", "4&5", "6&7"]);
    }

    fn random_function(b: &mut Bdd, v: &[Bd], rnd: &mut impl FnMut() -> u64) -> Bd {
        let mut f = FALSE;
        for _ in 0..(rnd() % 8) {
            let mut cube = TRUE;
            for &x in v {
                let nx = b.not(x).unwrap();
                cube = match rnd() % 4 {
                    0 => b.and(cube, x).unwrap(),
                    1 => b.and(cube, nx).unwrap(),
                    _ => cube,
                };
            }
            f = b.or(f, cube).unwrap();
        }
        f
    }

    #[test]
    fn covers_of_random_functions_are_exact_prime_and_irredundant() {
        let mut seed = 0x243f6a8885a308d3u64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let (mut b, v) = mgr(6);
            let f = random_function(&mut b, &v, &mut rnd);
            let cover = isop(&mut b, f, 64).unwrap().expect("within the limit");
            let text = cover_text(&cover).join(" | ");
            assert_eq!(cover_bdd(&mut b, &cover).unwrap(), f, "exact: {text}");
            let nf = b.not(f).unwrap();
            for (i, cube) in cover.iter().enumerate() {
                assert!(cube.windows(2).all(|w| w[0].0 < w[1].0), "sorted: {text}");
                // Prime: dropping any literal leaves the function.
                for skip in 0..cube.len() {
                    let mut wider = cube.clone();
                    wider.remove(skip);
                    let w = cube_bdd(&mut b, &wider).unwrap();
                    assert_ne!(b.and(w, nf).unwrap(), FALSE, "prime: {text}");
                }
                // Irredundant: the other cubes do not cover this one.
                let others: Vec<Cube> = cover
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, c)| c.clone())
                    .collect();
                assert_ne!(cover_bdd(&mut b, &others).unwrap(), f, "irredundant: {text}");
            }
        }
    }

    #[test]
    fn a_cover_over_the_limit_is_reported_as_none() {
        // Parity of 6 variables has 32 product terms.
        let (mut b, v) = mgr(6);
        let mut f = FALSE;
        for &x in &v {
            f = b.xor(f, x).unwrap();
        }
        assert!(isop(&mut b, f, 8).unwrap().is_none());
        assert_eq!(isop(&mut b, f, 64).unwrap().unwrap().len(), 32);
    }

    #[test]
    fn a_huge_cover_is_refused_quickly() {
        // The carry of a 24-bit adder (operands interleaved) has millions of
        // product terms. Refusing must not take time proportional to that.
        let (mut b, v) = mgr(48);
        let mut carry = FALSE;
        for pair in v.chunks(2).rev() {
            let g = b.and(pair[0], pair[1]).unwrap();
            let p = b.xor(pair[0], pair[1]).unwrap();
            let pc = b.and(p, carry).unwrap();
            carry = b.or(g, pc).unwrap();
        }
        let before = b.ops();
        assert!(isop(&mut b, carry, 64).unwrap().is_none());
        let cost = b.ops() - before;
        assert!(cost < 200_000, "refusing cost {cost} steps");
    }
}

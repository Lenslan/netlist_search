//! Irredundant sum of products (Minato-Morreale), used whenever no bus-level
//! structure is recognised. The result is always verified against the input
//! function before it is returned.

use rustc_hash::FxHashMap;

use super::bdd::{BResult, Bd, Bdd, Blowup, FALSE, TRUE};

/// A product term: `(variable, is_positive)`, sorted by variable.
pub type Cube = Vec<(u32, bool)>;

/// The function of one cube.
pub fn cube_bdd(b: &mut Bdd, cube: &Cube) -> BResult {
    let mut f = TRUE;
    for &(v, positive) in cube {
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

/// A cover of `f`: `Ok(None)` if it would need more than `max_cubes` cubes.
pub fn isop(b: &mut Bdd, f: Bd, max_cubes: usize) -> Result<Option<Vec<Cube>>, Blowup> {
    let mut s = Isopper {
        b,
        max: max_cubes,
        over: false,
        cube_cache: FxHashMap::default(),
    };
    let (mut cover, _built) = s.go(f)?;
    if s.over || cover.len() > max_cubes {
        return Ok(None);
    }
    // Grow each cube as far as it stays an implicant, then drop cubes the
    // others already cover: this turns `!0&2 | 0` into `2 | 0`.
    s.expand(f, &mut cover)?;
    s.prune(&mut cover)?;
    // Never hand out a cover that is not exactly the function.
    let check = cover_bdd(s.b, &cover)?;
    if check != f {
        return Ok(None);
    }
    Ok(Some(cover))
}

struct Isopper<'a> {
    b: &'a mut Bdd,
    max: usize,
    over: bool,
    cube_cache: FxHashMap<Cube, Bd>,
}

impl Isopper<'_> {
    fn cube(&mut self, cube: &Cube) -> BResult {
        if let Some(&f) = self.cube_cache.get(cube) {
            return Ok(f);
        }
        let f = cube_bdd(self.b, cube)?;
        if self.cube_cache.len() < 100_000 {
            self.cube_cache.insert(cube.clone(), f);
        }
        Ok(f)
    }

    /// Returns the cover of `f` and its BDD.
    fn go(&mut self, f: Bd) -> Result<(Vec<Cube>, Bd), Blowup> {
        if f == FALSE {
            return Ok((Vec::new(), FALSE));
        }
        if f == TRUE {
            return Ok((vec![Cube::new()], TRUE));
        }
        let v = self.b.top_var(f).expect("non terminal");
        let (f0, f1) = self.b.cofactors(f, v);
        let (c0, d0) = self.go(f0)?;
        let (c1, _d1) = self.go(f1)?;
        // Literals: the variable is the top one, so it goes first.
        let mut side0: Vec<Cube> = c0
            .into_iter()
            .map(|mut c| {
                c.insert(0, (v, false));
                c
            })
            .collect();
        let side1: Vec<Cube> = c1
            .into_iter()
            .map(|mut c| {
                c.insert(0, (v, true));
                c
            })
            .collect();
        if side0.len() + side1.len() > self.max {
            self.over = true;
        }
        // Start from the ¬v side, then add only the cubes of the v side that
        // are not already covered.
        let vlit = self.b.var(v)?;
        let nvlit = self.b.not(vlit)?;
        let mut cover = self.b.and(d0, nvlit)?;
        let mut kept = std::mem::take(&mut side0);
        for c in &side1 {
            let cb = self.cube(c)?;
            let ncover = self.b.not(cover)?;
            let uncovered = self.b.and(cb, ncover)?;
            if uncovered != FALSE {
                cover = self.b.or(cover, cb)?;
                kept.push(c.clone());
            }
        }
        Ok((kept, cover))
    }

    /// Drop literals that are not needed, keeping each cube an implicant of `f`.
    fn expand(&mut self, f: Bd, cover: &mut [Cube]) -> Result<(), Blowup> {
        let nf = self.b.not(f)?;
        for _ in 0..3 {
            let mut changed = false;
            for cube in cover.iter_mut() {
                if cube.len() < 2 {
                    continue;
                }
                let mut i = 0;
                while i < cube.len() {
                    let mut trial = cube.clone();
                    trial.remove(i);
                    let tb = self.cube(&trial)?;
                    let outside = self.b.and(tb, nf)?;
                    if outside == FALSE {
                        *cube = trial;
                        changed = true;
                    } else {
                        i += 1;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Ok(())
    }

    /// Drop cubes that the other cubes already cover.
    fn prune(&mut self, cover: &mut Vec<Cube>) -> Result<(), Blowup> {
        let mut i = 0;
        while i < cover.len() && cover.len() > 1 {
            let cb = self.cube(&cover[i])?;
            let mut rest = FALSE;
            for (j, c) in cover.iter().enumerate() {
                if j != i {
                    let cbj = self.cube(c)?;
                    rest = self.b.or(rest, cbj)?;
                }
            }
            let nrest = self.b.not(rest)?;
            let uncovered = self.b.and(cb, nrest)?;
            if uncovered == FALSE {
                cover.remove(i);
            } else {
                i += 1;
            }
        }
        Ok(())
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
        let mut v: Vec<String> = cover.iter().map(|c| cube_text(c)).collect();
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
    fn a_bus_equality_stays_one_cube_of_one_literal_per_bit() {
        let (mut b, v) = mgr(4);
        // v[0] is the MSB in this hand-made encoding: 5 = 0101
        let mut f = TRUE;
        for (i, &x) in v.iter().enumerate() {
            let bit = (5u32 >> (3 - i)) & 1 == 1;
            let lit = if bit { x } else { b.not(x).unwrap() };
            f = b.and(f, lit).unwrap();
        }
        let cover = isop(&mut b, f, 8).unwrap().unwrap();
        assert_eq!(cover.len(), 1);
        assert_eq!(cover[0].len(), 4);
    }

    #[test]
    fn covers_are_exact_for_random_functions() {
        let mut seed = 0x243f6a8885a308d3u64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..100 {
            let (mut b, v) = mgr(5);
            let mut f = FALSE;
            for _ in 0..(rnd() % 8) {
                let mut cube = TRUE;
                for &x in &v {
                    let nx = b.not(x).unwrap();
                    cube = match rnd() % 4 {
                        0 => b.and(cube, x).unwrap(),
                        1 => b.and(cube, nx).unwrap(),
                        _ => cube,
                    };
                }
                f = b.or(f, cube).unwrap();
            }
            match isop(&mut b, f, 64).unwrap() {
                Some(cover) => {
                    let rebuilt = cover_bdd(&mut b, &cover).unwrap();
                    assert_eq!(rebuilt, f, "cover {} is not exact", cover_text(&cover).join(" | "));
                    for c in &cover {
                        assert!(c.windows(2).all(|w| w[0].0 < w[1].0), "cube sorted");
                    }
                    assert!(cover.iter().all(|c| !c.is_empty() || cover.len() == 1));
                }
                None => panic!("cover exceeded the limit"),
            }
        }
    }

    #[test]
    fn a_huge_cover_is_reported_as_none() {
        // Parity of 6 variables has 32 product terms.
        let (mut b, v) = mgr(6);
        let mut f = FALSE;
        for &x in &v {
            let nx = b.not(x).unwrap();
            let nf = b.not(f).unwrap();
            let a = b.and(f, nx).unwrap();
            let c = b.and(nf, x).unwrap();
            f = b.or(a, c).unwrap();
        }
        assert!(isop(&mut b, f, 8).unwrap().is_none());
        assert!(isop(&mut b, f, 64).unwrap().is_some());
    }
}

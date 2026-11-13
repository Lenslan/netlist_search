use super::bdd::{Bd, Bdd, FALSE, TRUE};
use super::bus::{VarInfo, order_vars};
use super::expr::Radix;
use super::lift::{LiftOpts, Lifter};
use super::words;

/// A BDD manager with one variable per name, ordered as the analysis orders them.
struct Fx {
    b: Bdd,
    vars: Vec<VarInfo>,
}

impl Fx {
    fn new(spec: &[&str]) -> Fx {
        // "cnt[4]" declares a 4-bit bus cnt[3:0]; "a[7:4]" a slice; "sel" a scalar.
        let mut names = Vec::new();
        for s in spec {
            match s.find('[') {
                Some(i) => {
                    let inner = &s[i + 1..s.len() - 1];
                    let (hi, lo) = match inner.split_once(':') {
                        Some((h, l)) => (h.parse::<i64>().unwrap(), l.parse::<i64>().unwrap()),
                        None => (inner.parse::<i64>().unwrap() - 1, 0),
                    };
                    for k in lo..=hi {
                        names.push(format!("{}[{k}]", &s[..i]));
                    }
                }
                None => names.push(s.to_string()),
            }
        }
        let (vars, _) = order_vars(&names);
        let mut b = Bdd::new(1 << 22);
        for _ in 0..vars.len() {
            b.new_var();
        }
        Fx { b, vars }
    }

    fn v(&mut self, name: &str) -> Bd {
        let level = self
            .vars
            .iter()
            .position(|x| x.name == name)
            .unwrap_or_else(|| panic!("no variable {name}"));
        self.b.var(level as u32).unwrap()
    }

    /// Bits `base[lo..=hi]`, least significant first.
    fn bus(&mut self, base: &str, hi: i64, lo: i64) -> Vec<Bd> {
        (lo..=hi).map(|k| self.v(&format!("{base}[{k}]"))).collect()
    }

    fn konst(&self, value: u128, width: usize) -> Vec<Bd> {
        (0..width)
            .map(|i| if value >> i & 1 == 1 { TRUE } else { FALSE })
            .collect()
    }

    fn lift_with(&mut self, f: Bd, opts: LiftOpts) -> String {
        let mut l = Lifter::new(&mut self.b, &self.vars, opts);
        let e = l.lift(f).expect("an expression is found");
        assert!(!l.take_mismatch(), "a lifted expression failed its proof");
        let text = e.render(&self.vars, Radix::Dec);
        let back = e.to_bdd(&mut self.b).unwrap();
        assert_eq!(back, f, "'{text}' is not the function it was lifted from");
        text
    }

    fn lift(&mut self, f: Bd) -> String {
        self.lift_with(f, LiftOpts::default())
    }

    fn not(&mut self, f: Bd) -> Bd {
        self.b.not(f).unwrap()
    }
    fn and(&mut self, f: Bd, g: Bd) -> Bd {
        self.b.and(f, g).unwrap()
    }
    fn or(&mut self, f: Bd, g: Bd) -> Bd {
        self.b.or(f, g).unwrap()
    }
    fn xor(&mut self, f: Bd, g: Bd) -> Bd {
        self.b.xor(f, g).unwrap()
    }
    fn ite(&mut self, c: Bd, t: Bd, e: Bd) -> Bd {
        self.b.ite(c, t, e).unwrap()
    }
    fn eq_const(&mut self, bus: &[Bd], value: u128) -> Bd {
        let k = self.konst(value, bus.len());
        words::eq(&mut self.b, bus, &k).unwrap()
    }
    fn lt_const(&mut self, bus: &[Bd], value: u128) -> Bd {
        let k = self.konst(value, bus.len() + 1);
        words::ult(&mut self.b, bus, &k).unwrap()
    }
}

// ---- the two lines of grammar.example ---------------------------------------

#[test]
fn grammar_example_bus_equals_constant() {
    let mut x = Fx::new(&["cnt[4]"]);
    // cnt[0] & (!cnt[1]) & cnt[2] & (!cnt[3])
    let (c0, c1, c2, c3) = (x.v("cnt[0]"), x.v("cnt[1]"), x.v("cnt[2]"), x.v("cnt[3]"));
    let n1 = x.not(c1);
    let n3 = x.not(c3);
    let mut f = x.and(c0, n1);
    f = x.and(f, c2);
    f = x.and(f, n3);
    assert_eq!(x.lift(f), "cnt[3:0] == 5");
}

#[test]
fn grammar_example_mux() {
    let mut x = Fx::new(&["sel", "a", "b"]);
    // sel & a | !sel & b
    let (sel, a, b) = (x.v("sel"), x.v("a"), x.v("b"));
    let t = x.and(sel, a);
    let ns = x.not(sel);
    let e = x.and(ns, b);
    let f = x.or(t, e);
    assert_eq!(x.lift(f), "sel ? a : b");
}

// ---- basics -----------------------------------------------------------------

#[test]
fn constants_and_literals() {
    let mut x = Fx::new(&["a"]);
    assert_eq!(x.lift(TRUE), "1'b1");
    assert_eq!(x.lift(FALSE), "1'b0");
    let a = x.v("a");
    assert_eq!(x.lift(a), "a");
    let na = x.not(a);
    assert_eq!(x.lift(na), "!a");
}

#[test]
fn plain_and_or_xor() {
    let mut x = Fx::new(&["a", "b", "c"]);
    let (a, b, c) = (x.v("a"), x.v("b"), x.v("c"));
    let ab = x.and(a, b);
    let f = x.and(ab, c);
    assert_eq!(x.lift(f), "a & b & c");
    let nb = x.not(b);
    let g = x.or(a, nb);
    assert_eq!(x.lift(g), "a | !b");
    let h = x.xor(ab, c);
    assert_eq!(x.lift(h), "c ^ a & b");
    let p = x.xor(a, b);
    let p = x.xor(p, c);
    assert_eq!(x.lift(p), "a ^ b ^ c");
    let np = x.not(p);
    assert_eq!(x.lift(np), "!(a ^ b ^ c)");
}

#[test]
fn condition_on_a_state_register() {
    let mut x = Fx::new(&["state[4]", "mode"]);
    let st = x.bus("state", 3, 0);
    let is5 = x.eq_const(&st, 5);
    let is9 = x.eq_const(&st, 9);
    let either = x.or(is5, is9);
    assert_eq!(x.lift(either), "state[3:0] inside {5, 9}");
    let mode = x.v("mode");
    let f = x.and(mode, either);
    assert_eq!(x.lift(f), "mode & (state[3:0] inside {5, 9})");
}

#[test]
fn not_equal() {
    let mut x = Fx::new(&["cnt[2]"]);
    let c = x.bus("cnt", 1, 0);
    let e = x.eq_const(&c, 3);
    let f = x.not(e);
    assert_eq!(x.lift(f), "cnt[1:0] != 3");
}

#[test]
fn scattered_bits_of_a_bus_stay_literals() {
    let mut x = Fx::new(&["cnt[4]"]);
    let (c3, c1) = (x.v("cnt[3]"), x.v("cnt[1]"));
    let n1 = x.not(c1);
    let f = x.and(c3, n1);
    assert_eq!(x.lift(f), "cnt[3] & !cnt[1]");
}

// ---- comparisons ------------------------------------------------------------

#[test]
fn bus_against_constant() {
    let mut x = Fx::new(&["cnt[4]"]);
    let c = x.bus("cnt", 3, 0);
    let lt10 = x.lt_const(&c, 10);
    assert_eq!(x.lift(lt10), "cnt[3:0] < 10");
    let lt6 = x.lt_const(&c, 6);
    let ge6 = x.not(lt6);
    assert_eq!(x.lift(ge6), "cnt[3:0] >= 6");
}

#[test]
fn range_and_set() {
    let mut x = Fx::new(&["cnt[8]"]);
    let c = x.bus("cnt", 7, 0);
    let lt200 = x.lt_const(&c, 200);
    let lt16 = x.lt_const(&c, 16);
    let ge16 = x.not(lt16);
    let f = x.and(ge16, lt200);
    assert_eq!(x.lift(f), "cnt[7:0] >= 16 & cnt[7:0] < 200");
    let nf = x.not(f);
    assert_eq!(x.lift(nf), "cnt[7:0] < 16 | cnt[7:0] > 199");

    let mut x = Fx::new(&["cnt[4]"]);
    let c = x.bus("cnt", 3, 0);
    let mut f = FALSE;
    for v in [1, 4, 7] {
        let e = x.eq_const(&c, v);
        f = x.or(f, e);
    }
    assert_eq!(x.lift(f), "cnt[3:0] inside {1, 4, 7}");
    let nf = x.not(f);
    assert_eq!(x.lift(nf), "!(cnt[3:0] inside {1, 4, 7})");
}

#[test]
fn bus_against_bus() {
    let mut x = Fx::new(&["a[4]", "b[4]"]);
    let (a, b) = (x.bus("a", 3, 0), x.bus("b", 3, 0));
    let lt = words::ult(&mut x.b, &a, &b).unwrap();
    assert_eq!(x.lift(lt), "a[3:0] < b[3:0]");
    let ge = x.not(lt);
    assert_eq!(x.lift(ge), "a[3:0] >= b[3:0]");
    let gt = words::ult(&mut x.b, &b, &a).unwrap();
    assert_eq!(x.lift(gt), "a[3:0] > b[3:0]");
    let le = x.not(gt);
    assert_eq!(x.lift(le), "a[3:0] <= b[3:0]");
    let eq = words::eq(&mut x.b, &a, &b).unwrap();
    assert_eq!(x.lift(eq), "a[3:0] == b[3:0]");
    let ne = x.not(eq);
    assert_eq!(x.lift(ne), "a[3:0] != b[3:0]");
}

#[test]
fn signed_comparison() {
    let mut x = Fx::new(&["a[4]", "b[4]"]);
    let (a, b) = (x.bus("a", 3, 0), x.bus("b", 3, 0));
    let lt = words::slt(&mut x.b, &a, &b).unwrap();
    assert_eq!(x.lift(lt), "$signed(a[3:0]) < $signed(b[3:0])");
}

#[test]
fn comparison_under_an_enable() {
    let mut x = Fx::new(&["cnt[4]", "en"]);
    let c = x.bus("cnt", 3, 0);
    let lt = x.lt_const(&c, 10);
    let en = x.v("en");
    let f = x.and(en, lt);
    assert_eq!(x.lift(f), "en & cnt[3:0] < 10");
}

#[test]
fn two_comparisons_combined() {
    let mut x = Fx::new(&["a[4]", "b[4]", "st[3]"]);
    let (a, b, st) = (x.bus("a", 3, 0), x.bus("b", 3, 0), x.bus("st", 2, 0));
    let lt = words::ult(&mut x.b, &a, &b).unwrap();
    let is2 = x.eq_const(&st, 2);
    let f = x.or(lt, is2);
    assert_eq!(x.lift(f), "st[2:0] == 2 | a[3:0] < b[3:0]");
}

// ---- index, shift, multiplexer ----------------------------------------------

#[test]
fn bitmap_indexed_by_a_bus() {
    let mut x = Fx::new(&["bitmap[16]", "idx[4]"]);
    let (bm, idx) = (x.bus("bitmap", 15, 0), x.bus("idx", 3, 0));
    let f = words::dynamic_select(&mut x.b, &bm, &idx, FALSE).unwrap();
    assert_eq!(x.lift(f), "bitmap[idx[3:0]]");
}

#[test]
fn bitmap_shorter_than_the_index_range() {
    let mut x = Fx::new(&["bitmap[6]", "idx[3]"]);
    let (bm, idx) = (x.bus("bitmap", 5, 0), x.bus("idx", 2, 0));
    let f = words::dynamic_select(&mut x.b, &bm, &idx, FALSE).unwrap();
    assert_eq!(x.lift(f), "bitmap[idx[2:0]]");
}

#[test]
fn variable_shifts() {
    let mut x = Fx::new(&["d[8]", "s[3]"]);
    let (d, s) = (x.bus("d", 7, 0), x.bus("s", 2, 0));
    let r = words::shr_bit(&mut x.b, &d, &s, 2, FALSE).unwrap();
    assert_eq!(x.lift(r), "(d[7:0] >> s[2:0])[2]");
    let l = words::shl_bit(&mut x.b, &d, &s, 5).unwrap();
    assert_eq!(x.lift(l), "(d[5:0] << s[2:0])[5]");
    let ar = words::shr_bit(&mut x.b, &d, &s, 2, d[7]).unwrap();
    assert_eq!(x.lift(ar), "($signed(d[7:0]) >>> s[2:0])[2]");
}

#[test]
fn multiplexer_of_unrelated_signals() {
    let mut x = Fx::new(&["s[2]", "a", "b", "c", "d"]);
    let s = x.bus("s", 1, 0);
    let table = [x.v("a"), x.v("b"), x.v("c"), x.v("d")];
    let f = words::dynamic_select(&mut x.b, &table, &s, FALSE).unwrap();
    assert_eq!(x.lift(f), "case (s[1:0]) {0: a, 1: b, 2: c, 3: d}");
}

#[test]
fn select_wider_than_the_limit_is_not_recognised_but_still_correct() {
    let mut x = Fx::new(&["bitmap[8]", "idx[3]"]);
    let (bm, idx) = (x.bus("bitmap", 7, 0), x.bus("idx", 2, 0));
    let f = words::dynamic_select(&mut x.b, &bm, &idx, FALSE).unwrap();
    let opts = LiftOpts {
        sel_width: 1,
        ..LiftOpts::default()
    };
    let text = x.lift_with(f, opts);
    assert!(!text.contains("bitmap[idx"), "{text}");
}

// ---- arithmetic -------------------------------------------------------------

#[test]
fn increment_and_decrement() {
    let mut x = Fx::new(&["cnt[4]"]);
    let c = x.bus("cnt", 3, 0);
    let one = x.konst(1, 4);
    let inc = words::add(&mut x.b, &c, &one, FALSE).unwrap();
    assert_eq!(x.lift(inc[3]), "(cnt[3:0] + 1)[3]");
    // Bit 2 only depends on cnt[2:0]; on so narrow a bus the set reads better.
    assert_eq!(x.lift(inc[2]), "cnt[2:0] inside {3, 4, 5, 6}");
    let dec = words::sub(&mut x.b, &c, &one).unwrap();
    assert_eq!(x.lift(dec[3]), "(cnt[3:0] - 1)[3]");
    assert_eq!(x.lift(dec[2]), "cnt[2:0] inside {0, 5, 6, 7}");
}

#[test]
fn adding_a_constant() {
    let mut x = Fx::new(&["cnt[8]"]);
    let c = x.bus("cnt", 7, 0);
    let k = x.konst(37, 8);
    let sum = words::add(&mut x.b, &c, &k, FALSE).unwrap();
    // The top bit of `cnt + 37` is also a range test; by default the range is shown.
    assert_eq!(x.lift(sum[7]), "cnt[7:0] >= 91 & cnt[7:0] < 219");
    let arith = LiftOpts {
        prefer_arith: true,
        ..LiftOpts::default()
    };
    assert_eq!(x.lift_with(sum[7], arith.clone()), "(cnt[7:0] + 37)[7]");
    assert_eq!(x.lift_with(sum[6], arith), "(cnt[6:0] + 37)[6]");
}

#[test]
fn sum_difference_and_carry_of_two_buses() {
    let mut x = Fx::new(&["a[4]", "b[4]", "cin"]);
    let (a, b) = (x.bus("a", 3, 0), x.bus("b", 3, 0));
    let sum = words::add(&mut x.b, &a, &b, FALSE).unwrap();
    assert_eq!(x.lift(sum[3]), "(a[3:0] + b[3:0])[3]");
    assert_eq!(x.lift(sum[2]), "(a[2:0] + b[2:0])[2]");
    assert_eq!(x.lift(sum[4]), "(a[3:0] + b[3:0])[4]");
    let diff = words::sub(&mut x.b, &a, &b).unwrap();
    assert_eq!(x.lift(diff[3]), "(a[3:0] - b[3:0])[3]");
    let rdiff = words::sub(&mut x.b, &b, &a).unwrap();
    assert_eq!(x.lift(rdiff[3]), "(b[3:0] - a[3:0])[3]");
    let cin = x.v("cin");
    let sum = words::add(&mut x.b, &a, &b, cin).unwrap();
    assert_eq!(x.lift(sum[2]), "(a[2:0] + b[2:0] + cin)[2]");
}

#[test]
fn sum_of_two_slices() {
    let mut x = Fx::new(&["a[7:4]", "b[4]"]);
    let (a, b) = (x.bus("a", 7, 4), x.bus("b", 3, 0));
    let sum = words::add(&mut x.b, &a, &b, FALSE).unwrap();
    assert_eq!(x.lift(sum[2]), "(a[6:4] + b[2:0])[2]");
}

#[test]
fn counter_next_state_with_reset_and_enable() {
    let mut x = Fx::new(&["cnt[4]", "rst", "en"]);
    let c = x.bus("cnt", 3, 0);
    let one = x.konst(1, 4);
    let inc = words::add(&mut x.b, &c, &one, FALSE).unwrap();
    let (rst, en) = (x.v("rst"), x.v("en"));
    let next = x.ite(en, inc[3], c[3]);
    let nrst = x.not(rst);
    let f = x.and(nrst, next);
    assert_eq!(x.lift(f), "!rst & (en ? (cnt[3:0] + 1)[3] : cnt[3])");
}

#[test]
fn small_products() {
    let mut x = Fx::new(&["a[4]", "b[4]"]);
    let (a, b) = (x.bus("a", 3, 0), x.bus("b", 3, 0));
    let p = words::mul(&mut x.b, &a, &b).unwrap();
    assert_eq!(x.lift(p[5]), "(a[3:0] * b[3:0])[5]");
    assert_eq!(x.lift(p[7]), "(a[3:0] * b[3:0])[7]");
    let k = x.konst(5, 3);
    let p = words::mul(&mut x.b, &a, &k).unwrap();
    let arith = LiftOpts {
        prefer_arith: true,
        ..LiftOpts::default()
    };
    assert_eq!(x.lift_with(p[4], arith), "(a[3:0] * 5)[4]");
}

// ---- soundness --------------------------------------------------------------

#[test]
fn random_functions_always_lift_to_an_equal_expression() {
    let mut seed = 0x853c49e6748fea9bu64;
    let mut rnd = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for round in 0..300 {
        let mut x = Fx::new(&["p[3]", "q[3]", "s", "t"]);
        let leaves: Vec<Bd> = ["p[0]", "p[1]", "p[2]", "q[0]", "q[1]", "q[2]", "s", "t"]
            .iter()
            .map(|n| x.v(n))
            .collect();
        let mut stack: Vec<Bd> = Vec::new();
        for _ in 0..(6 + rnd() % 30) {
            let r = rnd();
            match r % 6 {
                0 | 1 | 2 => stack.push(leaves[(r >> 8) as usize % leaves.len()]),
                3 if !stack.is_empty() => {
                    let f = stack.pop().unwrap();
                    stack.push(x.not(f));
                }
                _ if stack.len() >= 2 => {
                    let (f, g) = (stack.pop().unwrap(), stack.pop().unwrap());
                    stack.push(match (r >> 16) % 3 {
                        0 => x.and(f, g),
                        1 => x.or(f, g),
                        _ => x.xor(f, g),
                    });
                }
                _ => {}
            }
        }
        for f in stack {
            // `lift` itself asserts that the expression equals `f`.
            let text = x.lift(f);
            assert!(!text.is_empty(), "round {round}");
        }
    }
}

#[test]
fn a_function_over_too_many_inputs_is_declined() {
    let names: Vec<String> = (0..12).map(|i| format!("x{i}")).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut x = Fx::new(&refs);
    let mut f = FALSE;
    for n in &names {
        let v = x.v(n);
        f = x.xor(f, v);
    }
    let opts = LiftOpts {
        max_support: 8,
        ..LiftOpts::default()
    };
    let mut l = Lifter::new(&mut x.b, &x.vars, opts);
    assert!(l.lift(f).is_none());
}

// ---- branches on a state register ---------------------------------------------

#[test]
fn branch_taken_in_one_state() {
    let mut x = Fx::new(&["state[4]", "cnt[8]", "hit"]);
    let (st, cnt) = (x.bus("state", 3, 0), x.bus("cnt", 7, 0));
    let is5 = x.eq_const(&st, 5);
    let lt = x.lt_const(&cnt, 200);
    let cond = x.and(is5, lt);
    let hit = x.v("hit");
    let f = x.ite(cond, hit, st[0]);
    assert_eq!(
        x.lift(f),
        "state[3:0] == 5 ? hit | cnt[7:0] >= 200 : state[0]"
    );
}

#[test]
fn two_states_with_different_actions() {
    let mut x = Fx::new(&["state[3]", "a[4]", "b[4]", "go"]);
    let (st, a, b) = (x.bus("state", 2, 0), x.bus("a", 3, 0), x.bus("b", 3, 0));
    let s2 = x.eq_const(&st, 2);
    let s6 = x.eq_const(&st, 6);
    let lt = words::ult(&mut x.b, &a, &b).unwrap();
    let go = x.v("go");
    let t2 = x.and(s2, lt);
    let t6 = x.and(s6, go);
    let f = x.or(t2, t6);
    assert_eq!(
        x.lift(f),
        "state[2:0] == 2 ? a[3:0] < b[3:0] : state[2:0] == 6 & go"
    );
}

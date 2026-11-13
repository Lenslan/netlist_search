//! Recognizers tested through real gates: word-level logic is synthesised into
//! randomly structured gates, written as Verilog, parsed, traced and lifted.

use netlist_search::liberty::CellLib;
use netlist_search::logic::{AnalyzeOpts, analyze};
use netlist_search::netlist::design::Design;
use netlist_search::netlist::index::ModuleIndex;
use netlist_search::synth::{ONE, Sig, Synth, ZERO};
use netlist_search::trace::{Cone, NodeKind, TraceOpts, trace};

fn lib() -> CellLib {
    let mut lib = CellLib::new();
    lib.load_str(include_str!("fixtures/basic.lib")).unwrap();
    lib
}

/// Endpoint form of `wire` in the netlist `src` (its last module is the top).
fn form_with(src: &str, wire: &str, opts: &AnalyzeOpts) -> String {
    let lib = lib();
    let index = ModuleIndex::build(&[src.as_bytes()]).unwrap();
    let design = Design::new(index, &lib);
    let path = design.resolve(None, "").unwrap_or_else(|e| panic!("{e:#}\n{src}"));
    let m = design.module(path.module()).unwrap();
    let bits = design.find_wire_bits(m, wire).unwrap_or_else(|e| panic!("{e:#}"));
    let cone = trace(&design, &path, bits[0], &TraceOpts::default()).unwrap();
    let a = analyze(&cone, None, opts);
    assert!(
        !a.notes.iter().any(|n| n.contains("INTERNAL")),
        "{:?}",
        a.notes
    );
    let info = a.wires[cone.target as usize].clone().expect("target is a wire");
    info.endpoint_form
        .unwrap_or_else(|| format!("<{}>", info.omitted.unwrap_or_else(|| "cut".into())))
}

fn form(src: &str, wire: &str) -> String {
    form_with(src, wire, &AnalyzeOpts::default())
}

fn arith() -> AnalyzeOpts {
    AnalyzeOpts {
        prefer_arith: true,
        ..AnalyzeOpts::default()
    }
}

/// Build with several seeds: the result must not depend on the gate structure.
fn each_seed(build: impl Fn(&mut Synth), check: impl Fn(&str)) {
    for seed in 1..=6u64 {
        let mut s = Synth::new("m", seed * 0x9e37_79b9);
        s.vary = seed > 1;
        build(&mut s);
        check(&s.emit());
    }
}

#[test]
fn compare_with_constant() {
    each_seed(
        |s| {
            let cnt = s.reg("cnt", 4);
            let lt = s.ult(&cnt, &Synth::constant(10, 4));
            s.name_net(&lt, "lt10");
            let ge = s.ult(&cnt, &Synth::constant(6, 4));
            let ge = s.not(&ge);
            s.name_net(&ge, "ge6");
            let eq = s.eq(&cnt, &Synth::constant(5, 4));
            s.name_net(&eq, "eq5");
        },
        |v| {
            assert_eq!(form(v, "lt10"), "cnt[3:0] < 10");
            assert_eq!(form(v, "ge6"), "cnt[3:0] >= 6");
            assert_eq!(form(v, "eq5"), "cnt[3:0] == 5");
        },
    );
}

#[test]
fn compare_two_buses() {
    each_seed(
        |s| {
            let a = s.reg("a", 6);
            let b = s.input_bus("b", 6);
            let lt = s.ult(&a, &b);
            s.name_net(&lt, "lt");
            let ge = s.not(&lt);
            s.name_net(&ge, "ge");
            let gt = s.ult(&b, &a);
            s.name_net(&gt, "gt");
            let eq = s.eq(&a, &b);
            s.name_net(&eq, "eq");
        },
        |v| {
            assert_eq!(form(v, "lt"), "a[5:0] < b[5:0]");
            assert_eq!(form(v, "ge"), "a[5:0] >= b[5:0]");
            assert_eq!(form(v, "gt"), "a[5:0] > b[5:0]");
            assert_eq!(form(v, "eq"), "a[5:0] == b[5:0]");
        },
    );
}

#[test]
fn window_and_enable() {
    each_seed(
        |s| {
            let cnt = s.reg("cnt", 8);
            let en = s.input("en");
            let lo = s.ult(&cnt, &Synth::constant(16, 8));
            let lo = s.not(&lo);
            let hi = s.ult(&cnt, &Synth::constant(200, 8));
            let win = s.and(&lo, &hi);
            s.name_net(&win, "win");
            let g = s.and(&en, &win);
            s.name_net(&g, "gated");
        },
        |v| {
            assert_eq!(form(v, "win"), "cnt[7:0] >= 16 & cnt[7:0] < 200");
            assert_eq!(form(v, "gated"), "en & cnt[7:0] >= 16 & cnt[7:0] < 200");
        },
    );
}

#[test]
fn bitmap_index() {
    each_seed(
        |s| {
            let bitmap = s.reg("bitmap", 16);
            let idx = s.reg("idx", 4);
            let hit = s.index(&bitmap, &idx);
            s.name_net(&hit, "hit");
        },
        |v| assert_eq!(form(v, "hit"), "bitmap[idx[3:0]]"),
    );
}

#[test]
fn barrel_shifters() {
    each_seed(
        |s| {
            let d = s.reg("d", 8);
            let sh = s.input_bus("sh", 3);
            let r = s.shr(&d, &sh, &ZERO);
            s.name_net(&r[2], "shr2");
            s.name_net(&r[0], "shr0");
            let l = s.shl(&d, &sh);
            s.name_net(&l[5], "shl5");
            let ar = s.shr(&d, &sh, &d[7].clone());
            s.name_net(&ar[2], "ashr2");
        },
        |v| {
            assert_eq!(form(v, "shr2"), "(d[7:0] >> sh[2:0])[2]");
            assert_eq!(form(v, "shr0"), "d[sh[2:0]]");
            assert_eq!(form(v, "shl5"), "(d[5:0] << sh[2:0])[5]");
            assert_eq!(form(v, "ashr2"), "($signed(d[7:0]) >>> sh[2:0])[2]");
        },
    );
}

#[test]
fn counter_increment_and_next_state() {
    each_seed(
        |s| {
            let cnt = s.reg("cnt", 4);
            let (rst, en) = (s.input("rst"), s.input("en"));
            let inc = s.add(&cnt, &Synth::constant(1, 4), &ZERO);
            s.name_net(&inc[3], "inc3");
            let dec = s.sub(&cnt, &Synth::constant(1, 4));
            s.name_net(&dec[3], "dec3");
            let held = s.mux(&en, &inc[3], &cnt[3]);
            let nrst = s.not(&rst);
            let next = s.and(&nrst, &held);
            s.name_net(&next, "next3");
        },
        |v| {
            assert_eq!(form(v, "inc3"), "(cnt[3:0] + 1)[3]");
            assert_eq!(form(v, "dec3"), "(cnt[3:0] - 1)[3]");
            assert_eq!(form(v, "next3"), "!rst & (en ? (cnt[3:0] + 1)[3] : cnt[3])");
        },
    );
}

#[test]
fn adders_and_subtractors() {
    each_seed(
        |s| {
            let a = s.reg("a", 8);
            let b = s.input_bus("b", 8);
            let cin = s.input("cin");
            let sum = s.add(&a, &b, &ZERO);
            s.name_net(&sum[7], "sum7");
            s.name_net(&sum[8], "carry");
            let diff = s.sub(&a, &b);
            s.name_net(&diff[7], "diff7");
            let sumc = s.add(&a, &b, &cin);
            s.name_net(&sumc[5], "sumc5");
            let k = s.add(&a, &Synth::constant(37, 8), &ZERO);
            s.name_net(&k[7], "k7");
        },
        |v| {
            assert_eq!(form(v, "sum7"), "(a[7:0] + b[7:0])[7]");
            assert_eq!(form(v, "carry"), "(a[7:0] + b[7:0])[8]");
            assert_eq!(form(v, "diff7"), "(a[7:0] - b[7:0])[7]");
            assert_eq!(form(v, "sumc5"), "(a[5:0] + b[5:0] + cin)[5]");
            assert_eq!(form_with(v, "k7", &arith()), "(a[7:0] + 37)[7]");
        },
    );
}

#[test]
fn small_multiplier() {
    each_seed(
        |s| {
            let a = s.reg("a", 4);
            let b = s.reg("b", 4);
            let p = s.mul(&a, &b);
            s.name_net(&p[5], "p5");
            s.name_net(&p[7], "p7");
            let k = s.mul(&a, &Synth::constant(5, 3));
            s.name_net(&k[4], "k4");
        },
        |v| {
            assert_eq!(form(v, "p5"), "(a[3:0] * b[3:0])[5]");
            assert_eq!(form(v, "p7"), "(a[3:0] * b[3:0])[7]");
            assert_eq!(form_with(v, "k4", &arith()), "(a[3:0] * 5)[4]");
        },
    );
}

#[test]
fn wide_adder_and_comparator_stay_exact() {
    let mut s = Synth::new("m", 7);
    let a = s.reg("a", 32);
    let b = s.reg("b", 32);
    let sum = s.add(&a, &b, &ZERO);
    s.name_net(&sum[31], "sum31");
    let lt = s.ult(&a, &b);
    s.name_net(&lt, "lt");
    let v = s.emit();
    assert_eq!(form(&v, "sum31"), "(a[31:0] + b[31:0])[31]");
    assert_eq!(form(&v, "lt"), "a[31:0] < b[31:0]");
}

/// Evaluate a cone node by plain simulation of its gates.
fn simulate(cone: &Cone, id: u32, value_of: &dyn Fn(&str) -> bool) -> bool {
    match &cone.node(id).kind {
        NodeKind::Const(c) => *c,
        NodeKind::Endpoint { ep, inv } => value_of(&cone.endpoints[*ep as usize].name) ^ inv,
        NodeKind::Alias { src, inv, .. } => simulate(cone, *src, value_of) ^ inv,
        NodeKind::Gate { func, inputs, .. } => func.eval(&|pin| {
            let (_, n) = inputs.iter().find(|(p, _)| p == pin).unwrap();
            simulate(cone, *n, value_of)
        }),
    }
}

#[test]
fn random_logic_forms_agree_with_gate_simulation() {
    // The endpoint form is parsed back by a tiny evaluator and compared with
    // simulating the gates, on random input vectors.
    for seed in 1..=20u64 {
        let mut s = Synth::new("m", seed * 77);
        let x = s.reg("x", 3);
        let y = s.input_bus("y", 3);
        let p = s.input("p");
        let mut ins = x.clone();
        ins.extend(y.clone());
        ins.push(p);
        let out = s.random_logic(&ins, 14, 1);
        if matches!(out[0], Sig::Const(_)) {
            continue;
        }
        s.name_net(&out[0], "f");
        let v = s.emit();

        let lib = lib();
        let index = ModuleIndex::build(&[v.as_bytes()]).unwrap();
        let design = Design::new(index, &lib);
        let path = design.resolve(None, "").unwrap();
        let m = design.module(path.module()).unwrap();
        let bit = design.find_wire_bits(m, "f").unwrap()[0];
        let cone = trace(&design, &path, bit, &TraceOpts::default()).unwrap();
        let a = analyze(&cone, None, &AnalyzeOpts::default());
        assert!(a.notes.is_empty(), "{:?}", a.notes);
        let text = a.wires[cone.target as usize]
            .as_ref()
            .and_then(|w| w.endpoint_form.clone())
            .unwrap_or_else(|| panic!("no form for seed {seed}"));
        let mut rng = seed.wrapping_mul(0x2545_f491_4f6c_dd1d) | 1;
        for _ in 0..64 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            let r = rng;
            let value_of = |name: &str| -> bool {
                let slot = match name {
                    "p" => 6,
                    _ => {
                        let i = name[2..3].parse::<usize>().unwrap();
                        if name.starts_with('x') { i } else { 3 + i }
                    }
                };
                r >> slot & 1 == 1
            };
            let want = simulate(&cone, cone.target, &value_of);
            let got = mini_eval::eval(&text, &|bus, hi, lo| {
                (lo..=hi).rev().fold(0u64, |acc, i| {
                    let name = if bus == "p" { "p".to_string() } else { format!("{bus}[{i}]") };
                    acc << 1 | u64::from(value_of(&name))
                })
            });
            assert_eq!(got, want, "seed {seed}: '{text}'\n{v}");
        }
    }
}

/// A small independent evaluator for the report's expression syntax: enough
/// for boolean operators, `?:`, comparisons with constants and `inside`.
mod mini_eval {
    pub fn eval(text: &str, bus: &dyn Fn(&str, u32, u32) -> u64) -> bool {
        let toks = lex(text);
        let mut p = P { t: &toks, i: 0, bus };
        let v = p.mux();
        assert_eq!(p.i, toks.len(), "trailing tokens in '{text}'");
        v != 0
    }

    fn lex(s: &str) -> Vec<String> {
        let b = s.as_bytes();
        let mut out = Vec::new();
        let mut i = 0;
        while i < b.len() {
            let c = b[i] as char;
            if c.is_whitespace() {
                i += 1;
            } else if c.is_ascii_alphanumeric() || c == '_' || c == '\'' {
                let st = i;
                while i < b.len()
                    && ((b[i] as char).is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'')
                {
                    i += 1;
                }
                out.push(s[st..i].to_string());
            } else if i + 1 < b.len() && matches!(&s[i..i + 2], "==" | "!=" | "<=" | ">=") {
                out.push(s[i..i + 2].to_string());
                i += 2;
            } else {
                out.push(c.to_string());
                i += 1;
            }
        }
        out
    }

    struct P<'a> {
        t: &'a [String],
        i: usize,
        bus: &'a dyn Fn(&str, u32, u32) -> u64,
    }

    impl P<'_> {
        fn peek(&self) -> &str {
            self.t.get(self.i).map_or("", String::as_str)
        }
        fn eat(&mut self, s: &str) -> bool {
            if self.peek() == s {
                self.i += 1;
                true
            } else {
                false
            }
        }
        fn expect(&mut self, s: &str) {
            assert!(self.eat(s), "expected '{s}', found '{}'", self.peek());
        }
        fn mux(&mut self) -> u64 {
            let c = self.or();
            if self.eat("?") {
                let t = self.mux();
                self.expect(":");
                let e = self.mux();
                return if c != 0 { t } else { e };
            }
            c
        }
        fn or(&mut self) -> u64 {
            let mut v = self.xor();
            while self.eat("|") {
                let r = self.xor();
                v = u64::from(v != 0 || r != 0);
            }
            v
        }
        fn xor(&mut self) -> u64 {
            let mut v = self.and();
            while self.eat("^") {
                let r = self.and();
                v = u64::from((v != 0) ^ (r != 0));
            }
            v
        }
        fn and(&mut self) -> u64 {
            let mut v = self.cmp();
            while self.eat("&") {
                let r = self.cmp();
                v = u64::from(v != 0 && r != 0);
            }
            v
        }
        fn cmp(&mut self) -> u64 {
            let l = self.unary();
            let op = self.peek().to_string();
            match op.as_str() {
                "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                    self.i += 1;
                    let r = self.unary();
                    u64::from(match op.as_str() {
                        "==" => l == r,
                        "!=" => l != r,
                        "<" => l < r,
                        "<=" => l <= r,
                        ">" => l > r,
                        _ => l >= r,
                    })
                }
                "inside" => {
                    self.i += 1;
                    self.expect("{");
                    let mut hit = false;
                    loop {
                        hit |= self.unary() == l;
                        if !self.eat(",") {
                            break;
                        }
                    }
                    self.expect("}");
                    u64::from(hit)
                }
                _ => l,
            }
        }
        fn unary(&mut self) -> u64 {
            if self.eat("!") {
                return u64::from(self.unary() == 0);
            }
            if self.eat("(") {
                let v = self.mux();
                self.expect(")");
                return v;
            }
            let t = self.peek().to_string();
            self.i += 1;
            if t == "1'b1" {
                return 1;
            }
            if t == "1'b0" {
                return 0;
            }
            if let Ok(n) = t.parse::<u64>() {
                return n;
            }
            if self.eat("[") {
                let hi: u32 = self.peek().parse().unwrap();
                self.i += 1;
                let lo = if self.eat(":") {
                    let lo: u32 = self.peek().parse().unwrap();
                    self.i += 1;
                    lo
                } else {
                    hi
                };
                self.expect("]");
                return (self.bus)(&t, hi, lo);
            }
            (self.bus)(&t, 0, 0)
        }
    }
}

#[test]
fn synth_constants_do_not_reach_the_netlist_as_gates() {
    let mut s = Synth::new("m", 3);
    let a = s.input("a");
    assert_eq!(s.and(&a, &ZERO), ZERO);
    assert_eq!(s.or(&a, &ONE), ONE);
    assert_eq!(s.and(&a, &ONE), a);
    assert_eq!(s.lines(), 0);
}

#[test]
fn wide_multiplier_is_matched_in_simulation_and_marked_unproven() {
    let mut s = Synth::new("m", 11);
    let a = s.reg("a", 16);
    let b = s.reg("b", 16);
    let p = s.mul(&a, &b);
    s.name_net(&p[20], "p20");
    let v = s.emit();

    let lib = lib();
    let index = ModuleIndex::build(&[v.as_bytes()]).unwrap();
    let design = Design::new(index, &lib);
    let path = design.resolve(None, "").unwrap();
    let m = design.module(path.module()).unwrap();
    let bit = design.find_wire_bits(m, "p20").unwrap()[0];
    let cone = trace(&design, &path, bit, &TraceOpts::default()).unwrap();
    let mut shown = vec![false; cone.nodes.len()];
    shown[cone.target as usize] = true;

    let a = analyze(&cone, Some(&shown), &AnalyzeOpts::default());
    let info = a.wires[cone.target as usize].clone().unwrap();
    assert_eq!(info.endpoint_form.as_deref(), Some("(a[15:0] * b[15:0])[20]"));
    assert!(info.unproven);
    assert!(a.notes.iter().any(|n| n.contains("unproven")), "{:?}", a.notes);

    let strict = AnalyzeOpts {
        strict: true,
        ..AnalyzeOpts::default()
    };
    let a = analyze(&cone, Some(&shown), &strict);
    let info = a.wires[cone.target as usize].clone().unwrap();
    assert!(!info.unproven);
    assert!(info.endpoint_form.as_deref() != Some("(a[15:0] * b[15:0])[20]"));
}

#[test]
fn random_logic_is_not_mistaken_for_a_product() {
    for seed in 1..=10u64 {
        let mut s = Synth::new("m", seed * 131);
        let a = s.reg("a", 6);
        let b = s.reg("b", 6);
        let mut ins = a.clone();
        ins.extend(b);
        let out = s.random_logic(&ins, 40, 1);
        if matches!(out[0], Sig::Const(_)) {
            continue;
        }
        s.name_net(&out[0], "f");
        let v = s.emit();
        let lib = lib();
        let index = ModuleIndex::build(&[v.as_bytes()]).unwrap();
        let design = Design::new(index, &lib);
        let path = design.resolve(None, "").unwrap();
        let m = design.module(path.module()).unwrap();
        let bit = design.find_wire_bits(m, "f").unwrap()[0];
        let cone = trace(&design, &path, bit, &TraceOpts::default()).unwrap();
        let a = analyze(&cone, None, &AnalyzeOpts::default());
        assert!(a.wires.iter().flatten().all(|w| !w.unproven), "seed {seed}");
    }
}

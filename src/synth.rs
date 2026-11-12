//! A tiny gate-level builder: word-level operations in, structural Verilog
//! out, using the cells of `tests/fixtures/basic.lib`.
//!
//! It exists to produce test netlists and the benchmark netlist. With `vary`
//! set, each operator is built from a randomly chosen gate structure, so tests
//! do not depend on one particular shape of logic.

use std::fmt::Write;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sig {
    Net(String),
    Const(bool),
}

impl Sig {
    fn text(&self) -> &str {
        match self {
            Sig::Net(n) => n,
            Sig::Const(true) => "1'b1",
            Sig::Const(false) => "1'b0",
        }
    }
}

pub const ZERO: Sig = Sig::Const(false);
pub const ONE: Sig = Sig::Const(true);

struct Reg {
    name: String,
    width: usize,
    d: Vec<Sig>,
}

pub struct Synth {
    name: String,
    ports: Vec<(String, &'static str, usize)>,
    wires: Vec<(String, usize)>,
    body: String,
    regs: Vec<Reg>,
    nets: u32,
    insts: u32,
    rng: u64,
    /// Choose gate structures at random.
    pub vary: bool,
    has_clk: bool,
}

/// Verilog spelling of a name: escaped if it is not a plain identifier.
fn ident(name: &str) -> String {
    let plain = name
        .bytes()
        .all(|c| c.is_ascii_alphanumeric() || c == b'_' || c == b'$')
        && !name.as_bytes().first().is_some_and(u8::is_ascii_digit);
    if plain {
        name.to_string()
    } else {
        format!("\\{name} ")
    }
}

/// MSB-first concatenation of little-endian bits.
fn concat(bits: &[Sig]) -> String {
    match bits {
        [one] => one.text().to_string(),
        _ => {
            let parts: Vec<&str> = bits.iter().rev().map(Sig::text).collect();
            format!("{{{}}}", parts.join(", "))
        }
    }
}

impl Synth {
    pub fn new(module: &str, seed: u64) -> Self {
        Synth {
            name: module.to_string(),
            ports: Vec::new(),
            wires: Vec::new(),
            body: String::new(),
            regs: Vec::new(),
            nets: 0,
            insts: 0,
            rng: seed | 1,
            vary: true,
            has_clk: false,
        }
    }

    pub fn rand(&mut self) -> u64 {
        self.rng ^= self.rng << 13;
        self.rng ^= self.rng >> 7;
        self.rng ^= self.rng << 17;
        self.rng
    }

    fn pick(&mut self, n: u64) -> u64 {
        if self.vary { self.rand() % n } else { 0 }
    }

    /// Number of instance lines emitted so far.
    pub fn lines(&self) -> u32 {
        self.insts
    }

    fn bits(name: &str, width: usize) -> Vec<Sig> {
        (0..width).map(|i| Sig::Net(format!("{name}[{i}]"))).collect()
    }

    pub fn input(&mut self, name: &str) -> Sig {
        self.ports.push((name.to_string(), "input", 0));
        Sig::Net(name.to_string())
    }

    /// An input bus; bits are returned least significant first.
    pub fn input_bus(&mut self, name: &str, width: usize) -> Vec<Sig> {
        self.ports.push((name.to_string(), "input", width));
        Self::bits(name, width)
    }

    pub fn output(&mut self, name: &str, value: &Sig) {
        self.ports.push((name.to_string(), "output", 0));
        let _ = writeln!(self.body, "  assign {name} = {};", value.text());
    }

    pub fn output_bus(&mut self, name: &str, value: &[Sig]) {
        self.ports.push((name.to_string(), "output", value.len()));
        let _ = writeln!(self.body, "  assign {name} = {};", concat(value));
    }

    /// A declared wire bus, to be driven by an instance output.
    pub fn wire_bus(&mut self, name: &str, width: usize) -> Vec<Sig> {
        self.wires.push((name.to_string(), width));
        Self::bits(name, width)
    }

    /// A register of flip-flops named `<name>_reg[i]`; returns its Q bits.
    /// Until `set_d` is called the register holds its value.
    pub fn reg(&mut self, name: &str, width: usize) -> Vec<Sig> {
        self.wires.push((name.to_string(), width));
        let q = Self::bits(name, width);
        self.regs.push(Reg {
            name: name.to_string(),
            width,
            d: q.clone(),
        });
        q
    }

    pub fn set_d(&mut self, name: &str, d: &[Sig]) {
        let r = self
            .regs
            .iter_mut()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("no register {name}"));
        assert_eq!(r.width, d.len(), "width of register {name}");
        r.d = d.to_vec();
    }

    fn fresh(&mut self) -> String {
        self.nets += 1;
        format!("n{}", self.nets)
    }

    /// Instantiate `cell` with the given input pins; returns the net on `Y`.
    fn cell(&mut self, cell: &str, pins: &[(&str, &Sig)]) -> Sig {
        let y = self.fresh();
        self.insts += 1;
        let _ = write!(self.body, "  {cell} U{} (", self.insts);
        for (p, s) in pins {
            let _ = write!(self.body, ".{p}({}), ", s.text());
        }
        let _ = writeln!(self.body, ".Y({y}));");
        Sig::Net(y)
    }

    /// Give `value` a name of its own (through a buffer).
    pub fn name_net(&mut self, value: &Sig, name: &str) -> Sig {
        self.insts += 1;
        self.wires.push((name.to_string(), 0));
        let _ = writeln!(
            self.body,
            "  BUFX2 U{} (.A({}), .Y({}));",
            self.insts,
            value.text(),
            ident(name)
        );
        Sig::Net(ident(name))
    }

    /// Any instance: module or black box. Pins are `(name, bits LSB first)`.
    pub fn instance(&mut self, cell: &str, inst: &str, pins: &[(&str, &[Sig])]) {
        self.insts += 1;
        let conns: Vec<String> = pins
            .iter()
            .map(|(p, bits)| format!(".{p}({})", concat(bits)))
            .collect();
        let _ = writeln!(self.body, "  {cell} {} ({});", ident(inst), conns.join(", "));
    }

    // ---- gates -------------------------------------------------------------

    pub fn not(&mut self, a: &Sig) -> Sig {
        match a {
            Sig::Const(c) => Sig::Const(!c),
            _ => self.cell("INVX1", &[("A", a)]),
        }
    }

    pub fn and(&mut self, a: &Sig, b: &Sig) -> Sig {
        match (a, b) {
            (Sig::Const(false), _) | (_, Sig::Const(false)) => ZERO,
            (Sig::Const(true), x) | (x, Sig::Const(true)) => x.clone(),
            _ if a == b => a.clone(),
            _ => match self.pick(3) {
                0 => self.cell("AND2X1", &[("A", a), ("B", b)]),
                1 => {
                    let n = self.cell("NAND2X1", &[("A", a), ("B", b)]);
                    self.not(&n)
                }
                _ => {
                    let (na, nb) = (self.not(a), self.not(b));
                    self.cell("NOR2X1", &[("A", &na), ("B", &nb)])
                }
            },
        }
    }

    pub fn or(&mut self, a: &Sig, b: &Sig) -> Sig {
        match (a, b) {
            (Sig::Const(true), _) | (_, Sig::Const(true)) => ONE,
            (Sig::Const(false), x) | (x, Sig::Const(false)) => x.clone(),
            _ if a == b => a.clone(),
            _ => match self.pick(3) {
                0 => self.cell("OR2X1", &[("A", a), ("B", b)]),
                1 => {
                    let n = self.cell("NOR2X1", &[("A", a), ("B", b)]);
                    self.not(&n)
                }
                _ => {
                    let (na, nb) = (self.not(a), self.not(b));
                    self.cell("NAND2X1", &[("A", &na), ("B", &nb)])
                }
            },
        }
    }

    pub fn xor(&mut self, a: &Sig, b: &Sig) -> Sig {
        match (a, b) {
            (Sig::Const(false), x) | (x, Sig::Const(false)) => x.clone(),
            (Sig::Const(true), x) | (x, Sig::Const(true)) => self.not(x),
            _ if a == b => ZERO,
            _ => match self.pick(3) {
                0 => self.cell("XOR2X1", &[("A", a), ("B", b)]),
                1 => {
                    let n = self.cell("XNOR2X1", &[("A", a), ("B", b)]);
                    self.not(&n)
                }
                _ => {
                    // (a | b) & !(a & b)
                    let o = self.cell("OR2X1", &[("A", a), ("B", b)]);
                    let n = self.cell("NAND2X1", &[("A", a), ("B", b)]);
                    self.cell("AND2X1", &[("A", &o), ("B", &n)])
                }
            },
        }
    }

    /// `s ? t : e`
    pub fn mux(&mut self, s: &Sig, t: &Sig, e: &Sig) -> Sig {
        match (s, t, e) {
            (Sig::Const(true), _, _) => t.clone(),
            (Sig::Const(false), _, _) => e.clone(),
            _ if t == e => t.clone(),
            (_, Sig::Const(_), _) | (_, _, Sig::Const(_)) => {
                let ns = self.not(s);
                let x = self.and(s, t);
                let y = self.and(&ns, e);
                self.or(&x, &y)
            }
            _ => match self.pick(3) {
                0 => self.cell("MUX2X1", &[("A", e), ("B", t), ("S", s)]),
                1 => {
                    let ns = self.not(s);
                    let n = self.cell("AOI22X1", &[("A0", s), ("A1", t), ("B0", &ns), ("B1", e)]);
                    self.not(&n)
                }
                _ => {
                    let ns = self.not(s);
                    let x = self.and(s, t);
                    let y = self.and(&ns, e);
                    self.or(&x, &y)
                }
            },
        }
    }

    pub fn and_all(&mut self, xs: &[Sig]) -> Sig {
        xs.iter().fold(ONE, |acc, x| self.and(&acc, x))
    }

    pub fn or_all(&mut self, xs: &[Sig]) -> Sig {
        xs.iter().fold(ZERO, |acc, x| self.or(&acc, x))
    }

    // ---- words (little-endian) ---------------------------------------------

    pub fn constant(value: u128, width: usize) -> Vec<Sig> {
        (0..width).map(|i| Sig::Const(value >> i & 1 == 1)).collect()
    }

    fn bit(v: &[Sig], i: usize) -> Sig {
        v.get(i).cloned().unwrap_or(ZERO)
    }

    /// `a + b + cin`, `max(len) + 1` bits.
    pub fn add(&mut self, a: &[Sig], b: &[Sig], cin: &Sig) -> Vec<Sig> {
        let w = a.len().max(b.len());
        let mut out = Vec::with_capacity(w + 1);
        let mut carry = cin.clone();
        for i in 0..w {
            let (x, y) = (Self::bit(a, i), Self::bit(b, i));
            let all_nets = [&x, &y, &carry].iter().all(|s| matches!(s, Sig::Net(_)));
            if all_nets && self.pick(2) == 0 {
                // One full-adder cell.
                let (s, co) = (self.fresh(), self.fresh());
                self.insts += 1;
                let _ = writeln!(
                    self.body,
                    "  ADDFX1 U{} (.A({}), .B({}), .CI({}), .S({s}), .CO({co}));",
                    self.insts,
                    x.text(),
                    y.text(),
                    carry.text()
                );
                out.push(Sig::Net(s));
                carry = Sig::Net(co);
            } else {
                let half = self.xor(&x, &y);
                out.push(self.xor(&half, &carry));
                let g = self.and(&x, &y);
                let p = self.and(&half, &carry);
                carry = self.or(&g, &p);
            }
        }
        out.push(carry);
        out
    }

    /// `a - b` modulo `2^(max(len) + 1)`.
    pub fn sub(&mut self, a: &[Sig], b: &[Sig]) -> Vec<Sig> {
        let w = a.len().max(b.len()) + 1;
        let a: Vec<Sig> = (0..w).map(|i| Self::bit(a, i)).collect();
        let nb: Vec<Sig> = (0..w)
            .map(|i| {
                let y = Self::bit(b, i);
                self.not(&y)
            })
            .collect();
        let mut r = self.add(&a, &nb, &ONE);
        r.truncate(w);
        r
    }

    /// `a * b`, `a.len() + b.len()` bits.
    pub fn mul(&mut self, a: &[Sig], b: &[Sig]) -> Vec<Sig> {
        let w = a.len() + b.len();
        let mut acc = vec![ZERO; w];
        for (i, y) in b.iter().enumerate() {
            let mut row = vec![ZERO; w];
            for (j, x) in a.iter().enumerate() {
                row[i + j] = self.and(x, y);
            }
            acc = self.add(&acc, &row, &ZERO);
            acc.truncate(w);
        }
        acc
    }

    pub fn eq(&mut self, a: &[Sig], b: &[Sig]) -> Sig {
        let w = a.len().max(b.len());
        let same: Vec<Sig> = (0..w)
            .map(|i| {
                let d = self.xor(&Self::bit(a, i), &Self::bit(b, i));
                self.not(&d)
            })
            .collect();
        self.and_all(&same)
    }

    /// Unsigned `a < b`.
    pub fn ult(&mut self, a: &[Sig], b: &[Sig]) -> Sig {
        let w = a.len().max(b.len());
        let mut less = ZERO;
        for i in 0..w {
            let (x, y) = (Self::bit(a, i), Self::bit(b, i));
            let nx = self.not(&x);
            let here = self.and(&nx, &y);
            let d = self.xor(&x, &y);
            let same = self.not(&d);
            let below = self.and(&same, &less);
            less = self.or(&here, &below);
        }
        less
    }

    /// `table[index]`, zero past the end of the table.
    pub fn index(&mut self, table: &[Sig], index: &[Sig]) -> Sig {
        let mut level: Vec<Sig> = table.to_vec();
        for s in index {
            level = level
                .chunks(2)
                .map(|pair| {
                    let odd = pair.get(1).cloned().unwrap_or(ZERO);
                    self.mux(s, &odd, &pair[0])
                })
                .collect();
        }
        level.first().cloned().unwrap_or(ZERO)
    }

    /// Barrel shifter: `a >> amount` (`fill` enters at the top).
    pub fn shr(&mut self, a: &[Sig], amount: &[Sig], fill: &Sig) -> Vec<Sig> {
        let mut cur = a.to_vec();
        for (i, s) in amount.iter().enumerate() {
            let step = 1usize << i;
            cur = (0..cur.len())
                .map(|k| {
                    let shifted = cur.get(k + step).cloned().unwrap_or_else(|| fill.clone());
                    self.mux(s, &shifted, &cur[k])
                })
                .collect();
        }
        cur
    }

    /// Barrel shifter: `a << amount`.
    pub fn shl(&mut self, a: &[Sig], amount: &[Sig]) -> Vec<Sig> {
        let mut cur = a.to_vec();
        for (i, s) in amount.iter().enumerate() {
            let step = 1usize << i;
            cur = (0..cur.len())
                .map(|k| {
                    let shifted = if k >= step { cur[k - step].clone() } else { ZERO };
                    self.mux(s, &shifted, &cur[k])
                })
                .collect();
        }
        cur
    }

    /// `n` gates of random two-input logic over `inputs`; returns the last
    /// `outputs` signals. Each gate reads recent signals, so depth is bounded.
    pub fn random_logic(&mut self, inputs: &[Sig], n: usize, outputs: usize) -> Vec<Sig> {
        let mut pool: Vec<Sig> = inputs.to_vec();
        for _ in 0..n {
            let window = pool.len().min(24);
            let base = pool.len() - window;
            let a = pool[base + (self.rand() as usize % window)].clone();
            let b = pool[self.rand() as usize % pool.len()].clone();
            let g = match self.rand() % 4 {
                0 => self.and(&a, &b),
                1 => self.or(&a, &b),
                2 => self.xor(&a, &b),
                _ => {
                    let c = pool[self.rand() as usize % pool.len()].clone();
                    self.mux(&a, &b, &c)
                }
            };
            pool.push(g);
        }
        let start = pool.len().saturating_sub(outputs);
        pool[start..].to_vec()
    }

    // ---- output ------------------------------------------------------------

    /// The module as structural Verilog.
    pub fn emit(&mut self) -> String {
        if !self.regs.is_empty() && !self.has_clk {
            self.has_clk = true;
            self.ports.insert(0, ("clk".to_string(), "input", 0));
        }
        let mut s = String::with_capacity(self.body.len() + 4096);
        let names: Vec<String> = self.ports.iter().map(|(n, _, _)| n.clone()).collect();
        let _ = writeln!(s, "module {} ({});", self.name, names.join(", "));
        let range = |w: usize| if w == 0 { String::new() } else { format!("[{}:0] ", w - 1) };
        for (n, dir, w) in &self.ports {
            let _ = writeln!(s, "  {dir} {}{n};", range(*w));
        }
        for (n, w) in &self.wires {
            let _ = writeln!(s, "  wire {}{};", range(*w), ident(n));
        }
        if self.nets > 0 {
            for chunk in (1..=self.nets).collect::<Vec<_>>().chunks(16) {
                let list: Vec<String> = chunk.iter().map(|i| format!("n{i}")).collect();
                let _ = writeln!(s, "  wire {};", list.join(", "));
            }
        }
        for r in &self.regs {
            for i in 0..r.width {
                let _ = writeln!(
                    s,
                    "  DFFX1 \\{}_reg[{i}] (.D({}), .CK(clk), .Q({}[{i}]));",
                    r.name,
                    r.d[i].text(),
                    r.name
                );
            }
        }
        s.push_str(&self.body);
        s.push_str("endmodule\n");
        s
    }
}

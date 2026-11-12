//! Parse one module body into compact, index-based structures.
//!
//! Nets are bit-blasted: every bit of every net gets a dense `BitId`. Names
//! are sub-slices of the (memory-mapped) source, so nothing is copied.

use std::fmt;
use std::ops::Range;
use std::sync::OnceLock;

use anyhow::{Result, anyhow};
use rustc_hash::FxHashMap;

use super::index::ModuleEntry;
use super::lexer::{Lexer, Tok, line_of};
use crate::liberty::Dir;

pub type BitId = u32;

/// One bit of a connection: a net bit, a constant, or nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitRef(u32);

impl BitRef {
    pub const CONST0: BitRef = BitRef(u32::MAX - 3);
    pub const CONST1: BitRef = BitRef(u32::MAX - 2);
    pub const CONSTX: BitRef = BitRef(u32::MAX - 1);
    pub const OPEN: BitRef = BitRef(u32::MAX);

    pub fn net(bit: BitId) -> Self {
        debug_assert!(bit < u32::MAX - 3);
        BitRef(bit)
    }

    pub fn as_net(self) -> Option<BitId> {
        (self.0 < u32::MAX - 3).then_some(self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignKind {
    /// `assign a = b;`
    Alias,
    /// `assign a = ~b;`
    Invert,
    /// Any other right-hand side; not interpreted.
    Complex,
}

pub struct Port<'a> {
    pub name: &'a [u8],
    pub dir: Dir,
    pub net: u32,
}

pub struct Net<'a> {
    pub name: &'a [u8],
    pub msb: i32,
    pub lsb: i32,
    pub is_vec: bool,
    /// BitId of the bit at index `lsb`.
    pub base: BitId,
}

impl Net<'_> {
    pub fn width(&self) -> u32 {
        self.msb.abs_diff(self.lsb) + 1
    }
}

/// A pin connected to a net bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PinRef {
    pub inst: u32,
    pub conn: u32,
    /// Position of the bit inside the connection, 0 = leftmost (MSB).
    pub pos: u32,
}

struct Inst<'a> {
    cell: u32,
    name: &'a [u8],
    conn_start: u32,
}

const NO_PIN: u32 = u32::MAX;

struct Conn {
    pin: u32,
    bit_start: u32,
}

pub struct Module<'a> {
    pub name: &'a [u8],
    pub ports: Vec<Port<'a>>,
    pub nets: Vec<Net<'a>>,
    pub warnings: Vec<String>,
    net_by_name: FxHashMap<&'a [u8], u32>,
    nbits: u32,
    cell_names: Vec<&'a [u8]>,
    pin_names: Vec<&'a [u8]>,
    /// One extra sentinel entry at the end.
    insts: Vec<Inst<'a>>,
    /// One extra sentinel entry at the end.
    conns: Vec<Conn>,
    conn_bits: Vec<BitRef>,
    assigns: FxHashMap<BitId, (BitRef, AssignKind)>,
    multi_assigned: Vec<BitId>,
    port_of_net: FxHashMap<u32, u32>,
    /// CSR reverse index: net bit -> positions in `conn_bits`.
    rev_off: Vec<u32>,
    rev: Vec<u32>,
    inst_by_name: OnceLock<FxHashMap<&'a [u8], u32>>,
}

impl fmt::Debug for Module<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Module({}, {} insts, {} bits)",
            String::from_utf8_lossy(self.name),
            self.num_insts(),
            self.nbits
        )
    }
}

impl<'a> Module<'a> {
    /// Parse the whole module.
    pub fn parse(entry: &ModuleEntry<'a>) -> Result<Self> {
        Parser::run(entry, false)
    }

    /// Parse only the port list and the declarations before the first
    /// instance or assign. Enough to learn port directions and widths.
    pub fn parse_header(entry: &ModuleEntry<'a>) -> Result<Self> {
        Parser::run(entry, true)
    }

    pub fn nbits(&self) -> u32 {
        self.nbits
    }

    pub fn num_insts(&self) -> u32 {
        self.insts.len() as u32 - 1
    }

    pub fn inst_cell(&self, inst: u32) -> &'a [u8] {
        self.cell_names[self.insts[inst as usize].cell as usize]
    }

    pub fn inst_name(&self, inst: u32) -> &'a [u8] {
        self.insts[inst as usize].name
    }

    /// Connection indices of an instance.
    pub fn inst_conns(&self, inst: u32) -> Range<u32> {
        self.insts[inst as usize].conn_start..self.insts[inst as usize + 1].conn_start
    }

    /// Pin name of a named connection; `None` for a positional one.
    pub fn conn_pin(&self, conn: u32) -> Option<&'a [u8]> {
        let p = self.conns[conn as usize].pin;
        (p != NO_PIN).then(|| self.pin_names[p as usize])
    }

    /// Bits of a connection, leftmost (MSB) first. Empty if unconnected.
    pub fn conn_bits(&self, conn: u32) -> &[BitRef] {
        let a = self.conns[conn as usize].bit_start as usize;
        let b = self.conns[conn as usize + 1].bit_start as usize;
        &self.conn_bits[a..b]
    }

    pub fn ref_name(&self, r: BitRef) -> String {
        match r {
            BitRef::CONST0 => "1'b0".into(),
            BitRef::CONST1 => "1'b1".into(),
            BitRef::CONSTX => "1'bx".into(),
            BitRef::OPEN => "<open>".into(),
            _ => self.bit_name(r.0),
        }
    }

    /// `(net index, offset from the net's LSB)` of a bit.
    pub fn net_of_bit(&self, bit: BitId) -> (u32, u32) {
        let n = self.nets.partition_point(|n| n.base <= bit) - 1;
        (n as u32, bit - self.nets[n].base)
    }

    pub fn bit_name(&self, bit: BitId) -> String {
        let (n, off) = self.net_of_bit(bit);
        let net = &self.nets[n as usize];
        let name = String::from_utf8_lossy(net.name);
        if net.is_vec {
            let idx = if net.msb >= net.lsb {
                net.lsb + off as i32
            } else {
                net.lsb - off as i32
            };
            format!("{name}[{idx}]")
        } else {
            name.into_owned()
        }
    }

    pub fn find_net(&self, name: &[u8]) -> Option<u32> {
        self.net_by_name.get(name).copied()
    }

    /// The bit of `net` at declared index `index` (0 for a scalar).
    pub fn bit_of(&self, net: u32, index: i32) -> Option<BitId> {
        let n = &self.nets[net as usize];
        let off = if n.msb >= n.lsb {
            index.checked_sub(n.lsb)?
        } else {
            n.lsb.checked_sub(index)?
        };
        (off >= 0 && (off as u32) < n.width()).then(|| n.base + off as u32)
    }

    /// Bits of a net, MSB first.
    pub fn net_bits(&self, net: u32) -> impl Iterator<Item = BitId> + use<> {
        let n = &self.nets[net as usize];
        let (base, w) = (n.base, n.width());
        (0..w).rev().map(move |o| base + o)
    }

    pub fn find_inst(&self, name: &[u8]) -> Option<u32> {
        let map = self.inst_by_name.get_or_init(|| {
            let mut m = FxHashMap::default();
            for i in 0..self.num_insts() {
                let n = self.insts[i as usize].name;
                if !n.is_empty() {
                    m.entry(n).or_insert(i);
                }
            }
            m
        });
        map.get(name).copied()
    }

    pub fn find_port(&self, name: &[u8]) -> Option<u32> {
        self.ports.iter().position(|p| p.name == name).map(|i| i as u32)
    }

    pub fn port_width(&self, port: u32) -> u32 {
        self.nets[self.ports[port as usize].net as usize].width()
    }

    /// `(port index, offset from the port's LSB)` if the bit belongs to a port.
    pub fn port_of_bit(&self, bit: BitId) -> Option<(u32, u32)> {
        let (n, off) = self.net_of_bit(bit);
        self.port_of_net.get(&n).map(|&p| (p, off))
    }

    /// The bit of a port at `offset` from its LSB.
    pub fn port_bit(&self, port: u32, offset: u32) -> Option<BitId> {
        let n = &self.nets[self.ports[port as usize].net as usize];
        (offset < n.width()).then(|| n.base + offset)
    }

    /// Every instance pin connected to `bit`.
    pub fn pins_on(&self, bit: BitId) -> impl Iterator<Item = PinRef> + '_ {
        let range = match self.rev_off.get(bit as usize + 1) {
            Some(&end) => self.rev_off[bit as usize] as usize..end as usize,
            None => 0..0,
        };
        self.rev[range].iter().map(move |&k| {
            let conn = self.conns.partition_point(|c| c.bit_start <= k) - 1;
            let inst = self.insts.partition_point(|i| i.conn_start as usize <= conn) - 1;
            PinRef {
                inst: inst as u32,
                conn: conn as u32,
                pos: k - self.conns[conn].bit_start,
            }
        })
    }

    /// The source of `bit` if it is the target of an `assign` (or a supply net).
    pub fn assign_driver(&self, bit: BitId) -> Option<(BitRef, AssignKind)> {
        self.assigns.get(&bit).copied()
    }

    /// True if more than one `assign` targets this bit.
    pub fn multi_assigned(&self, bit: BitId) -> bool {
        self.multi_assigned.contains(&bit)
    }
}

// ---------------------------------------------------------------------------

struct Parser<'a> {
    lx: Lexer<'a>,
    m: Module<'a>,
    cell_ids: FxHashMap<&'a [u8], u32>,
    pin_ids: FxHashMap<&'a [u8], u32>,
    port_dir_known: Vec<bool>,
    header_only: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExprKind {
    Plain,
    Invert,
    Complex,
}

impl<'a> Parser<'a> {
    fn run(entry: &ModuleEntry<'a>, header_only: bool) -> Result<Module<'a>> {
        let mut lx = Lexer::new(&entry.src[..entry.end]);
        lx.pos = entry.start;
        let mut p = Parser {
            lx,
            m: Module {
                name: entry.name,
                ports: Vec::new(),
                nets: Vec::new(),
                warnings: Vec::new(),
                net_by_name: FxHashMap::default(),
                nbits: 0,
                cell_names: Vec::new(),
                pin_names: Vec::new(),
                insts: Vec::new(),
                conns: Vec::new(),
                conn_bits: Vec::new(),
                assigns: FxHashMap::default(),
                multi_assigned: Vec::new(),
                port_of_net: FxHashMap::default(),
                rev_off: Vec::new(),
                rev: Vec::new(),
                inst_by_name: OnceLock::new(),
            },
            cell_ids: FxHashMap::default(),
            pin_ids: FxHashMap::default(),
            port_dir_known: Vec::new(),
            header_only,
        };
        p.header()?;
        p.body()?;
        Ok(p.finish())
    }

    fn err(&self, msg: impl fmt::Display) -> anyhow::Error {
        anyhow!(
            "module {}: {} at line {}",
            String::from_utf8_lossy(self.m.name),
            msg,
            line_of(self.lx.src, self.lx.tok_start)
        )
    }

    fn warn(&mut self, msg: impl fmt::Display) {
        if self.m.warnings.len() < 100 {
            let line = line_of(self.lx.src, self.lx.tok_start);
            self.m.warnings.push(format!(
                "module {}: {} at line {}",
                String::from_utf8_lossy(self.m.name),
                msg,
                line
            ));
        }
    }

    fn expect(&mut self, c: u8) -> Result<()> {
        match self.lx.next() {
            Tok::Punct(p) if p == c => Ok(()),
            t => Err(self.err(format!("expected '{}', found {}", c as char, show(t)))),
        }
    }

    fn peek_is(&mut self, c: u8) -> bool {
        self.lx.peek() == Tok::Punct(c)
    }

    // ---- declarations ------------------------------------------------------

    fn declare_net(&mut self, name: &'a [u8], range: Option<(i32, i32)>) -> u32 {
        if let Some(&n) = self.m.net_by_name.get(name) {
            if let Some((msb, lsb)) = range {
                let net = &self.m.nets[n as usize];
                if !net.is_vec || net.msb != msb || net.lsb != lsb {
                    self.warn(format!(
                        "net {} redeclared with a different range; keeping the first",
                        String::from_utf8_lossy(name)
                    ));
                }
            }
            return n;
        }
        let (msb, lsb, is_vec) = match range {
            Some((m, l)) => (m, l, true),
            None => (0, 0, false),
        };
        let n = self.m.nets.len() as u32;
        let net = Net {
            name,
            msb,
            lsb,
            is_vec,
            base: self.m.nbits,
        };
        self.m.nbits += net.width();
        self.m.nets.push(net);
        self.m.net_by_name.insert(name, n);
        n
    }

    fn set_port(&mut self, name: &'a [u8], dir: Option<Dir>, net: Option<u32>) {
        let i = match self.m.ports.iter().position(|p| p.name == name) {
            Some(i) => i,
            None => {
                self.m.ports.push(Port {
                    name,
                    dir: Dir::Inout,
                    net: u32::MAX,
                });
                self.port_dir_known.push(false);
                self.m.ports.len() - 1
            }
        };
        if let Some(d) = dir {
            self.m.ports[i].dir = d;
            self.port_dir_known[i] = true;
        }
        if let Some(n) = net {
            self.m.ports[i].net = n;
        }
    }

    fn int(&mut self) -> Result<i32> {
        let mut neg = false;
        let mut t = self.lx.next();
        if t == Tok::Punct(b'-') {
            neg = true;
            t = self.lx.next();
        }
        let Tok::Number(n) = t else {
            return Err(self.err(format!("expected a number, found {}", show(t))));
        };
        let v: i32 = std::str::from_utf8(n)
            .ok()
            .and_then(|s| s.parse().ok())
            .ok_or_else(|| self.err("bad index"))?;
        Ok(if neg { -v } else { v })
    }

    /// `[msb:lsb]` if present.
    fn opt_range(&mut self) -> Result<Option<(i32, i32)>> {
        if !self.peek_is(b'[') {
            return Ok(None);
        }
        self.lx.next();
        let msb = self.int()?;
        self.expect(b':')?;
        let lsb = self.int()?;
        self.expect(b']')?;
        Ok(Some((msb, lsb)))
    }

    fn skip_type_words(&mut self) {
        while let Tok::Ident(w) = self.lx.peek() {
            if matches!(w, b"wire" | b"reg" | b"logic" | b"signed" | b"tri" | b"unsigned") {
                self.lx.next();
            } else {
                break;
            }
        }
    }

    fn skip_balanced(&mut self) -> Result<()> {
        self.expect(b'(')?;
        let mut depth = 1;
        while depth > 0 {
            match self.lx.next() {
                Tok::Punct(b'(') => depth += 1,
                Tok::Punct(b')') => depth -= 1,
                Tok::Eof => return Err(self.err("unbalanced '('")),
                _ => {}
            }
        }
        Ok(())
    }

    fn header(&mut self) -> Result<()> {
        if self.peek_is(b'#') {
            self.lx.next();
            self.skip_balanced()?;
        }
        if self.peek_is(b';') {
            self.lx.next();
            return Ok(());
        }
        self.expect(b'(')?;
        let mut dir: Option<Dir> = None;
        let mut range = None;
        loop {
            match self.lx.next() {
                Tok::Punct(b')') => break,
                Tok::Punct(b',') => {}
                Tok::Ident(w @ (b"input" | b"output" | b"inout")) => {
                    dir = Some(match w {
                        b"input" => Dir::Input,
                        b"output" => Dir::Output,
                        _ => Dir::Inout,
                    });
                    self.skip_type_words();
                    range = self.opt_range()?;
                }
                Tok::Punct(b'.') => {
                    // `.name(expr)` port expression: not supported, skip it.
                    self.lx.next();
                    self.skip_balanced()?;
                    self.warn("port expressions in the module header are not supported");
                }
                t => {
                    let Some(name) = t.name() else {
                        return Err(self.err(format!("unexpected {} in port list", show(t))));
                    };
                    if dir.is_some() {
                        let net = self.declare_net(name, range);
                        self.set_port(name, dir, Some(net));
                    } else {
                        self.set_port(name, None, None);
                    }
                }
            }
        }
        self.expect(b';')
    }

    fn decl(&mut self, dir: Option<Dir>, supply: Option<BitRef>) -> Result<()> {
        self.skip_type_words();
        let range = self.opt_range()?;
        loop {
            let t = self.lx.next();
            let Some(name) = t.name() else {
                return Err(self.err(format!("expected a net name, found {}", show(t))));
            };
            let net = self.declare_net(name, range);
            if dir.is_some() {
                self.set_port(name, dir, Some(net));
            }
            if let Some(c) = supply {
                let bits: Vec<BitId> = self.m.net_bits(net).collect();
                for b in bits {
                    self.m.assigns.insert(b, (c, AssignKind::Alias));
                }
            }
            match self.lx.next() {
                Tok::Punct(b',') => {}
                Tok::Punct(b';') => return Ok(()),
                Tok::Punct(b'=') => {
                    // `wire x = expr;`
                    let lhs: Vec<BitRef> = self.m.net_bits(net).map(BitRef::net).collect();
                    let mut rhs = Vec::new();
                    let kind = self.expr(&mut rhs)?;
                    self.add_assign(&lhs, &rhs, kind);
                    match self.lx.next() {
                        Tok::Punct(b',') => {}
                        Tok::Punct(b';') => return Ok(()),
                        t => return Err(self.err(format!("expected ',' or ';', found {}", show(t)))),
                    }
                }
                t => return Err(self.err(format!("expected ',' or ';', found {}", show(t)))),
            }
        }
    }

    // ---- expressions -------------------------------------------------------

    /// Parse a connection / assign expression, appending its bits MSB first.
    fn expr(&mut self, out: &mut Vec<BitRef>) -> Result<ExprKind> {
        let mark = out.len();
        let mut kind = ExprKind::Plain;
        let mut t = self.lx.next();
        if matches!(t, Tok::Punct(b'~' | b'!')) {
            kind = ExprKind::Invert;
            t = self.lx.next();
        }
        if !self.primary(t, out)? {
            kind = ExprKind::Complex;
        }
        // Anything left before the delimiter means an operator expression.
        if !matches!(self.lx.peek(), Tok::Punct(b',' | b')' | b';' | b'}') | Tok::Eof) {
            kind = ExprKind::Complex;
        }
        if kind == ExprKind::Complex {
            out.truncate(mark);
            let mut depth = 0i32;
            loop {
                match self.lx.peek() {
                    Tok::Punct(b'(' | b'{' | b'[') => depth += 1,
                    Tok::Punct(b')' | b'}' | b']') if depth > 0 => depth -= 1,
                    Tok::Punct(b',' | b')' | b';' | b'}') if depth == 0 => break,
                    Tok::Eof => return Err(self.err("unterminated expression")),
                    _ => {}
                }
                self.lx.next();
            }
        }
        Ok(kind)
    }

    /// One operand starting at token `t`. Returns false if it is something
    /// this parser does not interpret.
    fn primary(&mut self, t: Tok<'a>, out: &mut Vec<BitRef>) -> Result<bool> {
        match t {
            Tok::Punct(b'{') => {
                loop {
                    if self.peek_is(b'}') {
                        self.lx.next();
                        break;
                    }
                    let item = self.lx.next();
                    let ok = match item {
                        Tok::Number(n) if self.peek_is(b'{') => {
                            // Replication `{N{...}}`.
                            let count: usize = std::str::from_utf8(n)
                                .ok()
                                .and_then(|s| s.parse().ok())
                                .ok_or_else(|| self.err("bad replication count"))?;
                            let mut inner = Vec::new();
                            let open = self.lx.next();
                            let ok = self.primary(open, &mut inner)?;
                            for _ in 0..count {
                                out.extend_from_slice(&inner);
                            }
                            ok
                        }
                        _ => self.primary(item, out)?,
                    };
                    if !ok {
                        return Ok(false);
                    }
                    match self.lx.next() {
                        Tok::Punct(b',') => {}
                        Tok::Punct(b'}') => break,
                        t => {
                            return Err(self.err(format!(
                                "expected ',' or '}}' in concatenation, found {}",
                                show(t)
                            )));
                        }
                    }
                }
                Ok(true)
            }
            Tok::Number(n) => {
                literal_bits(n, out).map_err(|e| self.err(e))?;
                Ok(true)
            }
            Tok::Ident(name) | Tok::Escaped(name) => {
                let name_start = self.lx.tok_start;
                let known = self.m.net_by_name.get(name).copied();
                if !self.peek_is(b'[') {
                    let net = match known {
                        Some(n) => n,
                        None => self.declare_net(name, None),
                    };
                    out.extend(self.m.net_bits(net).map(BitRef::net));
                    return Ok(true);
                }
                self.lx.next();
                let a = self.int()?;
                let b = if self.peek_is(b':') {
                    self.lx.next();
                    Some(self.int()?)
                } else {
                    None
                };
                self.expect(b']')?;
                let Some(net) = known.filter(|&n| self.m.nets[n as usize].is_vec) else {
                    // Select on something never declared as a vector: treat the
                    // whole text `name[i]` as the name of a scalar net.
                    let text = &self.lx.src[name_start..self.lx.pos];
                    let text = text.strip_prefix(b"\\").unwrap_or(text);
                    if !self.m.net_by_name.contains_key(text) {
                        self.warn(format!(
                            "{} is selected but never declared as a vector; treated as a scalar net",
                            String::from_utf8_lossy(text)
                        ));
                    }
                    let net = self.declare_net(text, None);
                    out.push(BitRef::net(self.m.nets[net as usize].base));
                    return Ok(true);
                };
                let (from, to) = (a, b.unwrap_or(a));
                let step = if from <= to { 1 } else { -1 };
                let mut i = from;
                loop {
                    let bit = self.m.bit_of(net, i).ok_or_else(|| {
                        self.err(format!(
                            "index {i} is outside the range of {}",
                            String::from_utf8_lossy(name)
                        ))
                    })?;
                    out.push(BitRef::net(bit));
                    if i == to {
                        break;
                    }
                    i += step;
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    // ---- statements --------------------------------------------------------

    fn add_assign(&mut self, lhs: &[BitRef], rhs: &[BitRef], kind: ExprKind) {
        for (i, l) in lhs.iter().rev().enumerate() {
            let Some(bit) = l.as_net() else { continue };
            let entry = match kind {
                ExprKind::Complex => (BitRef::OPEN, AssignKind::Complex),
                k => {
                    let r = if i < rhs.len() {
                        rhs[rhs.len() - 1 - i]
                    } else {
                        BitRef::CONST0
                    };
                    let k = if k == ExprKind::Invert {
                        AssignKind::Invert
                    } else {
                        AssignKind::Alias
                    };
                    (r, k)
                }
            };
            if self.m.assigns.insert(bit, entry).is_some() {
                self.m.multi_assigned.push(bit);
            }
        }
    }

    fn assign(&mut self) -> Result<()> {
        loop {
            let mut lhs = Vec::new();
            let t = self.lx.next();
            if !self.primary(t, &mut lhs)? {
                return Err(self.err("unsupported left-hand side in assign"));
            }
            self.expect(b'=')?;
            let mut rhs = Vec::new();
            let kind = self.expr(&mut rhs)?;
            self.add_assign(&lhs, &rhs, kind);
            match self.lx.next() {
                Tok::Punct(b',') => {}
                Tok::Punct(b';') => return Ok(()),
                t => return Err(self.err(format!("expected ',' or ';', found {}", show(t)))),
            }
        }
    }

    fn instance(&mut self, cell: &'a [u8]) -> Result<()> {
        let cell_id = match self.cell_ids.get(cell) {
            Some(&c) => c,
            None => {
                let c = self.m.cell_names.len() as u32;
                self.m.cell_names.push(cell);
                self.cell_ids.insert(cell, c);
                c
            }
        };
        if self.peek_is(b'#') {
            // Parameter override or delay.
            self.lx.next();
            if self.peek_is(b'(') {
                self.skip_balanced()?;
            } else {
                self.lx.next();
            }
        }
        loop {
            let name = match self.lx.peek() {
                t @ (Tok::Ident(_) | Tok::Escaped(_)) => {
                    self.lx.next();
                    t.name().unwrap()
                }
                _ => b"",
            };
            if self.peek_is(b'[') {
                self.opt_range()?;
                self.warn("instance arrays are not supported; treated as one instance");
            }
            self.expect(b'(')?;
            self.m.insts.push(Inst {
                cell: cell_id,
                name,
                conn_start: self.m.conns.len() as u32,
            });
            if self.peek_is(b')') {
                self.lx.next();
            } else {
                loop {
                    let mut bits = std::mem::take(&mut self.m.conn_bits);
                    let bit_start = bits.len() as u32;
                    let result = self.connection(&mut bits);
                    self.m.conn_bits = bits;
                    let pin = result?;
                    self.m.conns.push(Conn { pin, bit_start });
                    match self.lx.next() {
                        Tok::Punct(b',') => {}
                        Tok::Punct(b')') => break,
                        t => {
                            return Err(self.err(format!(
                                "expected ',' or ')' in the connection list, found {}",
                                show(t)
                            )));
                        }
                    }
                }
            }
            match self.lx.next() {
                Tok::Punct(b',') => {}
                Tok::Punct(b';') => return Ok(()),
                t => {
                    return Err(self.err(format!(
                        "expected ',' or ';' after an instance, found {}",
                        show(t)
                    )));
                }
            }
        }
    }

    /// One port connection; returns the pin id (or `NO_PIN` if positional).
    fn connection(&mut self, bits: &mut Vec<BitRef>) -> Result<u32> {
        let mark = bits.len();
        let pin = if self.peek_is(b'.') {
            self.lx.next();
            let t = self.lx.next();
            let Some(pin) = t.name() else {
                return Err(self.err(format!("expected a pin name, found {}", show(t))));
            };
            self.expect(b'(')?;
            let id = match self.pin_ids.get(pin) {
                Some(&p) => p,
                None => {
                    let p = self.m.pin_names.len() as u32;
                    self.m.pin_names.push(pin);
                    self.pin_ids.insert(pin, p);
                    p
                }
            };
            if !self.peek_is(b')') && self.expr(bits)? != ExprKind::Plain {
                self.unsupported_connection(bits, mark);
            }
            self.expect(b')')?;
            id
        } else {
            if !matches!(self.lx.peek(), Tok::Punct(b',' | b')'))
                && self.expr(bits)? != ExprKind::Plain
            {
                self.unsupported_connection(bits, mark);
            }
            NO_PIN
        };
        Ok(pin)
    }

    fn unsupported_connection(&mut self, bits: &mut Vec<BitRef>, mark: usize) {
        bits.truncate(mark);
        bits.push(BitRef::CONSTX);
        self.warn("expression in a port connection is not supported; treated as 1'bx");
    }

    fn body(&mut self) -> Result<()> {
        loop {
            let t = self.lx.next();
            match t {
                Tok::Eof => return Ok(()),
                Tok::Punct(b';') => {}
                Tok::Ident(w) => match w {
                    b"input" => self.decl(Some(Dir::Input), None)?,
                    b"output" => self.decl(Some(Dir::Output), None)?,
                    b"inout" => self.decl(Some(Dir::Inout), None)?,
                    b"wire" | b"tri" | b"wand" | b"wor" | b"tri0" | b"tri1" | b"triand"
                    | b"trior" | b"trireg" | b"reg" | b"logic" => self.decl(None, None)?,
                    b"supply0" => self.decl(None, Some(BitRef::CONST0))?,
                    b"supply1" => self.decl(None, Some(BitRef::CONST1))?,
                    b"parameter" | b"localparam" | b"defparam" | b"genvar" | b"integer"
                    | b"real" | b"time" | b"event" => {
                        self.lx.skip_past_semicolon();
                    }
                    b"specify" => loop {
                        match self.lx.next() {
                            Tok::Ident(b"endspecify") | Tok::Eof => break,
                            _ => {}
                        }
                    },
                    b"assign" => {
                        if self.header_only {
                            return Ok(());
                        }
                        self.assign()?;
                    }
                    _ => {
                        if self.header_only {
                            return Ok(());
                        }
                        self.instance(w)?;
                    }
                },
                Tok::Escaped(w) => {
                    if self.header_only {
                        return Ok(());
                    }
                    self.instance(w)?;
                }
                t => return Err(self.err(format!("unexpected {}", show(t)))),
            }
        }
    }

    fn finish(mut self) -> Module<'a> {
        // Ports named in the header but never declared are scalar nets.
        for i in 0..self.m.ports.len() {
            if self.m.ports[i].net == u32::MAX {
                let name = self.m.ports[i].name;
                self.m.ports[i].net = self.declare_net(name, None);
            }
        }
        let mut m = self.m;
        for (i, p) in m.ports.iter().enumerate() {
            m.port_of_net.entry(p.net).or_insert(i as u32);
        }
        m.insts.push(Inst {
            cell: 0,
            name: b"",
            conn_start: m.conns.len() as u32,
        });
        m.conns.push(Conn {
            pin: NO_PIN,
            bit_start: m.conn_bits.len() as u32,
        });
        if !self.header_only {
            let mut off = vec![0u32; m.nbits as usize + 1];
            for r in &m.conn_bits {
                if let Some(b) = r.as_net() {
                    off[b as usize + 1] += 1;
                }
            }
            for i in 1..off.len() {
                off[i] += off[i - 1];
            }
            let mut fill = off.clone();
            let mut rev = vec![0u32; m.conn_bits.len()];
            for (k, r) in m.conn_bits.iter().enumerate() {
                if let Some(b) = r.as_net() {
                    rev[fill[b as usize] as usize] = k as u32;
                    fill[b as usize] += 1;
                }
            }
            rev.truncate(*off.last().unwrap() as usize);
            m.rev_off = off;
            m.rev = rev;
        }
        m.insts.shrink_to_fit();
        m.conns.shrink_to_fit();
        m.conn_bits.shrink_to_fit();
        m.nets.shrink_to_fit();
        m
    }
}

fn show(t: Tok) -> String {
    match t {
        Tok::Ident(n) | Tok::Escaped(n) | Tok::Number(n) => {
            format!("'{}'", String::from_utf8_lossy(n))
        }
        Tok::Str(_) => "a string".into(),
        Tok::Punct(c) => format!("'{}'", c as char),
        Tok::Eof => "end of module".into(),
    }
}

/// Expand a Verilog number into bits, MSB first.
fn literal_bits(tok: &[u8], out: &mut Vec<BitRef>) -> std::result::Result<(), String> {
    let bad = || format!("bad literal '{}'", String::from_utf8_lossy(tok));
    let (size, rest) = match tok.iter().position(|&c| c == b'\'') {
        None => {
            let v: u64 = std::str::from_utf8(tok).ok().and_then(|s| s.parse().ok()).ok_or_else(bad)?;
            out.extend((0..32).rev().map(|i| if v >> i & 1 == 1 { BitRef::CONST1 } else { BitRef::CONST0 }));
            return Ok(());
        }
        Some(q) => {
            let size = if q == 0 {
                32
            } else {
                std::str::from_utf8(&tok[..q]).ok().and_then(|s| s.parse::<usize>().ok()).ok_or_else(bad)?
            };
            (size, &tok[q + 1..])
        }
    };
    let rest = match rest.first() {
        Some(b's' | b'S') => &rest[1..],
        _ => rest,
    };
    let (&base, digits) = rest.split_first().ok_or_else(bad)?;
    // Value bits, LSB first.
    let mut bits: Vec<BitRef> = Vec::new();
    let per_digit = match base.to_ascii_lowercase() {
        b'b' => 1,
        b'o' => 3,
        b'h' => 4,
        b'd' => 0,
        _ => return Err(bad()),
    };
    if per_digit == 0 {
        let text: String = digits.iter().filter(|&&c| c != b'_').map(|&c| c as char).collect();
        let v: u128 = text.parse().map_err(|_| bad())?;
        bits.extend((0..128).map(|i| if v >> i & 1 == 1 { BitRef::CONST1 } else { BitRef::CONST0 }));
    } else {
        for &c in digits.iter().rev() {
            if c == b'_' {
                continue;
            }
            match c.to_ascii_lowercase() {
                b'x' | b'z' | b'?' => bits.extend(std::iter::repeat_n(BitRef::CONSTX, per_digit)),
                d => {
                    let v = (d as char).to_digit(16).ok_or_else(bad)?;
                    if v >= 1 << per_digit {
                        return Err(bad());
                    }
                    bits.extend((0..per_digit).map(|i| {
                        if v >> i & 1 == 1 { BitRef::CONST1 } else { BitRef::CONST0 }
                    }));
                }
            }
        }
    }
    // Pad: x-extend if the top digit is x, else zero-extend.
    let pad = match bits.last() {
        Some(&BitRef::CONSTX) if per_digit != 0 => BitRef::CONSTX,
        _ => BitRef::CONST0,
    };
    bits.resize(size.max(1).min(1 << 20), pad);
    out.extend(bits.iter().rev());
    Ok(())
}

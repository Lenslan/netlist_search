//! Streaming Liberty parser. Only `cell`, `pin`, `bus`, `ff`, `latch` and
//! `statetable` groups are interpreted; everything else (timing tables, power,
//! templates) is skipped by brace counting without building a tree.

use anyhow::{Result, bail};

use super::func::parse_function;
use super::{CellDef, CellKind, Dir, PinDef};

pub(super) fn parse_library(text: &[u8], warnings: &mut Vec<String>) -> Result<Vec<CellDef>> {
    let mut cur = Cur { s: text, p: 0 };
    let mut cells = Vec::new();
    loop {
        match cur.stmt()? {
            Stmt::Eof => break,
            Stmt::Group(name, _) if name == b"library" => {
                let open = cur.line();
                loop {
                    match cur.stmt()? {
                        Stmt::Group(g, args) if g == b"cell" => {
                            let name = args.first().copied().unwrap_or(b"");
                            cells.push(parse_cell(&mut cur, name, warnings)?);
                        }
                        Stmt::Group(..) => cur.skip_body()?,
                        Stmt::End => break,
                        Stmt::Eof => bail!(
                            "unexpected end of file inside library group opened at line {open}"
                        ),
                        Stmt::Attr(..) | Stmt::Complex => {}
                    }
                }
            }
            Stmt::Group(..) => cur.skip_body()?,
            Stmt::End => bail!("unmatched '}}' at line {}", cur.line()),
            Stmt::Attr(..) | Stmt::Complex => {}
        }
    }
    Ok(cells)
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

fn parse_cell(cur: &mut Cur, name: &[u8], warnings: &mut Vec<String>) -> Result<CellDef> {
    let open = cur.line();
    let name = text(name);
    let mut pins: Vec<PinDef> = Vec::new();
    let mut kind = CellKind::Comb;
    let mut state_vars = None;
    let mut has_statetable = false;
    loop {
        match cur.stmt()? {
            Stmt::Group(g, args) => match g {
                b"pin" | b"bus" | b"bundle" => {
                    let is_bus = g != b"pin";
                    let body = parse_pin_body(cur, &name, &args, warnings)?;
                    for a in &args {
                        let pin_name = text(a);
                        if pins.iter().any(|p| p.name == pin_name) {
                            continue;
                        }
                        pins.push(PinDef {
                            name: pin_name,
                            dir: body.dir,
                            function: body.function.clone(),
                            three_state: body.three_state,
                            is_bus,
                        });
                    }
                }
                b"ff" | b"ff_bank" | b"latch" | b"latch_bank" => {
                    kind = if g.starts_with(b"ff") {
                        CellKind::Ff
                    } else {
                        CellKind::Latch
                    };
                    if args.len() >= 2 {
                        state_vars = Some((text(args[0]), text(args[1])));
                    }
                    cur.skip_body()?;
                }
                b"statetable" => {
                    has_statetable = true;
                    cur.skip_body()?;
                }
                _ => cur.skip_body()?,
            },
            Stmt::End => break,
            Stmt::Eof => {
                bail!("unexpected end of file inside cell ({name}) opened at line {open}")
            }
            Stmt::Attr(..) | Stmt::Complex => {}
        }
    }
    if kind == CellKind::Comb && has_statetable {
        kind = CellKind::Other;
    }
    Ok(CellDef {
        name,
        pins,
        kind,
        state_vars,
    })
}

struct PinBody {
    dir: Dir,
    function: Option<super::BoolExpr>,
    three_state: bool,
}

fn parse_pin_body(
    cur: &mut Cur,
    cell: &str,
    names: &[&[u8]],
    warnings: &mut Vec<String>,
) -> Result<PinBody> {
    let open = cur.line();
    let mut body = PinBody {
        dir: Dir::Input,
        function: None,
        three_state: false,
    };
    loop {
        match cur.stmt()? {
            Stmt::Attr(name, value) => match name {
                b"direction" => {
                    body.dir = match value {
                        b"output" => Dir::Output,
                        b"inout" => Dir::Inout,
                        b"internal" => Dir::Internal,
                        _ => Dir::Input,
                    }
                }
                b"function" => match parse_function(&String::from_utf8_lossy(value)) {
                    Ok(f) => body.function = Some(f),
                    Err(e) => warnings.push(format!(
                        "cell {cell}: pin {}: cannot parse function \"{}\": {e}",
                        names.first().map(|n| text(n)).unwrap_or_default(),
                        String::from_utf8_lossy(value)
                    )),
                },
                b"three_state" => body.three_state = true,
                _ => {}
            },
            // Nested groups: timing, internal_power, member pins of a bus, ...
            Stmt::Group(..) => cur.skip_body()?,
            Stmt::Complex => {}
            Stmt::End => break,
            Stmt::Eof => bail!(
                "unexpected end of file inside a pin group of cell ({cell}) opened at line {open}"
            ),
        }
    }
    Ok(body)
}

enum Stmt<'a> {
    /// `name : value ;`
    Attr(&'a [u8], &'a [u8]),
    /// `name ( args ) ;`
    Complex,
    /// `name ( args ) {` — the caller must consume or skip the body.
    Group(&'a [u8], Vec<&'a [u8]>),
    /// `}`
    End,
    Eof,
}

struct Cur<'a> {
    s: &'a [u8],
    p: usize,
}

impl<'a> Cur<'a> {
    fn line(&self) -> usize {
        memchr::memchr_iter(b'\n', &self.s[..self.p.min(self.s.len())]).count() + 1
    }

    fn peek(&self) -> Option<u8> {
        self.s.get(self.p).copied()
    }

    /// Skip whitespace, comments and backslash line continuations.
    fn skip_ws(&mut self) {
        let s = self.s;
        while self.p < s.len() {
            let c = s[self.p];
            if c.is_ascii_whitespace() {
                self.p += 1;
            } else if c == b'\\' && matches!(s.get(self.p + 1), Some(b'\n' | b'\r')) {
                self.p += 1;
            } else if c == b'/' && s.get(self.p + 1) == Some(&b'*') {
                self.p = match memchr::memmem::find(&s[self.p + 2..], b"*/") {
                    Some(i) => self.p + 2 + i + 2,
                    None => s.len(),
                };
            } else if c == b'/' && s.get(self.p + 1) == Some(&b'/') {
                self.p = match memchr::memchr(b'\n', &s[self.p..]) {
                    Some(i) => self.p + i,
                    None => s.len(),
                };
            } else {
                break;
            }
        }
    }

    /// Skip blanks on the current line only.
    fn skip_inline_ws(&mut self) {
        let s = self.s;
        while self.p < s.len() {
            let c = s[self.p];
            if c == b' ' || c == b'\t' {
                self.p += 1;
            } else if c == b'\\' && matches!(s.get(self.p + 1), Some(b'\n' | b'\r')) {
                self.p += 1;
                while matches!(self.peek(), Some(b'\n' | b'\r')) {
                    self.p += 1;
                }
            } else {
                break;
            }
        }
    }

    fn word(&mut self) -> &'a [u8] {
        let start = self.p;
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() || matches!(c, b'(' | b')' | b'{' | b'}' | b':' | b';' | b',' | b'"')
            {
                break;
            }
            self.p += 1;
        }
        &self.s[start..self.p]
    }

    fn stmt(&mut self) -> Result<Stmt<'a>> {
        loop {
            self.skip_ws();
            match self.peek() {
                None => return Ok(Stmt::Eof),
                Some(b'}') => {
                    self.p += 1;
                    return Ok(Stmt::End);
                }
                Some(b';') => {
                    self.p += 1;
                    continue;
                }
                _ => {}
            }
            let name = self.word();
            if name.is_empty() {
                bail!(
                    "unexpected '{}' at line {}",
                    self.s[self.p] as char,
                    self.line()
                );
            }
            self.skip_ws();
            return match self.peek() {
                Some(b':') => {
                    self.p += 1;
                    Ok(Stmt::Attr(name, self.value()))
                }
                Some(b'(') => {
                    let args = self.args()?;
                    self.skip_ws();
                    match self.peek() {
                        Some(b'{') => {
                            self.p += 1;
                            Ok(Stmt::Group(name, args))
                        }
                        Some(b';') => {
                            self.p += 1;
                            Ok(Stmt::Complex)
                        }
                        _ => Ok(Stmt::Complex),
                    }
                }
                _ => bail!(
                    "expected ':' or '(' after '{}' at line {}",
                    String::from_utf8_lossy(name),
                    self.line()
                ),
            };
        }
    }

    /// Value of a simple attribute; the cursor is just past the ':'.
    fn value(&mut self) -> &'a [u8] {
        self.skip_inline_ws();
        let s = self.s;
        let v = if self.peek() == Some(b'"') {
            let start = self.p + 1;
            let end = memchr::memchr(b'"', &s[start..]).map_or(s.len(), |i| start + i);
            self.p = (end + 1).min(s.len());
            &s[start..end]
        } else {
            let start = self.p;
            while let Some(c) = self.peek() {
                if matches!(c, b';' | b'\n' | b'}') {
                    break;
                }
                self.p += 1;
            }
            s[start..self.p].trim_ascii()
        };
        self.skip_inline_ws();
        if self.peek() == Some(b';') {
            self.p += 1;
        }
        v
    }

    /// Parenthesised argument list; the cursor is on the '('.
    fn args(&mut self) -> Result<Vec<&'a [u8]>> {
        let open = self.line();
        self.p += 1;
        let s = self.s;
        let mut out = Vec::new();
        loop {
            self.skip_ws();
            match self.peek() {
                None => bail!("unterminated '(' opened at line {open}"),
                Some(b')') => {
                    self.p += 1;
                    return Ok(out);
                }
                Some(b',') => self.p += 1,
                Some(b'"') => {
                    let start = self.p + 1;
                    let end = memchr::memchr(b'"', &s[start..]).map_or(s.len(), |i| start + i);
                    out.push(s[start..end].trim_ascii());
                    self.p = (end + 1).min(s.len());
                }
                Some(_) => {
                    let start = self.p;
                    while let Some(c) = self.peek() {
                        if matches!(c, b',' | b')' | b'"') {
                            break;
                        }
                        self.p += 1;
                    }
                    out.push(s[start..self.p].trim_ascii());
                }
            }
        }
    }

    /// Skip the rest of a group body; the cursor is just past its '{'.
    fn skip_body(&mut self) -> Result<()> {
        let open = self.line();
        let s = self.s;
        let mut depth = 1usize;
        let mut p = self.p;
        while p < s.len() {
            match s[p] {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        self.p = p + 1;
                        return Ok(());
                    }
                }
                b'"' => {
                    p = memchr::memchr(b'"', &s[p + 1..]).map_or(s.len(), |i| p + 1 + i);
                }
                b'/' if s.get(p + 1) == Some(&b'*') => {
                    p = memchr::memmem::find(&s[p + 2..], b"*/").map_or(s.len(), |i| p + 2 + i + 1);
                }
                _ => {}
            }
            p += 1;
        }
        self.p = s.len();
        bail!("unexpected end of file: group opened at line {open} is never closed")
    }
}

//! Byte-level lexer for structural Verilog.
//!
//! Works on raw bytes (no UTF-8 validation) and returns sub-slices of the
//! source, so lexing a memory-mapped netlist allocates nothing.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tok<'a> {
    /// Plain identifier or keyword.
    Ident(&'a [u8]),
    /// Escaped identifier `\name `, without the backslash. Never a keyword.
    Escaped(&'a [u8]),
    /// Number or sized literal, e.g. `12`, `1'b0`, `4'hF`.
    Number(&'a [u8]),
    /// String literal without the quotes.
    Str(&'a [u8]),
    Punct(u8),
    Eof,
}

impl<'a> Tok<'a> {
    /// The name carried by an identifier token of either kind.
    pub fn name(self) -> Option<&'a [u8]> {
        match self {
            Tok::Ident(n) | Tok::Escaped(n) => Some(n),
            _ => None,
        }
    }
}

pub struct Lexer<'a> {
    pub src: &'a [u8],
    pub pos: usize,
    /// Start offset of the token most recently returned by `next`.
    pub tok_start: usize,
}

#[inline]
fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_' || c == b'$'
}

#[inline]
fn is_ident_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'$'
}

#[inline]
fn is_space(c: u8) -> bool {
    c == b' ' || c == b'\n' || c == b'\t' || c == b'\r' || c == 0x0c || c == 0x0b
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a [u8]) -> Self {
        Lexer {
            src,
            pos: 0,
            tok_start: 0,
        }
    }

    /// Skip whitespace, comments, `(* attributes *)` and compiler directives.
    fn skip_trivia(&mut self) {
        let s = self.src;
        let n = s.len();
        let mut p = self.pos;
        loop {
            while p < n && is_space(s[p]) {
                p += 1;
            }
            if p >= n {
                break;
            }
            let next = if p + 1 < n { s[p + 1] } else { 0 };
            match s[p] {
                b'/' if next == b'/' => {
                    p = memchr::memchr(b'\n', &s[p..]).map_or(n, |i| p + i + 1);
                }
                b'/' if next == b'*' => {
                    p = memchr::memmem::find(&s[p + 2..], b"*/").map_or(n, |i| p + 2 + i + 2);
                }
                b'(' if next == b'*' && s.get(p + 2) != Some(&b')') => {
                    p = memchr::memmem::find(&s[p + 2..], b"*)").map_or(n, |i| p + 2 + i + 2);
                }
                b'`' => {
                    p = memchr::memchr(b'\n', &s[p..]).map_or(n, |i| p + i + 1);
                }
                _ => break,
            }
        }
        self.pos = p;
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Tok<'a> {
        self.skip_trivia();
        let s = self.src;
        let n = s.len();
        let start = self.pos;
        self.tok_start = start;
        if start >= n {
            return Tok::Eof;
        }
        let c = s[start];
        let mut p = start + 1;
        if is_ident_start(c) {
            while p < n && is_ident_byte(s[p]) {
                p += 1;
            }
            self.pos = p;
            return Tok::Ident(&s[start..p]);
        }
        if c == b'\\' {
            while p < n && !is_space(s[p]) {
                p += 1;
            }
            self.pos = p;
            return Tok::Escaped(&s[start + 1..p]);
        }
        if c.is_ascii_digit() || c == b'\'' {
            while p < n {
                let d = s[p];
                if d.is_ascii_alphanumeric() || d == b'_' || d == b'\'' || d == b'?' {
                    p += 1;
                } else if d == b'.' && p + 1 < n && s[p + 1].is_ascii_digit() {
                    p += 1;
                } else {
                    break;
                }
            }
            self.pos = p;
            return Tok::Number(&s[start..p]);
        }
        if c == b'"' {
            while p < n && s[p] != b'"' {
                if s[p] == b'\\' {
                    p += 1;
                }
                p += 1;
            }
            let end = p.min(n);
            self.pos = (end + 1).min(n);
            return Tok::Str(&s[start + 1..end]);
        }
        self.pos = p;
        Tok::Punct(c)
    }

    pub fn peek(&mut self) -> Tok<'a> {
        let (pos, start) = (self.pos, self.tok_start);
        let t = self.next();
        self.pos = pos;
        self.tok_start = start;
        t
    }

    /// Advance just past the next `;` that is not inside a comment, string or
    /// escaped identifier. Returns false (and moves to the end) if there is none.
    pub fn skip_past_semicolon(&mut self) -> bool {
        let s = self.src;
        let n = s.len();
        let mut p = self.pos;
        while p < n {
            // Only these four bytes can start something that hides a ';'.
            let Some(i) = memchr::memchr3(b';', b'\\', b'"', &s[p..]) else {
                break;
            };
            // A comment may start before the hit; look for '/' in the gap.
            let hit = p + i;
            if let Some(j) = memchr::memchr(b'/', &s[p..hit]) {
                let q = p + j;
                let next = s[q + 1];
                if next == b'/' {
                    p = memchr::memchr(b'\n', &s[q..]).map_or(n, |k| q + k + 1);
                    continue;
                }
                if next == b'*' {
                    p = memchr::memmem::find(&s[q + 2..], b"*/").map_or(n, |k| q + 2 + k + 2);
                    continue;
                }
                // A lone '/' (e.g. inside an escaped name already passed): move on.
                p = q + 1;
                continue;
            }
            match s[hit] {
                b';' => {
                    self.pos = hit + 1;
                    return true;
                }
                b'\\' => {
                    p = hit + 1;
                    while p < n && !is_space(s[p]) {
                        p += 1;
                    }
                }
                _ => {
                    // string
                    p = hit + 1;
                    while p < n && s[p] != b'"' {
                        if s[p] == b'\\' {
                            p += 1;
                        }
                        p += 1;
                    }
                    p = (p + 1).min(n);
                }
            }
        }
        self.pos = n;
        false
    }
}

/// 1-based line number of byte offset `pos`.
pub fn line_of(src: &[u8], pos: usize) -> usize {
    memchr::memchr_iter(b'\n', &src[..pos.min(src.len())]).count() + 1
}

//! First pass over the netlist: where each module is, and which cell/module
//! types are instantiated anywhere. Module bodies are not parsed here.

use std::fmt;

use anyhow::{Result, bail};
use rustc_hash::{FxHashMap, FxHashSet};

use super::lexer::{Lexer, Tok, line_of};

pub struct ModuleEntry<'a> {
    pub name: &'a [u8],
    /// Index of the source file this module came from.
    pub source: u32,
    /// The whole source file.
    pub src: &'a [u8],
    /// Offset just after the module name (start of the port list).
    pub start: usize,
    /// Offset of the `endmodule` keyword.
    pub end: usize,
}

impl<'a> ModuleEntry<'a> {
    /// Text from the port list up to (not including) `endmodule`.
    pub fn body(&self) -> &'a [u8] {
        &self.src[self.start..self.end]
    }
}

pub struct ModuleIndex<'a> {
    pub modules: Vec<ModuleEntry<'a>>,
    pub warnings: Vec<String>,
    by_name: FxHashMap<&'a [u8], u32>,
    instantiated: FxHashSet<&'a [u8]>,
}

impl fmt::Debug for ModuleIndex<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ModuleIndex({} modules)", self.modules.len())
    }
}

/// Keywords that start a statement which is not an instantiation.
pub(crate) fn is_statement_keyword(w: &[u8]) -> bool {
    matches!(
        w,
        b"input"
            | b"output"
            | b"inout"
            | b"wire"
            | b"tri"
            | b"tri0"
            | b"tri1"
            | b"wand"
            | b"wor"
            | b"triand"
            | b"trior"
            | b"trireg"
            | b"supply0"
            | b"supply1"
            | b"reg"
            | b"logic"
            | b"assign"
            | b"parameter"
            | b"localparam"
            | b"defparam"
            | b"specify"
            | b"genvar"
            | b"integer"
            | b"real"
            | b"time"
            | b"event"
    )
}

impl<'a> ModuleIndex<'a> {
    pub fn build(sources: &[&'a [u8]]) -> Result<Self> {
        let mut idx = ModuleIndex {
            modules: Vec::new(),
            warnings: Vec::new(),
            by_name: FxHashMap::default(),
            instantiated: FxHashSet::default(),
        };
        for (si, src) in sources.iter().enumerate() {
            idx.scan(si as u32, src)?;
        }
        Ok(idx)
    }

    fn scan(&mut self, source: u32, src: &'a [u8]) -> Result<()> {
        let mut lx = Lexer::new(src);
        loop {
            match lx.next() {
                Tok::Eof => return Ok(()),
                Tok::Ident(b"module") | Tok::Ident(b"macromodule") => {}
                _ => continue,
            }
            let kw_pos = lx.tok_start;
            let Some(name) = lx.next().name() else {
                bail!("expected a module name at line {}", line_of(src, lx.tok_start));
            };
            let start = lx.pos;
            let unterminated = |name: &[u8]| {
                anyhow::anyhow!(
                    "module {} (line {}) has no endmodule",
                    String::from_utf8_lossy(name),
                    line_of(src, kw_pos)
                )
            };
            // Header: `( ports ) ;`
            if !lx.skip_past_semicolon() {
                return Err(unterminated(name));
            }
            let end = loop {
                match lx.next() {
                    Tok::Ident(b"endmodule") => break lx.tok_start,
                    Tok::Eof => return Err(unterminated(name)),
                    Tok::Ident(b"specify") => loop {
                        match lx.next() {
                            Tok::Ident(b"endspecify") => break,
                            Tok::Eof => return Err(unterminated(name)),
                            _ => {}
                        }
                    },
                    Tok::Punct(b';') => {}
                    t => {
                        if let Some(w) = t.name() {
                            let keyword = matches!(t, Tok::Ident(_)) && is_statement_keyword(w);
                            if !keyword {
                                self.instantiated.insert(w);
                            }
                        }
                        if !lx.skip_past_semicolon() {
                            return Err(unterminated(name));
                        }
                    }
                }
            };
            let id = self.modules.len() as u32;
            if self.by_name.contains_key(name) {
                self.warnings.push(format!(
                    "module {} is defined more than once; using the first definition (duplicate at line {})",
                    String::from_utf8_lossy(name),
                    line_of(src, kw_pos)
                ));
            } else {
                self.by_name.insert(name, id);
            }
            self.modules.push(ModuleEntry {
                name,
                source,
                src,
                start,
                end,
            });
        }
    }

    pub fn find(&self, name: &[u8]) -> Option<u32> {
        self.by_name.get(name).copied()
    }

    /// True if some module instantiates a cell or module of this type name.
    pub fn is_instantiated(&self, name: &[u8]) -> bool {
        self.instantiated.contains(name)
    }

    /// Modules that nothing instantiates, in file order.
    pub fn top_candidates(&self) -> Vec<u32> {
        (0..self.modules.len() as u32)
            .filter(|&i| {
                let name = self.modules[i as usize].name;
                self.by_name.get(name) == Some(&i) && !self.instantiated.contains(name)
            })
            .collect()
    }
}

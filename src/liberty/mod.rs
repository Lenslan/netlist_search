//! Liberty (.lib) cell library: the subset needed to know each cell's pins,
//! boolean functions and whether it is sequential.

pub mod func;
mod parser;

use std::path::Path;

use anyhow::{Context, Result};
use rustc_hash::FxHashMap;

pub use func::BoolExpr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dir {
    Input,
    Output,
    Inout,
    Internal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellKind {
    /// Purely combinational (or a macro whose outputs carry no function).
    Comb,
    /// Has an `ff` / `ff_bank` group.
    Ff,
    /// Has a `latch` / `latch_bank` group.
    Latch,
    /// Sequential behaviour described only by a `statetable` (e.g. clock gates).
    Other,
}

#[derive(Debug, Clone)]
pub struct PinDef {
    pub name: String,
    pub dir: Dir,
    /// Boolean function of an output pin, if the library gives one.
    pub function: Option<BoolExpr>,
    pub three_state: bool,
    /// Declared with a `bus` group: connects to several net bits.
    pub is_bus: bool,
}

#[derive(Debug, Clone)]
pub struct CellDef {
    pub name: String,
    pub pins: Vec<PinDef>,
    pub kind: CellKind,
    /// Names of the state variable and its complement, e.g. `("IQ", "IQN")`.
    pub state_vars: Option<(String, String)>,
}

impl CellDef {
    pub fn pin(&self, name: &[u8]) -> Option<&PinDef> {
        self.pins.iter().find(|p| p.name.as_bytes() == name)
    }

    pub fn is_sequential(&self) -> bool {
        self.kind != CellKind::Comb
    }
}

#[derive(Debug, Default)]
pub struct CellLib {
    cells: FxHashMap<Vec<u8>, CellDef>,
    /// Non-fatal problems met while loading (e.g. an unparsable function).
    pub warnings: Vec<String>,
}

impl CellLib {
    pub fn new() -> Self {
        Self::default()
    }

    /// Load a `.lib` file, adding its cells to the library.
    pub fn load_file(&mut self, path: &Path) -> Result<()> {
        let file = std::fs::File::open(path)
            .with_context(|| format!("cannot open lib file {}", path.display()))?;
        // SAFETY: the mapping is read-only and dropped before this function returns.
        let map = unsafe { memmap2::Mmap::map(&file) }
            .with_context(|| format!("cannot map lib file {}", path.display()))?;
        self.load_bytes(&map)
            .with_context(|| format!("in lib file {}", path.display()))
    }

    pub fn load_str(&mut self, text: &str) -> Result<()> {
        self.load_bytes(text.as_bytes())
    }

    pub fn load_bytes(&mut self, text: &[u8]) -> Result<()> {
        let cells = parser::parse_library(text, &mut self.warnings)?;
        for c in cells {
            self.cells.entry(c.name.as_bytes().to_vec()).or_insert(c);
        }
        Ok(())
    }

    pub fn get(&self, name: &[u8]) -> Option<&CellDef> {
        self.cells.get(name)
    }

    pub fn len(&self) -> usize {
        self.cells.len()
    }

    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BASIC: &str = include_str!("../../tests/fixtures/basic.lib");

    fn basic() -> CellLib {
        let mut lib = CellLib::new();
        lib.load_str(BASIC).expect("basic.lib parses");
        lib
    }

    fn eval(cell: &CellDef, pin: &str, on: &[&str]) -> bool {
        cell.pin(pin.as_bytes())
            .unwrap()
            .function
            .as_ref()
            .unwrap_or_else(|| panic!("{}.{pin} has no function", cell.name))
            .eval(&|v| on.contains(&v))
    }

    #[test]
    fn loads_every_cell_of_the_fixture() {
        let lib = basic();
        assert_eq!(lib.len(), 29);
        assert!(lib.warnings.is_empty(), "{:?}", lib.warnings);
        assert!(lib.get(b"NOPE").is_none());
    }

    #[test]
    fn inverter_pins_and_function() {
        let lib = basic();
        let c = lib.get(b"INVX1").unwrap();
        assert_eq!(c.kind, CellKind::Comb);
        assert_eq!(c.pins.len(), 2);
        assert_eq!(c.pin(b"A").unwrap().dir, Dir::Input);
        assert_eq!(c.pin(b"Y").unwrap().dir, Dir::Output);
        assert!(c.pin(b"A").unwrap().function.is_none());
        assert!(eval(c, "Y", &[]));
        assert!(!eval(c, "Y", &["A"]));
    }

    #[test]
    fn nested_timing_groups_do_not_leak_pins() {
        let lib = basic();
        let names: Vec<_> = lib.get(b"INVX1").unwrap().pins.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, ["A", "Y"]);
    }

    #[test]
    fn one_pin_group_may_declare_several_pins() {
        let lib = basic();
        let c = lib.get(b"AND2X1").unwrap();
        assert_eq!(c.pin(b"A").unwrap().dir, Dir::Input);
        assert_eq!(c.pin(b"B").unwrap().dir, Dir::Input);
        assert!(eval(c, "Y", &["A", "B"]));
        assert!(!eval(c, "Y", &["A"]));
    }

    #[test]
    fn mux_and_aoi_functions() {
        let lib = basic();
        let m = lib.get(b"MUX2X1").unwrap();
        assert!(eval(m, "Y", &["S", "B"]));
        assert!(!eval(m, "Y", &["S", "A"]));
        assert!(eval(m, "Y", &["A"]));
        let a = lib.get(b"AOI22X1").unwrap();
        assert!(eval(a, "Y", &["A0", "B0"]));
        assert!(!eval(a, "Y", &["A0", "A1"]));
        assert!(!eval(a, "Y", &["B0", "B1"]));
    }

    #[test]
    fn cell_with_two_outputs() {
        let lib = basic();
        let c = lib.get(b"ADDFX1").unwrap();
        assert!(eval(c, "S", &["A", "B", "CI"]));
        assert!(!eval(c, "S", &["A", "B"]));
        assert!(eval(c, "CO", &["A", "CI"]));
        assert!(!eval(c, "CO", &["CI"]));
    }

    #[test]
    fn tie_cells_are_constants_even_without_semicolon() {
        let lib = basic();
        assert_eq!(
            lib.get(b"TIEHI").unwrap().pin(b"Y").unwrap().function,
            Some(BoolExpr::Const(true))
        );
        assert_eq!(
            lib.get(b"TIELO").unwrap().pin(b"Y").unwrap().function,
            Some(BoolExpr::Const(false))
        );
    }

    #[test]
    fn flip_flop_is_sequential_with_state_vars() {
        let lib = basic();
        let c = lib.get(b"DFFRX1").unwrap();
        assert_eq!(c.kind, CellKind::Ff);
        assert_eq!(c.state_vars, Some(("IQ".into(), "IQN".into())));
        assert_eq!(c.pin(b"Q").unwrap().function, Some(BoolExpr::Var("IQ".into())));
        assert_eq!(c.pin(b"QN").unwrap().function, Some(BoolExpr::Var("IQN".into())));
        assert_eq!(c.pin(b"CK").unwrap().dir, Dir::Input);
    }

    #[test]
    fn quoted_state_var_names_and_test_cell_is_ignored() {
        let lib = basic();
        let c = lib.get(b"SDFFX1").unwrap();
        assert_eq!(c.kind, CellKind::Ff);
        assert_eq!(c.state_vars, Some(("IQ".into(), "IQN".into())));
        assert!(c.pin(b"BOGUS").is_none());
        assert_eq!(c.pins.len(), 5);
    }

    #[test]
    fn latch_three_state_and_statetable_cells() {
        let lib = basic();
        assert_eq!(lib.get(b"LATX1").unwrap().kind, CellKind::Latch);
        let t = lib.get(b"TBUFX1").unwrap();
        assert!(t.pin(b"Y").unwrap().three_state);
        assert!(!t.pin(b"A").unwrap().three_state);
        let g = lib.get(b"ICGX1").unwrap();
        assert_eq!(g.kind, CellKind::Other);
        assert!(g.pin(b"GCK").unwrap().function.is_none());
    }

    #[test]
    fn macro_bus_pins() {
        let lib = basic();
        let c = lib.get(b"RAM16X4").unwrap();
        let q = c.pin(b"Q").unwrap();
        assert!(q.is_bus);
        assert_eq!(q.dir, Dir::Output);
        assert!(q.function.is_none());
        assert_eq!(c.pin(b"A").unwrap().dir, Dir::Input);
        assert!(c.pin(b"A[0]").is_none(), "bus member pins are not separate pins");
        assert!(c.pin(b"VDD").is_none(), "pg_pin is not a signal pin");
        assert!(!c.pin(b"CLK").unwrap().is_bus);
    }

    #[test]
    fn several_libraries_accumulate() {
        let mut lib = basic();
        lib.load_str(
            "library (extra) { cell (FOO) { pin (Z) { direction : output; function : \"0\"; } } }",
        )
        .unwrap();
        assert_eq!(lib.len(), 30);
        assert!(lib.get(b"FOO").is_some());
    }

    #[test]
    fn comments_and_line_comments_are_skipped() {
        let mut lib = CellLib::new();
        lib.load_str(
            "/* head */ library (x) { // note\n cell (C) { /* { */ pin (A) { direction : input; } } }",
        )
        .unwrap();
        assert_eq!(lib.get(b"C").unwrap().pins.len(), 1);
    }

    #[test]
    fn truncated_file_reports_the_open_group_and_line() {
        let mut lib = CellLib::new();
        let err = lib
            .load_str("library (x) {\n  cell (C) {\n    pin (A) { direction : input; }\n")
            .unwrap_err()
            .to_string();
        assert!(err.contains("line"), "{err}");
        assert!(err.contains("cell"), "{err}");
    }

    #[test]
    fn unparsable_function_becomes_a_warning_not_an_error() {
        let mut lib = CellLib::new();
        lib.load_str(
            "library (x) { cell (C) { pin (Y) { direction : output; function : \"A &\"; } } }",
        )
        .unwrap();
        assert!(lib.get(b"C").unwrap().pin(b"Y").unwrap().function.is_none());
        assert_eq!(lib.warnings.len(), 1);
        assert!(lib.warnings[0].contains("C"), "{:?}", lib.warnings);
    }
}

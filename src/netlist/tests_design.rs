use super::design::*;
use super::index::ModuleIndex;
use crate::liberty::{CellLib, Dir};

const HIER: &str = "
module leaf (a, y); input a; output y; INVX1 U1 (.A(a), .Y(y)); endmodule
module mid (a, y);
  input a; output y; wire w;
  wire [3:0] cnt;
  wire \\odd[1] ;
  leaf u_l0 (.a(a), .y(w));
  leaf u_l1 (.a(w), .y(y));
endmodule
module wrap (a); input a; leaf u_only (.a(a), .y()); endmodule
module top (in, out);
  input in; output out; wire t;
  mid u_a (.a(in), .y(t));
  mid u_b (.a(t), .y(out));
  mid \\u_x/u_y (.a(in), .y());
  wrap u_w (.a(in));
  INVX1 U7 (.A(in), .Y());
  mystery_cell u_unk (.p(in));
  and g0 (t, in, in);
endmodule
";

const ORPHAN: &str = "module other (a); input a; leaf u_q (.a(a), .y()); endmodule";

fn lib() -> &'static CellLib {
    let mut lib = CellLib::new();
    lib.load_str(include_str!("../../tests/fixtures/basic.lib")).unwrap();
    Box::leak(Box::new(lib))
}

fn design(srcs: &[&str]) -> Design<'static> {
    let leaked: Vec<&'static [u8]> = srcs
        .iter()
        .map(|s| &*Box::leak(s.to_string().into_boxed_str()).as_bytes())
        .collect();
    Design::new(ModuleIndex::build(&leaked).unwrap(), lib())
}

fn resolved(d: &Design, top: Option<&str>, path: &str) -> String {
    let p = d.resolve(top, path).unwrap_or_else(|e| panic!("resolve {path:?}: {e:#}"));
    format!(
        "{}|{}",
        d.path_string(&p),
        String::from_utf8_lossy(d.index.modules[p.module() as usize].name)
    )
}

fn resolve_err(d: &Design, top: Option<&str>, path: &str) -> String {
    match d.resolve(top, path) {
        Ok(p) => panic!("{path:?} unexpectedly resolved to {}", d.path_string(&p)),
        Err(e) => format!("{e:#}"),
    }
}

#[test]
fn cell_types_are_classified() {
    let d = design(&[HIER]);
    assert!(matches!(d.cell_ref(b"INVX1"), CellRef::Lib(_)));
    assert!(matches!(d.cell_ref(b"leaf"), CellRef::Module(0)));
    assert!(matches!(d.cell_ref(b"mystery_cell"), CellRef::Unknown));
    assert!(matches!(d.cell_ref(b"and"), CellRef::Builtin(Builtin::And)));
}

#[test]
fn path_from_top_with_or_without_the_top_name() {
    let d = design(&[HIER]);
    assert_eq!(resolved(&d, None, "u_a/u_l1"), "u_a/u_l1|leaf");
    assert_eq!(resolved(&d, None, "top/u_a/u_l1"), "u_a/u_l1|leaf");
    assert_eq!(resolved(&d, None, "/top/u_a/"), "u_a|mid");
}

#[test]
fn empty_path_is_the_top_module() {
    let d = design(&[HIER]);
    assert_eq!(resolved(&d, None, ""), "|top");
    assert_eq!(resolved(&d, None, "top"), "|top");
}

#[test]
fn dots_work_as_separators() {
    let d = design(&[HIER]);
    assert_eq!(resolved(&d, None, "u_b.u_l0"), "u_b/u_l0|leaf");
}

#[test]
fn explicit_top() {
    let d = design(&[HIER, ORPHAN]);
    assert_eq!(resolved(&d, Some("top"), "u_b"), "u_b|mid");
    assert_eq!(resolved(&d, Some("other"), "u_q"), "u_q|leaf");
    assert!(resolve_err(&d, Some("nope"), "u_b").contains("nope"));
}

#[test]
fn flattened_instance_names_use_the_longest_match() {
    let d = design(&[HIER]);
    assert_eq!(resolved(&d, None, "u_x/u_y/u_l0"), "u_x/u_y/u_l0|leaf");
    assert_eq!(resolved(&d, None, "u_x/u_y"), "u_x/u_y|mid");
}

#[test]
fn unique_suffix_is_accepted() {
    let d = design(&[HIER]);
    assert_eq!(resolved(&d, None, "u_only"), "u_w/u_only|leaf");
}

#[test]
fn ambiguous_suffix_lists_the_candidates() {
    let d = design(&[HIER]);
    let e = resolve_err(&d, None, "u_l1");
    assert!(e.contains("u_a/u_l1"), "{e}");
    assert!(e.contains("u_b/u_l1"), "{e}");
    assert!(e.contains("u_x/u_y/u_l1"), "{e}");
}

#[test]
fn unknown_instance_suggests_neighbours() {
    let d = design(&[HIER]);
    let e = resolve_err(&d, None, "u_a/u_l9");
    assert!(e.contains("u_l9"), "{e}");
    assert!(e.contains("u_l0") && e.contains("u_l1"), "{e}");
}

#[test]
fn path_to_a_library_cell_is_rejected_with_a_reason() {
    let d = design(&[HIER]);
    let e = resolve_err(&d, None, "u_a/u_l0/U1");
    assert!(e.contains("INVX1"), "{e}");
}

#[test]
fn several_tops_are_disambiguated_by_the_path() {
    let d = design(&[HIER, ORPHAN]);
    assert_eq!(resolved(&d, None, "u_q"), "u_q|leaf");
    assert_eq!(resolved(&d, None, "u_a"), "u_a|mid");
    let e = resolve_err(&d, None, "");
    assert!(e.contains("--top"), "{e}");
    assert!(e.contains("top") && e.contains("other"), "{e}");
}

#[test]
fn pin_info_for_module_library_and_unknown_cells() {
    let d = design(&[HIER]);
    let top = d.module(d.index.find(b"top").unwrap()).unwrap();
    let find = |inst: &str, pin: &str| {
        let i = top.find_inst(inst.as_bytes()).unwrap();
        let c = top
            .inst_conns(i)
            .find(|&c| top.conn_pin(c) == Some(pin.as_bytes()))
            .unwrap();
        d.pin_info(top, i, c)
    };
    match find("u_a", "a") {
        PinInfo::ModulePort { module, port, dir } => {
            assert_eq!(module, d.index.find(b"mid").unwrap());
            assert_eq!(port, 0);
            assert_eq!(dir, Dir::Input);
        }
        other => panic!("{other:?}"),
    }
    assert!(matches!(find("u_a", "y"), PinInfo::ModulePort { dir: Dir::Output, .. }));
    match find("U7", "Y") {
        PinInfo::LibPin { cell, pin } => {
            assert_eq!(cell.name, "INVX1");
            assert_eq!(pin.dir, Dir::Output);
        }
        other => panic!("{other:?}"),
    }
    assert!(matches!(find("u_unk", "p"), PinInfo::Unknown));
}

#[test]
fn positional_pins_of_builtin_gates() {
    let d = design(&[HIER]);
    let top = d.module(d.index.find(b"top").unwrap()).unwrap();
    let g = top.find_inst(b"g0").unwrap();
    let conns: Vec<u32> = top.inst_conns(g).collect();
    assert!(matches!(d.pin_info(top, g, conns[0]), PinInfo::BuiltinPin { index: 0, .. }));
    assert!(matches!(d.pin_info(top, g, conns[2]), PinInfo::BuiltinPin { index: 2, .. }));
}

#[test]
fn wire_lookup_scalar_bit_range_and_whole_bus() {
    let d = design(&[HIER]);
    let m = d.module(d.index.find(b"mid").unwrap()).unwrap();
    let names = |w: &str| -> Vec<String> {
        d.find_wire_bits(m, w)
            .unwrap_or_else(|e| panic!("{w}: {e:#}"))
            .iter()
            .map(|&b| m.bit_name(b))
            .collect()
    };
    assert_eq!(names("w"), ["w"]);
    assert_eq!(names("cnt[3]"), ["cnt[3]"]);
    assert_eq!(names("cnt"), ["cnt[3]", "cnt[2]", "cnt[1]", "cnt[0]"]);
    assert_eq!(names("cnt[2:1]"), ["cnt[2]", "cnt[1]"]);
    assert_eq!(names("odd[1]"), ["odd[1]"]);
    assert_eq!(names("\\odd[1]"), ["odd[1]"]);
}

#[test]
fn missing_wire_explains_what_exists() {
    let d = design(&[HIER]);
    let m = d.module(d.index.find(b"mid").unwrap()).unwrap();
    let e = format!("{:#}", d.find_wire_bits(m, "cnt[7]").unwrap_err());
    assert!(e.contains("[3:0]"), "{e}");
    let e = format!("{:#}", d.find_wire_bits(m, "cmt").unwrap_err());
    assert!(e.contains("cnt"), "{e}");
}

#[test]
fn module_parse_errors_surface_when_the_module_is_used() {
    let d = design(&["module bad (); INVX1 U1 (.A(a) .Y(b)); endmodule"]);
    let e = format!("{:#}", d.module(0).unwrap_err());
    assert!(e.contains("bad"), "{e}");
    // The error is remembered, not re-parsed.
    assert!(d.module(0).is_err());
}

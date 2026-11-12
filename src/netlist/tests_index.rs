use super::index::*;

fn names(idx: &ModuleIndex) -> Vec<String> {
    idx.modules
        .iter()
        .map(|m| String::from_utf8_lossy(m.name).into_owned())
        .collect()
}

const TWO: &[u8] = b"module a (x); input x; endmodule
// module fake ();
/* module fake2 (); endmodule */
module top (p);
  input p;
  wire w;
  assign w = p;
  a u1 (.x(p));
  INVX1 U2 (.A(p));
endmodule
";

#[test]
fn finds_modules_and_ignores_commented_ones() {
    let idx = ModuleIndex::build(&[TWO]).unwrap();
    assert_eq!(names(&idx), ["a", "top"]);
    assert_eq!(idx.find(b"top"), Some(1));
    assert_eq!(idx.find(b"fake"), None);
}

#[test]
fn body_excludes_endmodule_and_starts_after_the_name() {
    let idx = ModuleIndex::build(&[TWO]).unwrap();
    let body = String::from_utf8_lossy(idx.modules[0].body()).into_owned();
    assert!(body.trim_start().starts_with("(x);"), "{body:?}");
    assert!(body.contains("input x;"));
    assert!(!body.contains("endmodule"));
}

#[test]
fn instantiated_types_exclude_declaration_keywords() {
    let idx = ModuleIndex::build(&[TWO]).unwrap();
    assert!(idx.is_instantiated(b"a"));
    assert!(idx.is_instantiated(b"INVX1"));
    assert!(!idx.is_instantiated(b"top"));
    assert!(!idx.is_instantiated(b"wire"));
    assert!(!idx.is_instantiated(b"assign"));
    assert!(!idx.is_instantiated(b"input"));
}

#[test]
fn top_candidates_are_the_uninstantiated_modules() {
    let idx = ModuleIndex::build(&[TWO]).unwrap();
    assert_eq!(idx.top_candidates(), [1]);
}

#[test]
fn several_sources_share_one_index() {
    let a: &[u8] = b"module leaf (); endmodule";
    let b: &[u8] = b"module root (); leaf u (); endmodule";
    let idx = ModuleIndex::build(&[a, b]).unwrap();
    assert_eq!(names(&idx), ["leaf", "root"]);
    assert_eq!(idx.top_candidates(), [1]);
    assert_eq!(idx.modules[1].source, 1);
}

#[test]
fn escaped_module_names_and_parameterised_instances() {
    let src: &[u8] = b"module \\weird/name (a); input a; endmodule
module t (); FOO #(.W(4)) u0 (.a(1'b0)); \\weird/name u1 (.a(1'b1)); endmodule";
    let idx = ModuleIndex::build(&[src]).unwrap();
    assert_eq!(names(&idx), ["weird/name", "t"]);
    assert!(idx.is_instantiated(b"FOO"));
    assert!(idx.is_instantiated(b"weird/name"));
    assert_eq!(idx.top_candidates(), [1]);
}

#[test]
fn duplicate_module_names_keep_the_first_and_warn() {
    let src: &[u8] = b"module d (a); input a; endmodule module d (); endmodule";
    let idx = ModuleIndex::build(&[src]).unwrap();
    assert_eq!(idx.modules.len(), 2);
    assert_eq!(idx.find(b"d"), Some(0));
    assert_eq!(idx.warnings.len(), 1);
}

#[test]
fn missing_endmodule_is_an_error_naming_the_module() {
    let src: &[u8] = b"module broken (a);\n input a;\n";
    let err = ModuleIndex::build(&[src]).unwrap_err().to_string();
    assert!(err.contains("broken"), "{err}");
    assert!(err.contains("endmodule"), "{err}");
}

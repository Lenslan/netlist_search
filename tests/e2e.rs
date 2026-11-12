//! End-to-end tests of the endpoint forms: netlist in, readable logic out.

use std::process::Command;

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn run(netlists: &[&str], extra: &[&str]) -> String {
    let lib = fixture("basic.lib");
    let files: Vec<String> = netlists.iter().map(|n| fixture(n)).collect();
    let mut args: Vec<&str> = vec!["--lib", &lib, "--netlist"];
    args.extend(files.iter().map(String::as_str));
    args.extend_from_slice(extra);
    let out = Command::new(env!("CARGO_BIN_EXE_netlist_search"))
        .args(&args)
        .output()
        .expect("tool runs");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{stderr}");
    String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n")
}

/// The `endpoint:` line of the wire called `wire`.
fn endpoint_of(report: &str, wire: &str) -> String {
    let mut lines = report.lines();
    while let Some(l) = lines.next() {
        let mut words = l.split_whitespace();
        if words.next().is_some_and(|d| d.starts_with('d')) && words.next() == Some(wire) {
            for l in lines.by_ref() {
                if let Some(e) = l.trim().strip_prefix("endpoint:") {
                    return e.trim().to_string();
                }
                if !l.starts_with("        ") {
                    break;
                }
            }
            panic!("wire {wire} has no endpoint line in:\n{report}");
        }
    }
    panic!("wire {wire} not found in:\n{report}");
}

#[test]
fn grammar_example_bus_compare_from_and_gates() {
    let r = run(&["grammar.v"], &["--wire", "eq5"]);
    assert_eq!(endpoint_of(&r, "eq5"), "cnt[3:0] == 5");
}

#[test]
fn grammar_example_bus_compare_does_not_depend_on_the_gate_structure() {
    let r = run(&["grammar.v"], &["--wire", "eq5_alt"]);
    assert_eq!(endpoint_of(&r, "eq5_alt"), "cnt[3:0] == 5");
}

#[test]
fn grammar_example_mux_from_and_or_gates() {
    let r = run(&["grammar.v"], &["--wire", "mux_y"]);
    assert_eq!(endpoint_of(&r, "mux_y"), "sel ? a : b");
}

#[test]
fn grammar_example_mux_from_an_aoi_cell() {
    let r = run(&["grammar.v"], &["--wire", "mux_alt"]);
    assert_eq!(endpoint_of(&r, "mux_alt"), "sel ? a : b");
    assert_eq!(endpoint_of(&r, "k2"), "sel ? !a : !b");
}

#[test]
fn radix_changes_how_constants_are_written() {
    let r = run(&["grammar.v"], &["--wire", "eq5", "--radix", "bin"]);
    assert_eq!(endpoint_of(&r, "eq5"), "cnt[3:0] == 4'b0101");
    let r = run(&["grammar.v"], &["--wire", "eq5", "--radix", "hex"]);
    assert_eq!(endpoint_of(&r, "eq5"), "cnt[3:0] == 4'h5");
}

#[test]
fn fsm_branch_conditions_are_named_by_state_value() {
    let r = run(&["fsm.v"], &["--wire", "nstate[2]"]);
    assert_eq!(endpoint_of(&r, "is5"), "state[3:0] == 5");
    assert_eq!(endpoint_of(&r, "is9"), "state[3:0] == 9");
    assert_eq!(endpoint_of(&r, "is5or9"), "state[3:0] inside {5, 9}");
    assert_eq!(endpoint_of(&r, "nstate[2]"), "mode & (state[3:0] inside {5, 9})");
}

#[test]
fn fsm_other_next_state_bits() {
    let r = run(&["fsm.v"], &["--wire", "nstate"]);
    assert_eq!(endpoint_of(&r, "nstate[3]"), "!state[3]");
    assert_eq!(endpoint_of(&r, "nstate[1]"), "state[3:0] == 5 | state[1] & ack");
    assert_eq!(endpoint_of(&r, "nstate[0]"), "req ^ state[0]");
}

#[test]
fn equal_and_inverted_wires_are_listed_as_aliases() {
    let r = run(&["fsm.v"], &["--wire", "branch_ok"]);
    assert!(r.contains("aliases:  == branch, == !is5or9"), "{r}");
    assert_eq!(endpoint_of(&r, "branch_ok"), "!(state[3:0] inside {5, 9})");
}

#[test]
fn endpoints_in_other_instances_use_absolute_names() {
    let r = run(
        &["fsm.v", "hier.v"],
        &["--inst", "u_fsm", "--wire", "nstate[2]"],
    );
    assert_eq!(
        endpoint_of(&r, "nstate[2]"),
        "/u_cfg/mode & (state[3:0] inside {5, 9})"
    );
}

#[test]
fn tracing_from_the_top_crosses_into_the_fsm() {
    let r = run(&["fsm.v", "hier.v"], &["--wire", "out"]);
    // out = next_state & branch_ok = mode & inside & !inside = 0
    assert_eq!(endpoint_of(&r, "out"), "1'b0");
}

#[test]
fn filter_selects_wires_by_the_signal_they_use() {
    let r = run(&["fsm.v"], &["--wire", "nstate[1]", "--filter", "ack"]);
    assert!(r.contains(" hold1 "), "{r}");
    assert!(!r.contains(" is5 "), "{r}");
}

#[test]
fn no_lift_prints_only_local_forms() {
    let r = run(&["fsm.v"], &["--wire", "nstate[2]", "--no-lift"]);
    assert!(r.contains("local:"), "{r}");
    assert!(!r.contains("endpoint:"), "{r}");
}

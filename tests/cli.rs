//! End-to-end tests of the command-line tool.

use std::process::Command;

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// Run the tool; returns (success, stdout, stderr).
fn run(args: &[&str]) -> (bool, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_netlist_search"))
        .args(args)
        .output()
        .expect("tool runs");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n"),
        String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n"),
    )
}

fn fsm(extra: &[&str]) -> (bool, String, String) {
    let (net, lib) = (fixture("fsm.v"), fixture("basic.lib"));
    let mut args = vec!["--netlist", &net, "--lib", &lib];
    args.extend_from_slice(extra);
    run(&args)
}

fn assert_has(text: &str, needles: &[&str]) {
    for n in needles {
        assert!(text.contains(n), "missing {n:?} in:\n{text}");
    }
}

#[test]
fn report_lists_endpoints_wires_and_local_forms() {
    let (ok, out, err) = fsm(&["--wire", "nstate[2]"]);
    assert!(ok, "{err}");
    assert_has(
        &out,
        &[
            "=== Cone of nstate[2]   (module fsm) ===",
            "Endpoints (5):",
            "[REG] state[3]",
            "inst state_reg[3] DFFRX1",
            "[PORT-IN] mode",
            "d0 nstate[2]",
            "AND2X1 U23",
            "local:    mode & is5or9",
            "d1 is5or9",
            "local:    is5 | is9",
            "local:    !(state[3] | n2 | state[1] | n0)",
            "local:    !state[2]",
        ],
    );
}

#[test]
fn a_bus_without_index_is_traced_bit_by_bit() {
    let (ok, out, err) = fsm(&["--wire", "nstate"]);
    assert!(ok, "{err}");
    assert_eq!(out.matches("=== Cone of").count(), 4);
    assert_has(&out, &["Cone of nstate[3] ", "Cone of nstate[0] "]);
}

#[test]
fn alias_through_a_buffer_and_mux_local_form() {
    let (ok, out, err) = fsm(&["--wire", "nstate[0]"]);
    assert!(ok, "{err}");
    assert_has(&out, &["BUFX2 U51", "local:    t0", "local:    req & n0 | !req & state[0]"]);
}

#[test]
fn filter_keeps_only_wires_that_depend_on_the_signal() {
    let (ok, out, err) = fsm(&["--wire", "nstate[1]", "--filter", "ack"]);
    assert!(ok, "{err}");
    assert_has(&out, &["d0 nstate[1]", "d1 hold1"]);
    assert!(!out.contains("d1 is5"), "{out}");
}

#[test]
fn instance_path_selects_the_module_instance() {
    let (fsm_v, hier, lib) = (fixture("fsm.v"), fixture("hier.v"), fixture("basic.lib"));
    let (ok, out, err) = run(&[
        "--netlist", &fsm_v, "--netlist", &hier, "--lib", &lib, "--inst", "u_fsm", "--wire",
        "nstate[2]",
    ]);
    assert!(ok, "{err}");
    assert_has(
        &out,
        &[
            "=== Cone of u_fsm/nstate[2]   (module fsm, instance u_fsm) ===",
            "[REG] /u_cfg/mode",
            "inst /u_cfg/mode_reg DFFX1",
            "local:    /mode_w  (input port)",
            "local:    /u_cfg/mode  (submodule output)",
        ],
    );
}

#[test]
fn no_cross_stops_at_the_port() {
    let (fsm_v, hier, lib) = (fixture("fsm.v"), fixture("hier.v"), fixture("basic.lib"));
    let (ok, out, err) = run(&[
        "--netlist", &fsm_v, "--netlist", &hier, "--lib", &lib, "--inst", "chip/u_fsm", "--wire",
        "nstate[2]", "--no-cross",
    ]);
    assert!(ok, "{err}");
    assert_has(&out, &["[PORT-IN] mode", "Notes:", "--no-cross"]);
    assert!(!out.contains("/u_cfg/mode"), "{out}");
}

#[test]
fn missing_wire_fails_with_suggestions() {
    let (ok, out, err) = fsm(&["--wire", "nstat"]);
    assert!(!ok);
    assert!(out.is_empty(), "{out}");
    assert_has(&err, &["error:", "nstat", "not found", "nstate"]);
}

#[test]
fn missing_instance_fails() {
    let (ok, _, err) = fsm(&["--inst", "u_nope", "--wire", "nstate[2]"]);
    assert!(!ok);
    assert_has(&err, &["error:", "u_nope"]);
}

#[test]
fn missing_file_fails() {
    let lib = fixture("basic.lib");
    let (ok, _, err) = run(&["--netlist", "no_such_file.v", "--lib", &lib, "--wire", "x"]);
    assert!(!ok);
    assert_has(&err, &["error:", "no_such_file.v"]);
}

#[test]
fn bad_radix_fails() {
    let (ok, _, err) = fsm(&["--wire", "nstate[2]", "--radix", "octal"]);
    assert!(!ok);
    assert_has(&err, &["radix"]);
}

#[test]
fn output_file_receives_the_report() {
    let path = std::env::temp_dir().join(format!("netlist_search_test_{}.txt", std::process::id()));
    let p = path.to_string_lossy().into_owned();
    let (ok, out, err) = fsm(&["--wire", "nstate[2]", "-o", &p]);
    assert!(ok, "{err}");
    assert!(out.is_empty(), "{out}");
    let text = std::fs::read_to_string(&path).unwrap();
    std::fs::remove_file(&path).ok();
    assert!(text.contains("=== Cone of nstate[2]"), "{text}");
}

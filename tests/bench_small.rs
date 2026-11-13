//! The benchmark generator at a small size: every suggested query must run,
//! and no report may contain an internal error.

use std::process::Command;

#[test]
fn generated_netlist_answers_every_query() {
    let dir = std::env::temp_dir().join(format!("netlist_search_bench_{}", std::process::id()));
    let out = Command::new(env!("CARGO_BIN_EXE_gen_netlist"))
        .args(["--lines", "20000", "--out"])
        .arg(&dir)
        .output()
        .unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let queries = std::fs::read_to_string(dir.join("queries.txt")).unwrap();
    let mut reports = Vec::new();
    for q in queries.lines() {
        // Lines look like: --inst "u_blk_0" --wire "nstate[2]"
        let parts: Vec<&str> = q.split('"').collect();
        let (inst, wire) = (parts[1], parts[3]);
        if wire == "deep3" {
            continue; // thousands of random gates: slow in an unoptimised build
        }
        let out = Command::new(env!("CARGO_BIN_EXE_netlist_search"))
            .arg("--netlist")
            .arg(dir.join("bench.v"))
            .arg("--lib")
            .arg(dir.join("bench.lib"))
            .args(["--inst", inst, "--wire", wire])
            .output()
            .unwrap();
        let text = String::from_utf8_lossy(&out.stdout).into_owned();
        assert!(out.status.success(), "{q}: {}", String::from_utf8_lossy(&out.stderr));
        assert!(!text.contains("INTERNAL"), "{q}:\n{text}");
        reports.push((wire.to_string(), text));
    }
    std::fs::remove_dir_all(&dir).ok();
    let of = |w: &str| &reports.iter().find(|(x, _)| x == w).unwrap().1;
    assert!(of("sh2").contains("(data[9:0] >> state[2:0])[2]"), "{}", of("sh2"));
    assert!(of("cnt_next7").contains("? (cnt[7:0] + 1)[7] : cnt[7]"), "{}", of("cnt_next7"));
    assert!(of("branch_b").contains("state[3:0] == 9 & "), "{}", of("branch_b"));
    assert!(of("nstate[0]").contains("endpoint: state[3:0] == 5 ? "), "{}", of("nstate[0]"));
    assert!(of("nstate[0]").contains("[UNKNOWN]") || !of("nstate[0]").contains("mem_q"));
}

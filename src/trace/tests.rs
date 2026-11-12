use super::*;
use crate::liberty::CellLib;
use crate::netlist::design::Design;
use crate::netlist::index::ModuleIndex;

fn lib() -> &'static CellLib {
    let mut lib = CellLib::new();
    lib.load_str(include_str!("../../tests/fixtures/basic.lib")).unwrap();
    Box::leak(Box::new(lib))
}

fn design(src: &str) -> Design<'static> {
    let leaked: &'static [u8] = Box::leak(src.to_string().into_boxed_str()).as_bytes();
    Design::new(ModuleIndex::build(&[leaked]).unwrap(), lib())
}

fn opts() -> TraceOpts {
    TraceOpts {
        max_nodes: 200_000,
        max_hier_depth: 8,
        cross: true,
    }
}

fn cone_with(src: &str, inst: &str, wire: &str, o: &TraceOpts) -> Cone {
    let d = design(src);
    let path = d.resolve(None, inst).unwrap_or_else(|e| panic!("{e:#}"));
    let m = d.module(path.module()).unwrap();
    let bits = d.find_wire_bits(m, wire).unwrap_or_else(|e| panic!("{e:#}"));
    assert_eq!(bits.len(), 1, "test wires are single bits");
    trace(&d, &path, bits[0], o).unwrap_or_else(|e| panic!("{e:#}"))
}

fn cone(src: &str, inst: &str, wire: &str) -> Cone {
    cone_with(src, inst, wire, &opts())
}

/// Assert that the dump contains each of `lines` (after trimming).
fn has(c: &Cone, lines: &[&str]) {
    let dump = c.dump();
    let got: Vec<&str> = dump.lines().map(str::trim).collect();
    for l in lines {
        assert!(got.contains(&l.trim()), "missing line {l:?} in dump:\n{dump}");
    }
}

fn kinds(c: &Cone) -> Vec<(EndpointKind, String)> {
    let mut v: Vec<_> = c.endpoints.iter().map(|e| (e.kind, e.name.clone())).collect();
    v.sort_by(|a, b| a.1.cmp(&b.1));
    v
}

const COMB: &str = "module m (a, b, c, y);
  input a, b, c; output y; wire n1, n2;
  AND2X1 U1 (.A(a), .B(b), .Y(n1));
  INVX1 U2 (.A(c), .Y(n2));
  OR2X1 U3 (.A(n1), .B(n2), .Y(y));
endmodule";

#[test]
fn gates_are_followed_back_to_primary_inputs() {
    let c = cone(COMB, "", "y");
    has(
        &c,
        &[
            "d0 y = OR2X1 U3 (A=n1, B=n2)",
            "d1 n1 = AND2X1 U1 (A=a, B=b)",
            "d1 n2 = INVX1 U2 (A=c)",
            "d2 a = [PORT-IN] a",
            "d2 b = [PORT-IN] b",
            "d2 c = [PORT-IN] c",
        ],
    );
    assert_eq!(c.nodes[c.target as usize].name, "y");
    assert!(!c.truncated);
}

#[test]
fn topological_order_puts_inputs_before_users() {
    let c = cone(COMB, "", "y");
    let pos = |name: &str| {
        c.topo
            .iter()
            .position(|&n| c.nodes[n as usize].name == name)
            .unwrap_or_else(|| panic!("{name} not in topo"))
    };
    assert!(pos("a") < pos("n1"));
    assert!(pos("n1") < pos("y"));
    assert!(pos("n2") < pos("y"));
    assert_eq!(*c.topo.last().unwrap(), c.target);
    assert_eq!(c.topo.len(), c.nodes.len());
}

const REGS: &str = "module m (clk, rst_n, d, y, z);
  input clk, rst_n, d; output y, z; wire [1:0] cnt; wire n5, q2;
  DFFRX1 \\cnt_reg[1] (.D(d), .CK(clk), .RN(rst_n), .Q(cnt[1]), .QN(n5));
  DFFRX1 \\cnt_reg[0] (.D(d), .CK(clk), .RN(rst_n), .Q(cnt[0]));
  DFFX1 U77 (.D(d), .CK(clk), .Q(q2));
  LATX1 lat0 (.D(d), .G(clk), .Q(z));
  AND3X1 U1 (.A(cnt[0]), .B(n5), .C(q2), .Y(y));
endmodule";

#[test]
fn flip_flop_outputs_are_register_endpoints_named_after_the_signal() {
    let c = cone(REGS, "", "y");
    has(
        &c,
        &[
            "d0 y = AND3X1 U1 (A=cnt[0], B=n5, C=q2)",
            "d1 cnt[0] = [REG] cnt[0]",
            "d1 n5 = ![REG] cnt[1]",
            "d1 q2 = [REG] q2",
        ],
    );
    assert_eq!(
        kinds(&c),
        [
            (EndpointKind::Reg, "cnt[0]".to_string()),
            (EndpointKind::Reg, "cnt[1]".to_string()),
            (EndpointKind::Reg, "q2".to_string()),
        ]
    );
}

#[test]
fn q_and_qn_of_one_flop_share_an_endpoint() {
    let src = "module m (clk, d, y); input clk, d; output y; wire q, qn;
  DFFRX1 r_reg (.D(d), .CK(clk), .RN(1'b1), .Q(q), .QN(qn));
  AND2X1 U1 (.A(q), .B(qn), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    assert_eq!(c.endpoints.len(), 1);
    has(&c, &["d1 q = [REG] r", "d1 qn = ![REG] r"]);
}

#[test]
fn register_endpoint_records_instance_and_cell() {
    let c = cone(REGS, "", "y");
    let e = c.endpoints.iter().find(|e| e.name == "cnt[1]").unwrap();
    assert_eq!(e.inst.as_deref(), Some("cnt_reg[1]"));
    assert_eq!(e.cell.as_deref(), Some("DFFRX1"));
}

#[test]
fn latch_output_is_a_latch_endpoint() {
    let c = cone(REGS, "", "z");
    assert_eq!(kinds(&c), [(EndpointKind::Latch, "z".to_string())]);
}

#[test]
fn cell_missing_from_the_library_is_an_unknown_endpoint() {
    let src = "module m (a, y); input a; output y; wire [7:0] dout; wire n1;
  SRAM_1024x32 u_ram (.addr(a), .dout(dout));
  INVX1 U1 (.A(dout[3]), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    let e = &c.endpoints[0];
    assert_eq!(e.kind, EndpointKind::Unknown);
    assert_eq!(e.name, "u_ram.dout[3]");
    assert!(e.detail.contains("SRAM_1024x32"), "{}", e.detail);
    assert_eq!(e.cell.as_deref(), Some("SRAM_1024x32"));
}

#[test]
fn unknown_cell_pin_on_a_driven_net_is_assumed_to_be_a_load() {
    let src = "module m (a, y); input a; output y;
  INVX1 U1 (.A(a), .Y(y));
  MYSTERY u_m (.p(y));
endmodule";
    let c = cone(src, "", "y");
    has(&c, &["d0 y = INVX1 U1 (A=a)"]);
    assert!(
        c.notes.iter().any(|n| n.contains("u_m") && n.contains("load")),
        "{:?}",
        c.notes
    );
}

#[test]
fn library_macro_without_function_is_a_black_box() {
    let src = "module m (clk, y); input clk; output y; wire [3:0] q;
  RAM16X4 u_ram (.CLK(clk), .Q(q));
  BUFX2 U1 (.A(q[2]), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    let e = &c.endpoints[0];
    assert_eq!(e.kind, EndpointKind::BlackBox);
    assert_eq!(e.name, "u_ram.Q[2]");
    assert!(e.detail.contains("RAM16X4"), "{}", e.detail);
}

#[test]
fn statetable_cell_output_is_a_black_box() {
    let src = "module m (clk, en, y); input clk, en; output y;
  ICGX1 u_icg (.CK(clk), .E(en), .GCK(y));
endmodule";
    let c = cone(src, "", "y");
    assert_eq!(kinds(&c), [(EndpointKind::BlackBox, "u_icg.GCK".to_string())]);
}

#[test]
fn three_state_output_is_an_inout_endpoint() {
    let src = "module m (a, oe, y); input a, oe; output y;
  TBUFX1 U1 (.A(a), .OE(oe), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    assert_eq!(c.endpoints[0].kind, EndpointKind::Inout);
}

#[test]
fn constants_tie_cells_and_supplies() {
    let src = "module m (y); output y; wire hi, lo, n1; supply1 vdd;
  TIEHI U1 (.Y(hi));
  TIELO U2 (.Y(lo));
  AND3X1 U3 (.A(hi), .B(vdd), .C(1'b1), .Y(n1));
  OR2X1 U4 (.A(n1), .B(lo), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    has(
        &c,
        &[
            "d1 n1 = AND3X1 U3 (A=hi, B=vdd, C=1'b1)",
            "d2 hi = const 1",
            "d2 vdd = const 1",
            "d1 lo = const 0",
        ],
    );
    assert!(c.endpoints.is_empty());
}

#[test]
fn x_constant_is_an_endpoint() {
    let src = "module m (y); output y; INVX1 U1 (.A(1'bx), .Y(y)); endmodule";
    let c = cone(src, "", "y");
    assert_eq!(kinds(&c), [(EndpointKind::ConstX, "1'bx".to_string())]);
}

#[test]
fn undriven_net_and_floating_input_pin() {
    let src = "module m (y); output y; wire n1;
  AND2X1 U1 (.A(n1), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    assert_eq!(
        kinds(&c),
        [
            (EndpointKind::Undriven, "U1.B".to_string()),
            (EndpointKind::Undriven, "n1".to_string()),
        ]
    );
}

#[test]
fn two_drivers_make_a_multi_driver_endpoint() {
    let src = "module m (a, b, y); input a, b; output y;
  INVX1 U1 (.A(a), .Y(y));
  INVX1 U2 (.A(b), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    let e = &c.endpoints[0];
    assert_eq!(e.kind, EndpointKind::MultiDriver);
    assert!(e.detail.contains("U1") && e.detail.contains("U2"), "{}", e.detail);
}

#[test]
fn combinational_loop_is_cut_and_reported() {
    let src = "module m (a, y); input a; output y; wire n1;
  NAND2X1 U1 (.A(a), .B(y), .Y(n1));
  INVX1 U2 (.A(n1), .Y(y));
endmodule";
    let c = cone(src, "", "y");
    assert!(c.endpoints.iter().any(|e| e.kind == EndpointKind::Loop), "{}", c.dump());
    assert!(c.notes.iter().any(|n| n.contains("loop")), "{:?}", c.notes);
    assert_eq!(*c.topo.last().unwrap(), c.target);
}

#[test]
fn node_budget_truncates_the_far_side_of_the_cone() {
    let o = TraceOpts {
        max_nodes: 3,
        ..opts()
    };
    let c = cone_with(COMB, "", "y", &o);
    assert!(c.truncated);
    assert!(c.endpoints.iter().any(|e| e.kind == EndpointKind::Truncated));
    // The gate driving the target is still there.
    has(&c, &["d0 y = OR2X1 U3 (A=n1, B=n2)"]);
    assert!(c.notes.iter().any(|n| n.contains("--max-nodes")), "{:?}", c.notes);
}

#[test]
fn assign_alias_and_inversion_are_followed() {
    let src = "module m (a, y, z, k, q); input a; output y, z, k, q; wire n1;
  assign n1 = a;
  assign y = n1;
  assign z = ~a;
  assign k = 1'b0;
  assign q = a & n1;
endmodule";
    let c = cone(src, "", "y");
    has(&c, &["d0 y = n1 (assign)", "d0 n1 = a (assign)", "d0 a = [PORT-IN] a"]);
    let c = cone(src, "", "z");
    has(&c, &["d0 z = !a (assign)"]);
    let c = cone(src, "", "k");
    has(&c, &["d0 k = const 0"]);
    let c = cone(src, "", "q");
    assert_eq!(c.endpoints[0].kind, EndpointKind::ComplexAssign);
}

#[test]
fn gate_primitives_are_gates() {
    let src = "module m (a, b, y); input a, b; output y; wire n1;
  nand (n1, a, b);
  not g1 (y, n1);
endmodule";
    let c = cone(src, "", "y");
    has(&c, &["d0 y = not g1 (I1=n1)", "d1 n1 = nand <unnamed> (I1=a, I2=b)"]);
}

const HIER: &str = "
module leaf (a, b, y); input a, b; output y; wire q;
  DFFX1 st_reg (.D(a), .CK(b), .Q(q));
  AND2X1 U1 (.A(a), .B(q), .Y(y));
endmodule
module mid (x, sel, o); input [1:0] x; input sel; output o; wire w;
  leaf u_leaf (.a(x[1]), .b(sel), .y(w));
  OR2X1 U2 (.A(w), .B(x[0]), .Y(o));
endmodule
module top (p, q, r); input [1:0] p; input q; output r; wire mode, t;
  DFFX1 mode_reg (.D(q), .CK(q), .Q(mode));
  INVX1 U9 (.A(p[1]), .Y(t));
  mid u_mid (.x({t, mode}), .sel(1'b1), .o(r));
endmodule";

#[test]
fn drivers_inside_child_modules_are_followed_downwards() {
    let c = cone(HIER, "u_mid", "o");
    has(
        &c,
        &[
            "d0 o = OR2X1 U2 (A=w, B=x[0])",
            "d1 w = /u_mid/u_leaf/y (submodule output)",
            "d1 /u_mid/u_leaf/y = AND2X1 /u_mid/u_leaf/U1 (A=/u_mid/u_leaf/a, B=/u_mid/u_leaf/q)",
            "d2 /u_mid/u_leaf/q = [REG] /u_mid/u_leaf/st",
        ],
    );
}

#[test]
fn input_ports_are_followed_up_into_the_parent() {
    let c = cone(HIER, "u_mid", "o");
    has(
        &c,
        &[
            "d1 x[0] = /mode (input port)",
            "d1 /mode = [REG] /mode",
            "d2 /u_mid/u_leaf/a = x[1] (input port)",
            "d2 x[1] = /t (input port)",
            "d2 /t = INVX1 /U9 (A=/p[1])",
            "d3 /p[1] = [PORT-IN] /p[1]",
        ],
    );
    assert_eq!(
        kinds(&c),
        [
            (EndpointKind::Reg, "/mode".to_string()),
            (EndpointKind::PortIn, "/p[1]".to_string()),
            (EndpointKind::Reg, "/u_mid/u_leaf/st".to_string()),
        ]
    );
}

#[test]
fn constant_tied_to_an_input_port_in_the_parent() {
    let c = cone(HIER, "u_mid/u_leaf", "b");
    has(&c, &["d0 b = /u_mid/sel (input port)", "d0 /u_mid/sel = const 1"]);
}

#[test]
fn names_inside_the_target_instance_are_bare() {
    let c = cone(HIER, "u_mid/u_leaf", "y");
    has(&c, &["d0 y = AND2X1 U1 (A=a, B=q)", "d1 q = [REG] st"]);
    assert!(c.nodes[c.target as usize].in_target);
}

#[test]
fn no_cross_stops_at_module_boundaries() {
    let o = TraceOpts {
        cross: false,
        ..opts()
    };
    let c = cone_with(HIER, "u_mid", "o", &o);
    assert_eq!(
        kinds(&c),
        [
            (EndpointKind::SubmoduleOut, "w".to_string()),
            (EndpointKind::PortIn, "x[0]".to_string()),
        ]
    );
    let w = c.endpoints.iter().find(|e| e.name == "w").unwrap();
    assert!(w.detail.contains("u_leaf") && w.detail.contains("leaf"), "{}", w.detail);
}

#[test]
fn hierarchy_depth_limit_stops_further_crossings() {
    let o = TraceOpts {
        max_hier_depth: 1,
        ..opts()
    };
    // From u_mid/u_leaf: one crossing reaches u_mid, a second (to top) is refused.
    let c = cone_with(HIER, "u_mid/u_leaf", "a", &o);
    has(&c, &["d0 a = /u_mid/x[1] (input port)"]);
    assert_eq!(kinds(&c), [(EndpointKind::PortIn, "/u_mid/x[1]".to_string())]);
    assert!(c.notes.iter().any(|n| n.contains("--max-hier-depth")), "{:?}", c.notes);
}

#[test]
fn unconnected_port_in_the_parent_is_undriven() {
    let src = "module sub (a, y); input a; output y; BUFX2 U1 (.A(a), .Y(y)); endmodule
module top (r); output r; sub u (.a(), .y(r)); endmodule";
    let c = cone(src, "u", "y");
    assert_eq!(c.endpoints[0].kind, EndpointKind::Undriven);
}

#[test]
fn multi_bit_child_port_maps_bit_by_bit() {
    let src = "module sub (d, q); input [2:0] d; output [2:0] q;
  BUFX2 U0 (.A(d[0]), .Y(q[0])); BUFX2 U1 (.A(d[1]), .Y(q[1])); BUFX2 U2 (.A(d[2]), .Y(q[2]));
endmodule
module top (a, b, c, r); input a, b, c; output r; wire [2:0] w;
  sub u (.d({a, b, c}), .q(w));
  BUFX2 U9 (.A(w[1]), .Y(r));
endmodule";
    let c = cone(src, "", "r");
    has(
        &c,
        &[
            "d1 w[1] = /u/q[1] (submodule output)",
            "d2 /u/d[1] = b (input port)",
        ],
    );
    assert_eq!(kinds(&c), [(EndpointKind::PortIn, "b".to_string())]);
}

#[test]
fn positional_connections_to_modules_and_cells() {
    let src = "module sub (a, y); input a; output y; INVX1 U1 (a, y); endmodule
module top (p, r); input p; output r; sub u (p, r); endmodule";
    let c = cone(src, "", "r");
    has(&c, &["d0 /u/y = INVX1 /u/U1 (A=/u/a)", "d1 p = [PORT-IN] p"]);
}

#[test]
fn full_adder_outputs_use_their_own_functions() {
    let src = "module m (a, b, ci, s, co); input a, b, ci; output s, co;
  ADDFX1 U1 (.A(a), .B(b), .CI(ci), .S(s), .CO(co));
endmodule";
    let c = cone(src, "", "co");
    match &c.nodes[c.target as usize].kind {
        NodeKind::Gate { out_pin, inputs, .. } => {
            assert_eq!(out_pin, "CO");
            assert_eq!(inputs.len(), 3);
        }
        _ => panic!("{}", c.dump()),
    }
}

// ---- sibling bits -----------------------------------------------------------

const SIB: &str = "module m (clk, d, sel, y, z, w, v);
  input clk; input [7:0] d; input [1:0] sel; output y, z, w, v;
  wire [3:0] cnt; wire [3:0] part; wire q5, q4;
  DFFX1 \\cnt_reg[3] (.D(d[3]), .CK(clk), .Q(cnt[3]));
  DFFX1 \\cnt_reg[2] (.D(d[2]), .CK(clk), .Q(cnt[2]));
  DFFX1 \\cnt_reg[1] (.D(d[1]), .CK(clk), .Q(cnt[1]));
  DFFX1 \\cnt_reg[0] (.D(d[0]), .CK(clk), .Q(cnt[0]));
  DFFX1 lim_reg_5_ (.D(d[5]), .CK(clk), .Q(q5));
  DFFX1 lim_reg_4_ (.D(d[4]), .CK(clk), .Q(q4));
  DFFX1 lim_reg_0_ (.D(d[0]), .CK(clk), .Q());
  DFFX1 \\part_reg[3] (.D(d[3]), .CK(clk), .Q(part[3]));
  AND2X1 U1 (.A(cnt[3]), .B(cnt[2]), .Y(y));
  AND2X1 U2 (.A(q5), .B(q4), .Y(z));
  AND2X1 U3 (.A(d[6]), .B(d[5]), .Y(w));
  AND2X1 U4 (.A(part[3]), .B(sel[1]), .Y(v));
endmodule";

fn siblings(c: &Cone) -> Vec<String> {
    let mut s = c.siblings.clone();
    s.sort();
    s
}

#[test]
fn lower_register_bits_outside_the_cone_are_siblings() {
    let c = cone(SIB, "", "y");
    assert_eq!(siblings(&c), ["cnt[0]", "cnt[1]"]);
}

#[test]
fn siblings_follow_the_underscore_naming_style_and_must_exist() {
    let c = cone(SIB, "", "z");
    // lim_reg_0_ exists; bits 1 to 3 do not.
    assert_eq!(siblings(&c), ["lim[0]"]);
}

#[test]
fn lower_bits_of_a_port_bus_are_siblings() {
    let c = cone(SIB, "", "w");
    assert_eq!(siblings(&c), ["d[0]", "d[1]", "d[2]", "d[3]", "d[4]"]);
}

#[test]
fn a_bit_whose_neighbours_do_not_exist_has_no_siblings() {
    let c = cone(SIB, "", "v");
    // part_reg[2..0] are not in the netlist; sel[0] is.
    assert_eq!(siblings(&c), ["sel[0]"]);
}

#[test]
fn siblings_in_other_instances_carry_the_instance_prefix() {
    let src = "module sub (clk, d, q); input clk; input [1:0] d; output q; wire [1:0] st;
  DFFX1 \\st_reg[1] (.D(d[1]), .CK(clk), .Q(st[1]));
  DFFX1 \\st_reg[0] (.D(d[0]), .CK(clk), .Q(st[0]));
  BUFX2 U1 (.A(st[1]), .Y(q));
endmodule
module top (clk, d, r); input clk; input [1:0] d; output r; sub u (.clk(clk), .d(d), .q(r)); endmodule";
    let c = cone(src, "", "r");
    assert_eq!(siblings(&c), ["/u/st[0]"]);
}

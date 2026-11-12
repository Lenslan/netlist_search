use super::index::ModuleIndex;
use super::parser::*;
use crate::liberty::Dir;

/// Parse the first module of `src`.
fn parse(src: &str) -> Module<'static> {
    try_parse(src).unwrap_or_else(|e| panic!("parse failed: {e:#}"))
}

fn try_parse(src: &str) -> anyhow::Result<Module<'static>> {
    let src: &'static [u8] = Box::leak(src.to_string().into_boxed_str()).as_bytes();
    let idx = ModuleIndex::build(&[src])?;
    Module::parse(&idx.modules[0])
}

fn s(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// Names of the bits of connection `conn`, MSB first.
fn conn_names(m: &Module, conn: u32) -> Vec<String> {
    m.conn_bits(conn).iter().map(|b| m.ref_name(*b)).collect()
}

/// `(pin, [bit names])` for every connection of instance `inst`.
fn inst_conns(m: &Module, inst: u32) -> Vec<(String, Vec<String>)> {
    m.inst_conns(inst)
        .map(|c| {
            (
                m.conn_pin(c).map(s).unwrap_or_else(|| "<pos>".into()),
                conn_names(m, c),
            )
        })
        .collect()
}

fn bit(m: &Module, name: &str) -> BitId {
    let (base, idx) = match name.find('[') {
        Some(i) => (&name[..i], name[i + 1..name.len() - 1].parse::<i32>().unwrap()),
        None => (name, 0),
    };
    let net = m.find_net(base.as_bytes()).unwrap_or_else(|| panic!("no net {base}"));
    m.bit_of(net, idx).unwrap_or_else(|| panic!("no bit {name}"))
}

const SIMPLE: &str = "module m (a, b, y);
  input a;
  input [1:0] b;
  output y;
  wire n1;
  AND2X1 U1 (.A(a), .B(b[0]), .Y(n1));
  INVX1 U2 (.A(n1), .Y(y));
endmodule";

#[test]
fn non_ansi_ports_get_directions_from_the_body() {
    let m = parse(SIMPLE);
    assert_eq!(s(m.name), "m");
    let ports: Vec<_> = m.ports.iter().map(|p| (s(p.name), p.dir)).collect();
    assert_eq!(
        ports,
        [
            ("a".to_string(), Dir::Input),
            ("b".to_string(), Dir::Input),
            ("y".to_string(), Dir::Output)
        ]
    );
    assert_eq!(m.port_width(1), 2);
    assert_eq!(m.port_width(0), 1);
}

#[test]
fn instances_and_named_connections() {
    let m = parse(SIMPLE);
    assert_eq!(m.num_insts(), 2);
    assert_eq!(s(m.inst_cell(0)), "AND2X1");
    assert_eq!(s(m.inst_name(0)), "U1");
    assert_eq!(
        inst_conns(&m, 0),
        [
            ("A".to_string(), vec!["a".to_string()]),
            ("B".to_string(), vec!["b[0]".to_string()]),
            ("Y".to_string(), vec!["n1".to_string()]),
        ]
    );
    assert_eq!(s(m.inst_name(1)), "U2");
}

#[test]
fn ansi_ports() {
    let m = parse(
        "module m (input [3:0] a, input b, c, output wire [1:0] y, inout z); endmodule",
    );
    let ports: Vec<_> = m
        .ports
        .iter()
        .enumerate()
        .map(|(i, p)| (s(p.name), p.dir, m.port_width(i as u32)))
        .collect();
    assert_eq!(
        ports,
        [
            ("a".to_string(), Dir::Input, 4),
            ("b".to_string(), Dir::Input, 1),
            ("c".to_string(), Dir::Input, 1),
            ("y".to_string(), Dir::Output, 2),
            ("z".to_string(), Dir::Inout, 1),
        ]
    );
}

#[test]
fn selects_concatenation_replication_and_constants() {
    let m = parse(
        "module m ();
  wire [3:0] a; wire b, c;
  RAM u (.D({a[3:2], b, 1'b0, 2'b10, {2{c}}}), .A(a), .Z(a[2:1]), .X(1'bx));
endmodule",
    );
    let c = inst_conns(&m, 0);
    assert_eq!(c[0].1, ["a[3]", "a[2]", "b", "1'b0", "1'b1", "1'b0", "c", "c"]);
    assert_eq!(c[1].1, ["a[3]", "a[2]", "a[1]", "a[0]"]);
    assert_eq!(c[2].1, ["a[2]", "a[1]"]);
    assert_eq!(c[3].1, ["1'bx"]);
}

#[test]
fn hex_and_decimal_literals_expand_msb_first() {
    let m = parse("module m (); X u (.A(4'hA), .B(3'd5), .C(2'b1_0)); endmodule");
    let c = inst_conns(&m, 0);
    assert_eq!(c[0].1, ["1'b1", "1'b0", "1'b1", "1'b0"]);
    assert_eq!(c[1].1, ["1'b1", "1'b0", "1'b1"]);
    assert_eq!(c[2].1, ["1'b1", "1'b0"]);
}

#[test]
fn ascending_ranges_keep_declared_order() {
    let m = parse("module m (); wire [0:3] w; X u (.A(w), .B(w[1:2])); endmodule");
    let c = inst_conns(&m, 0);
    assert_eq!(c[0].1, ["w[0]", "w[1]", "w[2]", "w[3]"]);
    assert_eq!(c[1].1, ["w[1]", "w[2]"]);
    let net = m.find_net(b"w").unwrap();
    assert!(m.bit_of(net, 2).is_some());
    assert!(m.bit_of(net, 4).is_none());
}

#[test]
fn empty_and_positional_connections() {
    let m = parse(
        "module m (); wire a, y;
  DFFRX1 r (.D(a), .QN(), .Q(y));
  INVX1 U3 (a, y);
endmodule",
    );
    let c = inst_conns(&m, 0);
    assert_eq!(c[1], ("QN".to_string(), vec![]));
    let p = inst_conns(&m, 1);
    assert_eq!(p[0], ("<pos>".to_string(), vec!["a".to_string()]));
    assert_eq!(p[1], ("<pos>".to_string(), vec!["y".to_string()]));
}

#[test]
fn several_instances_in_one_statement() {
    let m = parse(
        "module m (); wire a, b, c;
  INVX1 U1 (.A(a), .Y(b)), U2 (.A(b), .Y(c));
endmodule",
    );
    assert_eq!(m.num_insts(), 2);
    assert_eq!(s(m.inst_name(1)), "U2");
    assert_eq!(s(m.inst_cell(1)), "INVX1");
    assert_eq!(inst_conns(&m, 1)[1].1, ["c"]);
}

#[test]
fn assign_alias_invert_constant_vector_and_complex() {
    let m = parse(
        "module m (); wire a, b, y, z, k, q; wire [1:0] v;
  assign y = a;
  assign z = ~a;
  assign k = 1'b1;
  assign v[1:0] = {a, b};
  assign q = a & b;
endmodule",
    );
    let drv = |n: &str| {
        let (r, k) = m.assign_driver(bit(&m, n)).unwrap_or_else(|| panic!("{n} undriven"));
        (m.ref_name(r), k)
    };
    assert_eq!(drv("y"), ("a".to_string(), AssignKind::Alias));
    assert_eq!(drv("z"), ("a".to_string(), AssignKind::Invert));
    assert_eq!(drv("k"), ("1'b1".to_string(), AssignKind::Alias));
    assert_eq!(drv("v[1]"), ("a".to_string(), AssignKind::Alias));
    assert_eq!(drv("v[0]"), ("b".to_string(), AssignKind::Alias));
    assert_eq!(drv("q").1, AssignKind::Complex);
    assert!(m.assign_driver(bit(&m, "a")).is_none());
}

#[test]
fn supply_nets_are_constants() {
    let m = parse("module m (); supply1 vdd; supply0 gnd; endmodule");
    let (r, k) = m.assign_driver(bit(&m, "vdd")).unwrap();
    assert_eq!((m.ref_name(r), k), ("1'b1".to_string(), AssignKind::Alias));
    let (r, _) = m.assign_driver(bit(&m, "gnd")).unwrap();
    assert_eq!(m.ref_name(r), "1'b0");
}

#[test]
fn undeclared_names_become_implicit_scalar_nets() {
    let m = parse("module m (); INVX1 U1 (.A(n9), .Y(n10)); endmodule");
    assert!(m.find_net(b"n9").is_some());
    assert_eq!(inst_conns(&m, 0)[1].1, ["n10"]);
}

#[test]
fn undeclared_bit_select_becomes_a_net_named_with_its_index() {
    let m = parse("module m (); INVX1 U1 (.A(foo[3]), .Y(y)); endmodule");
    assert_eq!(inst_conns(&m, 0)[0].1, ["foo[3]"]);
    assert_eq!(m.warnings.len(), 1);
}

#[test]
fn escaped_instance_and_net_names() {
    let m = parse(
        "module m (); wire [3:0] cnt; wire \\n$5 , n1, clk;
  DFFRX1 \\cnt_reg[3] (.D(n1), .CK(clk), .Q(cnt[3]), .QN(\\n$5 ));
endmodule",
    );
    assert_eq!(s(m.inst_name(0)), "cnt_reg[3]");
    let c = inst_conns(&m, 0);
    assert_eq!(c[2].1, ["cnt[3]"]);
    assert_eq!(c[3].1, ["n$5"]);
    assert_eq!(m.find_inst(b"cnt_reg[3]"), Some(0));
    assert_eq!(m.find_inst(b"nope"), None);
}

#[test]
fn reverse_index_lists_every_pin_on_a_bit() {
    let m = parse(SIMPLE);
    let pins: Vec<_> = m
        .pins_on(bit(&m, "n1"))
        .map(|p| (s(m.inst_name(p.inst)), s(m.conn_pin(p.conn).unwrap()), p.pos))
        .collect();
    assert_eq!(
        pins,
        [("U1".to_string(), "Y".to_string(), 0), ("U2".to_string(), "A".to_string(), 0)]
    );
    assert_eq!(m.pins_on(bit(&m, "b[1]")).count(), 0);
}

#[test]
fn reverse_index_reports_position_inside_a_bus_connection() {
    let m = parse("module m (); wire [3:0] a; RAM u (.D({a[3:2], a[0]})); endmodule");
    let p: Vec<_> = m.pins_on(bit(&m, "a[0]")).map(|p| p.pos).collect();
    assert_eq!(p, [2]);
}

#[test]
fn gate_primitives_with_and_without_instance_names() {
    let m = parse("module m (); wire y, a, b, z; and (y, a, b); not g1 (z, y); endmodule");
    assert_eq!(m.num_insts(), 2);
    assert_eq!(s(m.inst_cell(0)), "and");
    assert_eq!(s(m.inst_name(0)), "");
    assert_eq!(inst_conns(&m, 0).len(), 3);
    assert_eq!(s(m.inst_name(1)), "g1");
}

#[test]
fn parameters_and_delays_are_skipped() {
    let m = parse(
        "module m (); wire a, b;
  parameter P = 3;
  FOO #(.W(4), .S(\"x;y\")) u (.a(b));
  BAR #5 v (.a(a));
endmodule",
    );
    assert_eq!(m.num_insts(), 2);
    assert_eq!(s(m.inst_name(0)), "u");
    assert_eq!(s(m.inst_cell(1)), "BAR");
    assert_eq!(s(m.inst_name(1)), "v");
}

#[test]
fn multiple_names_per_declaration() {
    let m = parse("module m (); wire a, b, c; wire [3:0] x, y; endmodule");
    for n in ["a", "b", "c"] {
        assert!(m.find_net(n.as_bytes()).is_some());
    }
    assert!(m.bit_of(m.find_net(b"y").unwrap(), 3).is_some());
    assert_eq!(m.nbits(), 11);
}

#[test]
fn bit_names_round_trip() {
    let m = parse("module m (); wire [3:0] x; wire s; endmodule");
    assert_eq!(m.bit_name(bit(&m, "x[2]")), "x[2]");
    assert_eq!(m.bit_name(bit(&m, "s")), "s");
}

#[test]
fn port_bits_map_both_ways() {
    let m = parse("module m (a, y); input [3:0] a; output y; endmodule");
    assert_eq!(m.port_of_bit(bit(&m, "a[0]")), Some((0, 0)));
    assert_eq!(m.port_of_bit(bit(&m, "a[3]")), Some((0, 3)));
    assert_eq!(m.port_of_bit(bit(&m, "y")), Some((1, 0)));
    assert_eq!(m.port_bit(0, 3), Some(bit(&m, "a[3]")));
    assert_eq!(m.port_bit(0, 4), None);
    assert_eq!(m.find_port(b"y"), Some(1));
}

#[test]
fn internal_nets_are_not_ports() {
    let m = parse(SIMPLE);
    assert_eq!(m.port_of_bit(bit(&m, "n1")), None);
}

#[test]
fn syntax_error_reports_module_and_line() {
    let err = try_parse("module m ();\n wire a, b;\n INVX1 U1 (.A(a) .Y(b));\nendmodule")
        .unwrap_err();
    let msg = format!("{err:#}");
    assert!(msg.contains("line 3"), "{msg}");
    assert!(msg.contains("m"), "{msg}");
}

#[test]
fn header_only_parse_reads_ports_without_instances() {
    let src: &'static [u8] = Box::leak(SIMPLE.to_string().into_boxed_str()).as_bytes();
    let idx = ModuleIndex::build(&[src]).unwrap();
    let h = Module::parse_header(&idx.modules[0]).unwrap();
    assert_eq!(h.num_insts(), 0);
    assert_eq!(h.ports.len(), 3);
    assert_eq!(h.ports[2].dir, Dir::Output);
    assert_eq!(h.port_width(1), 2);
}

/* Wraps the fsm fixture (fsm.v) in a small hierarchy. */
module cfg (clk, d, mode);
  input clk, d;
  output mode;
  DFFX1 mode_reg (.D(d), .CK(clk), .Q(mode));
endmodule

module chip (clk, rst_n, req, ack, cfg_d, out);
  input clk, rst_n, req, ack, cfg_d;
  output out;
  wire mode_w, ns, bo;
  cfg u_cfg (.clk(clk), .d(cfg_d), .mode(mode_w));
  fsm u_fsm (.clk(clk), .rst_n(rst_n), .req(req), .ack(ack), .mode(mode_w),
             .next_state(ns), .branch_ok(bo));
  AND2X1 U1 (.A(ns), .B(bo), .Y(out));
endmodule

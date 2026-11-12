/* Gate-level FSM used by the end-to-end tests.
 *
 *   state[3:0]        the state register
 *   nstate[3:0]       next state
 *   mode ? (state inside {5,9}) : 0   feeds nstate[2]
 *   req toggles state[0], ack holds state[1], state[3] toggles every cycle
 *   next_state, branch_ok   buffered copies of two internal nets
 */
module fsm (clk, rst_n, req, ack, mode, next_state, branch_ok);
  input clk, rst_n, req, ack, mode;
  output next_state, branch_ok;
  wire [3:0] state;
  wire [3:0] nstate;
  wire n3, n2, n1, n0;
  wire is5, is9, is5or9, t0, hold1, branch;

  DFFRX1 \state_reg[3] (.D(nstate[3]), .CK(clk), .RN(rst_n), .Q(state[3]));
  DFFRX1 \state_reg[2] (.D(nstate[2]), .CK(clk), .RN(rst_n), .Q(state[2]), .QN(n2_inv_unused));
  DFFRX1 \state_reg[1] (.D(nstate[1]), .CK(clk), .RN(rst_n), .Q(state[1]));
  DFFRX1 \state_reg[0] (.D(nstate[0]), .CK(clk), .RN(rst_n), .Q(state[0]));

  /* next state bit 2: mode AND (state == 5 or state == 9) */
  INVX1 U10 (.A(state[0]), .Y(n0));
  INVX1 U11 (.A(state[1]), .Y(n1));
  INVX1 U12 (.A(state[2]), .Y(n2));
  INVX1 U13 (.A(state[3]), .Y(n3));
  NOR4X1 U20 (.A(state[3]), .B(n2), .C(state[1]), .D(n0), .Y(is5));
  NOR4X1 U21 (.A(n3), .B(state[2]), .C(state[1]), .D(n0), .Y(is9));
  OR2X1 U22 (.A(is5), .B(is9), .Y(is5or9));
  AND2X1 U23 (.A(mode), .B(is5or9), .Y(nstate[2]));

  /* next state bit 3: toggle */
  INVX1 U30 (.A(state[3]), .Y(nstate[3]));

  /* next state bit 1: ack AND state[1], or state 5 */
  AND2X1 U40 (.A(ack), .B(state[1]), .Y(hold1));
  OR2X1 U41 (.A(hold1), .B(is5), .Y(nstate[1]));

  /* next state bit 0: req ? !state[0] : state[0] */
  MUX2X1 U50 (.A(state[0]), .B(n0), .S(req), .Y(t0));
  BUFX2 U51 (.A(t0), .Y(nstate[0]));

  /* outputs */
  BUFX2 U60 (.A(nstate[2]), .Y(next_state));
  INVX1 U61 (.A(is5or9), .Y(branch));
  BUFX2 U62 (.A(branch), .Y(branch_ok));
endmodule

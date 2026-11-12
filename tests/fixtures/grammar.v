/* The two lines of grammar.example, as gates. */
module gram (clk, d, sel, a, b, eq5, eq5_alt, mux_y, mux_alt);
  input clk, sel, a, b;
  input [3:0] d;
  output eq5, eq5_alt, mux_y, mux_alt;
  wire [3:0] cnt;
  wire n1, n3, t1, t2, nsel, m1, m2, k1, k2;

  DFFX1 \cnt_reg[3] (.D(d[3]), .CK(clk), .Q(cnt[3]));
  DFFX1 \cnt_reg[2] (.D(d[2]), .CK(clk), .Q(cnt[2]));
  DFFX1 \cnt_reg[1] (.D(d[1]), .CK(clk), .Q(cnt[1]));
  DFFX1 \cnt_reg[0] (.D(d[0]), .CK(clk), .Q(cnt[0]));

  /* cnt[0] & (!cnt[1]) & cnt[2] & (!cnt[3]) */
  INVX1 U1 (.A(cnt[1]), .Y(n1));
  INVX1 U2 (.A(cnt[3]), .Y(n3));
  AND2X1 U3 (.A(cnt[0]), .B(n1), .Y(t1));
  AND2X1 U4 (.A(cnt[2]), .B(n3), .Y(t2));
  AND2X1 U5 (.A(t1), .B(t2), .Y(eq5));

  /* The same function built from other gates. */
  NAND2X1 U6 (.A(cnt[0]), .B(cnt[2]), .Y(k1));
  NOR3X1 U7 (.A(k1), .B(cnt[1]), .C(cnt[3]), .Y(eq5_alt));

  /* sel & a | !sel & b */
  INVX1 U10 (.A(sel), .Y(nsel));
  AND2X1 U11 (.A(sel), .B(a), .Y(m1));
  AND2X1 U12 (.A(nsel), .B(b), .Y(m2));
  OR2X1 U13 (.A(m1), .B(m2), .Y(mux_y));

  /* The same function as one and-or-invert cell and an inverter. */
  AOI22X1 U14 (.A0(sel), .A1(a), .B0(nsel), .B1(b), .Y(k2));
  INVX1 U15 (.A(k2), .Y(mux_alt));
endmodule

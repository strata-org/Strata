program Core;
procedure callee0(x0 : bool) returns (y0 : bool)
spec {
  ensures [post_0]: (y0 == !x0);
} {
  y0 := !x0;
};
procedure callee1(x1 : bool) returns (y1 : bool)
spec {
  ensures [post_1]: (y1 == x1);
} {
  y1 := x1;
};
procedure callee2(x2 : bool, x3 : bool) returns (y2 : bool)
spec {
  ensures [post_2]: (y2 == (x2 && x3));
} {
  y2 := x2 && x3;
};
procedure caller(a : bool, b : bool) returns (r0 : bool, r1 : bool, r2 : bool) {
  call r0 := callee0(a);
  call r1 := callee1(b);
  call r2 := callee2(r0, r1);
};

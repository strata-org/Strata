program Core;
var g : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 > 0);
  ensures [post_0]: (y0 == x0);
  ensures [post_g0]: (g == old g + 1);
  modifies g;
} {
  y0 := x0;
  g := g + 1;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  ensures [post_1]: (y1 == x1 * 2);
} {
  y1 := x1 * 2;
};
procedure callee2(x2 : int) returns (y2 : int) {
  y2 := x2;
};
procedure caller(a : int) returns (r0 : int, r1 : int, r2 : int) spec {
  modifies g;
} {
  call r0 := callee0(a);
  call r1 := callee1(r0);
  call r2 := callee2(r1);
};

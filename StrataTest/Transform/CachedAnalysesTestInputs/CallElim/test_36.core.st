program Core;
var g : int;
var h : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 > 0);
  ensures [post_0]: (y0 == old g);
  ensures [post_g]: (g == x0);
  modifies g;
} {
  y0 := g;
  g := x0;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  ensures [post_1]: (y1 == old h);
  ensures [post_h]: (h == x1);
  modifies h;
} {
  y1 := h;
  h := x1;
};
procedure caller(a : int, b : int) returns (r0 : int, r1 : int) spec {
  modifies g;
  modifies h;
} {
  call r0 := callee0(a);
  call r1 := callee1(b);
};

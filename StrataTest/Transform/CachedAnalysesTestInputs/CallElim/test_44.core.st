program Core;
var g : int;
var h : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  ensures [post_0]: (y0 == old g);
  ensures [post_g0]: (g == x0);
  modifies g;
} {
  y0 := g;
  g := x0;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  ensures [post_1]: (y1 == old h);
  ensures [post_h1]: (h == x1);
  modifies h;
} {
  y1 := h;
  h := x1;
};
procedure callee2(x2 : int) returns (y2 : int)
spec {
  requires [pre_2]: (x2 >= 0);
  ensures [post_2]: (y2 == x2 + old g + old h);
  modifies g;
  modifies h;
} {
  y2 := x2 + g + h;
  g := 0;
  h := 0;
};
procedure caller(a : int) returns (r0 : int, r1 : int, r2 : int) spec {
  modifies g;
  modifies h;
} {
  call r0 := callee0(a);
  call r1 := callee1(a);
  call r2 := callee2(r0);
};

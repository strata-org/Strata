program Core;
var g : int;
var h : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  ensures [post_0]: (y0 == x0 + 1);
  ensures [post_g0]: (g == old g + 1);
  modifies g;
} {
  y0 := x0 + 1;
  g := g + 1;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  requires [pre_1]: (x1 >= 0);
  ensures [post_1]: (y1 == x1 + 2);
  ensures [post_h1]: (h == old h + 1);
  modifies h;
} {
  y1 := x1 + 2;
  h := h + 1;
};
procedure callee2(x2 : int) returns (y2 : int)
spec {
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
  call r1 := callee1(r0);
  call r2 := callee2(r1);
};

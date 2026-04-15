program Core;
var g : int;
var h : bool;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  ensures [post_0]: (y0 == old g + x0);
  ensures [post_g]: (g == x0);
  ensures [post_h]: (h == (x0 > 0));
  modifies g;
  modifies h;
} {
  y0 := g + x0;
  g := x0;
  h := x0 > 0;
};
procedure caller(a : int) returns (r0 : int) spec {
  modifies g;
  modifies h;
} {
  call r0 := callee0(a);
};

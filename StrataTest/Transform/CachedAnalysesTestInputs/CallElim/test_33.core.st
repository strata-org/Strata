program Core;
var g : bool;
procedure callee0(x0 : bool) returns (y0 : bool)
spec {
  requires [pre_0]: (x0 == true);
  ensures [post_0]: (y0 == old g);
  ensures [post_g]: (g == x0);
  modifies g;
} {
  y0 := g;
  g := x0;
};
procedure caller(a : bool) returns (r0 : bool) spec {
  modifies g;
} {
  call r0 := callee0(a);
};

program Core;
var g : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  requires [pre_g]: (g >= 0);
  ensures [post_0]: (y0 == old g);
  ensures [post_g]: (g == old g + x0);
  modifies g;
} {
  y0 := g;
  g := g + x0;
};
procedure caller(a : int) returns (r0 : int, r1 : int) spec {
  modifies g;
} {
  call r0 := callee0(a);
  call r1 := callee0(a);
};

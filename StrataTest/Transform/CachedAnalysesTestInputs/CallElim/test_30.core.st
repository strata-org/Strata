program Core;
var g : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  ensures [post_0]: (y0 == x0);
  ensures [post_g]: (g == old g + 1);
  modifies g;
} {
  y0 := x0;
  g := g + 1;
};
procedure caller(a : int) returns (r0 : int) spec {
  modifies g;
} {
  call r0 := callee0(a);
};

program Core;
var g : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  ensures [post_0]: (y0 == old g);
  modifies g;
} {
  y0 := g;
  g := x0;
};
procedure caller(a : int) returns (r0 : int) spec {
  modifies g;
} {
  call r0 := callee0(a);
};

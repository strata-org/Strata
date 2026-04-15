program Core;
var g : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  ensures [post_0]: (y0 == x0 + old g);
  ensures [post_g]: (g == 0);
  modifies g;
} {
  y0 := x0 + g;
  g := 0;
};
procedure caller(a : int) returns (r0 : int) spec {
  modifies g;
} {
  call r0 := callee0(a);
};

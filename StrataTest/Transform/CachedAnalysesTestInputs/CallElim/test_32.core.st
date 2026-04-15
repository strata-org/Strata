program Core;
var g : int;
var h : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  ensures [post_0]: (y0 == old g + old h);
  modifies g;
  modifies h;
} {
  y0 := g + h;
  g := x0;
  h := x0;
};
procedure caller(a : int) returns (r0 : int) spec {
  modifies g;
  modifies h;
} {
  call r0 := callee0(a);
};

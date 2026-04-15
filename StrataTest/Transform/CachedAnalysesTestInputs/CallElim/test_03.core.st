program Core;
procedure callee0(x0 : int, x1 : int) returns (y0 : int) {
  y0 := x0 + x1;
};
procedure caller(a : int, b : int) returns (r0 : int) {
  call r0 := callee0(a, b);
};

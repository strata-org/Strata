program Core;
procedure callee0(x0 : int) returns (y0 : int) {
  y0 := x0 + 1;
};
procedure caller(a : int) returns (r0 : int) {
  call r0 := callee0(a);
};

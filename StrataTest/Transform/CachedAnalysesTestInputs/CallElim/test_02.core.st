program Core;
procedure callee0(x0 : bool) returns (y0 : bool) {
  y0 := x0;
};
procedure caller(a : bool) returns (r0 : bool) {
  call r0 := callee0(a);
};

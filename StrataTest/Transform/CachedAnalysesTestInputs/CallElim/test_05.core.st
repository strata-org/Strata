program Core;
procedure callee0(x0 : int) returns (y0 : int, y1 : int) {
  y0 := x0;
  y1 := x0 + 1;
};
procedure caller(a : int) returns (r0 : int, r1 : int) {
  call r0, r1 := callee0(a);
};

program Core;
procedure callee0() returns (y0 : int) {
  y0 := 0;
};
procedure caller() returns (r0 : int) {
  call r0 := callee0();
};

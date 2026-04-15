program Core;
procedure callee0(x0 : int) returns (y0 : int) {
  y0 := x0 * 2;
};
procedure caller(a : int) returns (r0 : int) {
  var tmp : int;
  tmp := a + 1;
  call r0 := callee0(tmp);
};

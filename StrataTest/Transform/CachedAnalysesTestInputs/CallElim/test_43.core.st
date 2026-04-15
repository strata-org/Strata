program Core;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  ensures [post_0]: (y0 == x0);
} {
  y0 := x0;
};
procedure callee1(x1 : int) returns (y1 : int) {
  y1 := x1 + 1;
};
procedure callee2(x2 : int) returns (y2 : int)
spec {
  requires [pre_2]: (x2 >= 0);
  ensures [post_2]: (y2 == x2 + 2);
} {
  y2 := x2 + 2;
};
procedure caller(a : int) returns (r0 : int, r1 : int, r2 : int) {
  call r0 := callee0(a);
  call r1 := callee1(r0);
  call r2 := callee2(r1);
  call r0 := callee0(r2);
};

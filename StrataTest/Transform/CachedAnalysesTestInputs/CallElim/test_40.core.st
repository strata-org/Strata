program Core;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  ensures [post_0]: (y0 == x0 + 1);
} {
  y0 := x0 + 1;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  requires [pre_1]: (x1 >= 0);
  ensures [post_1]: (y1 == x1 + 2);
} {
  y1 := x1 + 2;
};
procedure callee2(x2 : int) returns (y2 : int)
spec {
  requires [pre_2]: (x2 >= 0);
  ensures [post_2]: (y2 == x2 + 3);
} {
  y2 := x2 + 3;
};
procedure caller(a : int) returns (r0 : int, r1 : int, r2 : int) {
  call r0 := callee0(a);
  call r1 := callee1(r0);
  call r2 := callee2(r1);
};

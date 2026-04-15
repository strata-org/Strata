program Core;
var g : int;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  requires [pre_0]: (x0 >= 0);
  ensures [post_0]: (y0 == x0);
} {
  y0 := x0;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  requires [pre_1]: (x1 > 0);
  ensures [post_1]: (y1 == x1 - 1);
} {
  y1 := x1 - 1;
};
procedure callee2(x2 : int) returns (y2 : int)
spec {
  ensures [post_2]: (y2 == old g + x2);
  ensures [post_g2]: (g == x2);
  modifies g;
} {
  y2 := g + x2;
  g := x2;
};
procedure callee3(x3 : int) returns (y3 : int) {
  y3 := x3 + 100;
};
procedure caller(a : int) returns (r0 : int, r1 : int, r2 : int, r3 : int) spec {
  modifies g;
} {
  call r0 := callee0(a);
  call r1 := callee1(r0);
  call r2 := callee2(r1);
  call r3 := callee3(r2);
  call r0 := callee0(r3);
};

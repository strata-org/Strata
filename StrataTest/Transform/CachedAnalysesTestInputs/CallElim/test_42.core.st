program Core;
procedure callee0(x0 : int) returns (y0 : int)
spec {
  ensures [post_0]: (y0 >= x0);
} {
  y0 := x0 + 1;
};
procedure callee1(x1 : int) returns (y1 : int)
spec {
  ensures [post_1]: (y1 >= x1);
} {
  y1 := x1 + 1;
};
procedure callee2(x2 : int) returns (y2 : int)
spec {
  ensures [post_2]: (y2 >= x2);
} {
  y2 := x2 + 1;
};
procedure callee3(x3 : int) returns (y3 : int)
spec {
  ensures [post_3]: (y3 >= x3);
} {
  y3 := x3 + 1;
};
procedure caller(a : int) returns (r0 : int, r1 : int, r2 : int, r3 : int) {
  call r0 := callee0(a);
  call r1 := callee1(a);
  call r2 := callee2(a);
  call r3 := callee3(a);
};

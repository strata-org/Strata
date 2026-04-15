program Core;
procedure f1(x : int) returns (y : int) spec { ensures [post]: (y >= x); } { y := x; };
procedure f2(x : int) returns (y : int) spec { ensures [post]: (y >= x); } { y := x + 1; };
procedure caller(a : int) returns (r : int) { call r := f1(a); call r := f2(r); };

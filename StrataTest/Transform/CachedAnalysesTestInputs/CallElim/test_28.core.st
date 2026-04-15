program Core;
procedure f1(x : int) returns (y : int) spec { ensures [post]: (y >= 0); } { if (x >= 0) { y := x; } else { y := 0 - x; } };
procedure f2(x : int) returns (y : int) { y := x + 1; };
procedure caller(a : int) returns (b : int) { call b := f1(a); call b := f2(b); };

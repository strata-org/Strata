program Core;
procedure f1(x : int) returns (y : int) spec { requires [pre]: (x > 0); ensures [post]: (y > 0); } { y := x; };
procedure f2(x : int) returns (y : int) spec { ensures [post]: (y == x + x); } { y := x + x; };
procedure caller(a : int) returns (b : int) { call b := f1(a); call b := f2(b); };

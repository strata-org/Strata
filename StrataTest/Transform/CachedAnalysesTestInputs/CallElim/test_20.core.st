program Core;
procedure inc(x : int) returns (y : int) spec { ensures [post]: (y == x + 1); } { y := x + 1; };
procedure dec(x : int) returns (y : int) { y := x - 1; };
procedure caller(a : int) returns (b : int) { call b := inc(a); call b := dec(b); };

program Core;
procedure square(x : int) returns (y : int) spec { ensures [post]: (y == x * x); } { y := x * x; };
procedure negate(x : int) returns (y : int) { y := 0 - x; };
procedure caller(a : int) returns (b : int) { call b := square(a); call b := negate(b); };

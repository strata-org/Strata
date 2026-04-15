program Core;
procedure add(x : int, y : int) returns (z : int) spec { ensures [post]: (z == x + y); } { z := x + y; };
procedure mul2(x : int) returns (y : int) { y := x + x; };
procedure caller(a : int, b : int) returns (r : int) { var t : int; call t := add(a, b); call r := mul2(t); };

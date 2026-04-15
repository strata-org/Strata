program Core;
procedure id1(x : int) returns (y : int) spec { ensures [p1]: (y == x); } { y := x; };
procedure id2(x : int) returns (y : int) spec { ensures [p2]: (y == x); } { y := x; };
procedure caller(a : int) returns (b : int) { call b := id1(a); call b := id2(b); call b := id1(b); };

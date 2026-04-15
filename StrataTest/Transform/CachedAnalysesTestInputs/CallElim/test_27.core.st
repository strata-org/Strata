program Core;
procedure f1() returns () { };
procedure f2(x : int) returns (y : int) spec { ensures [post]: (y == x); } { y := x; };
procedure caller(a : int) returns (b : int) { call f1(); call b := f2(a); };

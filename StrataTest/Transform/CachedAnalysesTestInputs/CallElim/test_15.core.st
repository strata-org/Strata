program Core;
procedure callee(x : int) returns (y : int)
spec { free requires [pre]: (x >= 0); ensures [post]: (y == x); }
{ y := x; };
procedure caller(a : int) returns (b : int) { call b := callee(a); };

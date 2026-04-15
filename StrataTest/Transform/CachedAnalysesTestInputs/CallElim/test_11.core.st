program Core;
procedure callee(x : int) returns (y : int)
spec { ensures [post]: (y == x + 1); }
{ y := x + 1; };
procedure caller(a : int) returns (b : int) { call b := callee(a); };

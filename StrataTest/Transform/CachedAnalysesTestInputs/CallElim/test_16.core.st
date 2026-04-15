program Core;
procedure callee(x : int) returns (y : int)
spec { ensures [post]: (y == x * 2); }
{ y := x + x; };
procedure caller(a : int) returns (b : int) { call b := callee(a); call b := callee(b); };

program Core;
procedure callee(x : bool) returns (y : bool)
spec { ensures [post]: (y == !x); }
{ y := !x; };
procedure caller(a : bool) returns (b : bool) { call b := callee(a); };

program Core;
procedure callee(x : int) returns (y : int)
spec { requires [pre]: (x >= 0); ensures [post]: (y >= 0); }
{ y := x; };
procedure caller(a : int) returns (b : int) { call b := callee(a); };

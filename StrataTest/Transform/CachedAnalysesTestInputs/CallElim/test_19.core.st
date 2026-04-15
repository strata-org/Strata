program Core;
procedure callee(x : int) returns (y : int)
spec { requires [pre]: (x >= 0); requires [pre2]: (x < 100); ensures [post]: (y == x); }
{ y := x; };
procedure caller(a : int) returns (b : int) { call b := callee(a); call b := callee(b); };

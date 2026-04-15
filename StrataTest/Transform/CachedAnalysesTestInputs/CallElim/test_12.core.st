program Core;
procedure callee(x : int, y : int) returns (z : int)
spec { requires [pre]: (x >= 0); requires [pre2]: (y >= 0); ensures [post]: (z == x + y); }
{ z := x + y; };
procedure caller(a : int) returns (r : int) { call r := callee(a, a); };

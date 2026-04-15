program Core;
procedure abs(x : int) returns (y : int)
spec { ensures [post]: (y >= 0); }
{ if (x >= 0) { y := x; } else { y := 0 - x; } };
procedure caller(a : int) returns (b : int) { call b := abs(a); };

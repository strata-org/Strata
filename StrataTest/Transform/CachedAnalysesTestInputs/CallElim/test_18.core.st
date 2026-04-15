program Core;
procedure max(x : int, y : int) returns (z : int)
spec { ensures [ge_x]: (z >= x); ensures [ge_y]: (z >= y); }
{ if (x >= y) { z := x; } else { z := y; } };
procedure caller(a : int, b : int) returns (r : int) { call r := max(a, b); };

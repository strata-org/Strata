program Core;
procedure f1(x : int) returns (y : int) { y := x; };
procedure f2(x : int) returns (y : int) { y := x + 1; };
procedure caller(a : int) returns (b : int, c : int) { call b := f1(a); call c := f2(a); };

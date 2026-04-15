program Core;
procedure leaf(x : int) returns (y : int) {
  y := x + 1;
};
procedure caller(a : int) returns (b : int) {
  call b := leaf(a);
};

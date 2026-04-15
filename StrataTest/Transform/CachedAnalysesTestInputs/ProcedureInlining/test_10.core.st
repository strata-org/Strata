program Core;
procedure leaf(x : int) returns (y : int) {
  y := x + 1;
};
procedure mid(a : int) returns (b : int) {
  call b := leaf(a);
};
procedure top(n : int) returns (r : int) {
  call r := mid(n);
};

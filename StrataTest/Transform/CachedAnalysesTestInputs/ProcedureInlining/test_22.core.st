program Core;
procedure leaf_a(x : int) returns (y : int) {
  y := x * 2;
};
procedure leaf_b(x : int) returns (y : int) {
  y := x + 10;
};
procedure branch(n : int) returns (r : int) {
  if (n > 0) {
    call r := leaf_a(n);
  } else {
    call r := leaf_b(n);
  }
};
procedure entry(v : int) returns (w : int) {
  call w := branch(v);
};

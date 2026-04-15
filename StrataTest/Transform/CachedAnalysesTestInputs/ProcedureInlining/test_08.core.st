program Core;
procedure pair_swap(x : int, y : int) returns (a : int, b : int) {
  a := y;
  b := x;
};
procedure do_swap(p : int, q : int) returns (u : int, v : int) {
  call u, v := pair_swap(p, q);
};

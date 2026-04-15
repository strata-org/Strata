program Core;
procedure swap(x : int, y : int) returns (a : int, b : int) {
  a := y;
  b := x;
};
procedure ordered(p : int, q : int) returns (u : int, v : int) {
  if (p > q) {
    call u, v := swap(p, q);
  } else {
    u := p;
    v := q;
  }
};
procedure sort_pair(i : int, j : int) returns (lo : int, hi : int) {
  call lo, hi := ordered(i, j);
};

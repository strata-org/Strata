program Core;
procedure first(x : int, y : int) returns (r : int) {
  r := x;
};
procedure second(x : int, y : int) returns (r : int) {
  r := y;
};
procedure select(x : int, y : int, pick_first : bool) returns (r : int) {
  if (pick_first) {
    call r := first(x, y);
  } else {
    call r := second(x, y);
  }
};
procedure double_select(a : int, b : int) returns (r1 : int, r2 : int) {
  call r1 := select(a, b, true);
  call r2 := select(a, b, false);
};

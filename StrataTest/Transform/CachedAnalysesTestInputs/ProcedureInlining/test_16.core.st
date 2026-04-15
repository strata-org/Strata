program Core;
procedure max(a : int, b : int) returns (r : int) {
  if (a > b) {
    r := a;
  } else {
    r := b;
  }
};
procedure clamp_low(x : int) returns (y : int) {
  call y := max(x, 0);
};
procedure process(n : int) returns (m : int) {
  call m := clamp_low(n);
};

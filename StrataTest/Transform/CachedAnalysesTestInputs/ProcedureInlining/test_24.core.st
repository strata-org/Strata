program Core;
procedure min(a : int, b : int) returns (r : int) {
  if (a < b) {
    r := a;
  } else {
    r := b;
  }
};
procedure clamp(x : int, lo : int, hi : int) returns (r : int) {
  var tmp : int;
  if (x < lo) {
    r := lo;
  } else {
    call r := min(x, hi);
  }
};
procedure bounded(v : int) returns (w : int) {
  call w := clamp(v, 0, 100);
};
procedure process(n : int) returns (m : int) {
  call m := bounded(n);
};

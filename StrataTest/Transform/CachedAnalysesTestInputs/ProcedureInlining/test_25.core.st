program Core;
procedure neg(x : int) returns (r : int) {
  r := 0 - x;
};
procedure abs(x : int) returns (r : int) {
  if (x < 0) {
    call r := neg(x);
  } else {
    r := x;
  }
};
procedure sum_abs(a : int, b : int) returns (s : int) {
  var va : int;
  var vb : int;
  call va := abs(a);
  call vb := abs(b);
  s := va + vb;
};
procedure main(x : int, y : int) returns (r : int) {
  call r := sum_abs(x, y);
};

program Core;
procedure inc(x : int) returns (r : int) {
  r := x + 1;
};
procedure dec(x : int) returns (r : int) {
  r := x - 1;
};
procedure fork(x : int, up : bool) returns (r : int) {
  if (up) {
    call r := inc(x);
  } else {
    call r := dec(x);
  }
};
procedure apply_twice(x : int, b1 : bool, b2 : bool) returns (r : int) {
  var tmp : int;
  call tmp := fork(x, b1);
  call r := fork(tmp, b2);
};

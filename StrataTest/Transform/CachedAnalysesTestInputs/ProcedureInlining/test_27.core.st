program Core;
procedure mk_pair(x : int, y : int) returns (a : int, b : int) {
  a := x;
  b := y;
};
procedure add_pair(x : int, y : int) returns (s : int) {
  var a : int;
  var b : int;
  call a, b := mk_pair(x, y);
  s := a + b;
};
procedure scale_add(x : int, y : int, k : int) returns (r : int) {
  var s : int;
  call s := add_pair(x, y);
  r := s * k;
};
procedure entry(p : int, q : int) returns (out : int) {
  call out := scale_add(p, q, 3);
};

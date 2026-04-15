program Core;
procedure pack(a : int, b : int, c : int) returns (x : int, y : int, z : int) {
  x := a;
  y := b;
  z := c;
};
procedure shift(a : int, b : int, c : int) returns (x : int, y : int, z : int) {
  call x, y, z := pack(b, c, a);
};
procedure double_shift(a : int, b : int, c : int) returns (x : int, y : int, z : int) {
  var p : int;
  var q : int;
  var r : int;
  call p, q, r := shift(a, b, c);
  call x, y, z := shift(p, q, r);
};
procedure quad_shift(a : int, b : int, c : int) returns (x : int, y : int, z : int) {
  var p : int;
  var q : int;
  var r : int;
  call p, q, r := double_shift(a, b, c);
  call x, y, z := double_shift(p, q, r);
};
procedure entry(a : int, b : int, c : int) returns (x : int, y : int, z : int) {
  call x, y, z := quad_shift(a, b, c);
};

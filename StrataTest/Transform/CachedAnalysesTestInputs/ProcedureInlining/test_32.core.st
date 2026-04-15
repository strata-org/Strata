program Core;
procedure op_add(x : int, y : int) returns (r : int) {
  r := x + y;
};
procedure op_mul(x : int, y : int) returns (r : int) {
  r := x * y;
};
procedure op_sub(x : int, y : int) returns (r : int) {
  r := x - y;
};
procedure combine(a : int, b : int, c : int) returns (r : int) {
  var s : int;
  var p : int;
  call s := op_add(a, b);
  call p := op_mul(s, c);
  call r := op_sub(p, a);
};

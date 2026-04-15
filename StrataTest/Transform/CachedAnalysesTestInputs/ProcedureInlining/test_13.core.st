program Core;
procedure mul2(x : int) returns (r : int) {
  r := x * 2;
};
procedure add_then_mul(a : int, b : int) returns (c : int) {
  var s : int;
  s := a + b;
  call c := mul2(s);
};
procedure compute(n : int) returns (m : int) {
  call m := add_then_mul(n, n);
};

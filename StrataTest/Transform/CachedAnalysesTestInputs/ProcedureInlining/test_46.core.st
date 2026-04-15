program Core;
procedure add(x : int, y : int) returns (r : int) {
  r := x + y;
};
procedure mul(x : int, y : int) returns (r : int) {
  r := x * y;
};
procedure sub(x : int, y : int) returns (r : int) {
  r := x - y;
};
procedure poly(x : int) returns (r : int) {
  var x2 : int;
  var t1 : int;
  var t2 : int;
  call x2 := mul(x, x);
  call t1 := mul(3, x2);
  call t2 := mul(2, x);
  var s : int;
  call s := add(t1, t2);
  call r := add(s, 1);
};
procedure eval_poly(n : int) returns (m : int) {
  call m := poly(n);
};

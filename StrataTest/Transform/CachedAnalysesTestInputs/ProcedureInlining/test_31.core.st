program Core;
procedure left(x : int) returns (r : int) {
  r := x * 2;
};
procedure right(x : int) returns (r : int) {
  r := x * 3;
};
procedure merge(a : int, b : int) returns (r : int) {
  r := a + b;
};
procedure diamond(x : int) returns (r : int) {
  var l : int;
  var ri : int;
  call l := left(x);
  call ri := right(x);
  call r := merge(l, ri);
};

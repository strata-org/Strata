program Core;
procedure square(x : int) returns (r : int) {
  r := x * x;
};
procedure add(a : int, b : int) returns (r : int) {
  r := a + b;
};
procedure sum_of_squares(x : int, y : int) returns (r : int) {
  var sx : int;
  var sy : int;
  call sx := square(x);
  call sy := square(y);
  call r := add(sx, sy);
};
procedure main(p : int, q : int) returns (out : int) {
  call out := sum_of_squares(p, q);
};

program Core;
procedure compute_a(x : int) returns (r : int) {
  r := x + 10;
};
procedure compute_b(x : int) returns (r : int) {
  r := x * 5;
};
procedure compute_c(x : int) returns (r : int) {
  r := x - 3;
};
procedure compute_d(x : int) returns (r : int) {
  r := x + x;
};
procedure pipeline(n : int) returns (r : int) {
  var a : int;
  var b : int;
  var c : int;
  call a := compute_a(n);
  call b := compute_b(n);
  call c := compute_c(n);
  call r := compute_d(a + b + c);
};

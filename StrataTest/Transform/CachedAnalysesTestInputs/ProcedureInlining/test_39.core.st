program Core;
procedure half(x : int) returns (r : int) {
  r := x / 2;
};
procedure double(x : int) returns (r : int) {
  r := x * 2;
};
procedure id_via_half_double(x : int) returns (r : int) {
  var h : int;
  call h := half(x);
  call r := double(h);
};
procedure id_via_double_half(x : int) returns (r : int) {
  var d : int;
  call d := double(x);
  call r := half(d);
};
procedure both(n : int) returns (a : int, b : int) {
  call a := id_via_half_double(n);
  call b := id_via_double_half(n);
};

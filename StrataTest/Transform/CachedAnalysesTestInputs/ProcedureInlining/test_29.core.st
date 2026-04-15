program Core;
procedure cube(x : int) returns (r : int) {
  r := x * x * x;
};
procedure offset(x : int, d : int) returns (r : int) {
  r := x + d;
};
procedure cube_offset(x : int, d : int) returns (r : int) {
  var c : int;
  call c := cube(x);
  call r := offset(c, d);
};
procedure main(n : int) returns (m : int) {
  call m := cube_offset(n, 7);
};

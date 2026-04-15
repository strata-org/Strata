program Core;
procedure read_x(x : int) returns (r : int) {
  r := x;
};
procedure read_y(y : int) returns (r : int) {
  r := y;
};
procedure read_z(z : int) returns (r : int) {
  r := z;
};
procedure gather(x : int, y : int, z : int) returns (s : int) {
  var a : int;
  var b : int;
  var c : int;
  call a := read_x(x);
  call b := read_y(y);
  call c := read_z(z);
  s := a + b + c;
};

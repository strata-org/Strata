program Core;
procedure identity(x : int) returns (y : int) {
  y := x;
};
procedure double_call(a : int) returns (b : int) {
  var tmp : int;
  call tmp := identity(a);
  call b := identity(tmp);
};

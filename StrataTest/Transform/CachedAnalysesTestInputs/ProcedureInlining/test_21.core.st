program Core;
procedure add1(x : int) returns (r : int) {
  r := x + 1;
};
procedure add2(x : int) returns (r : int) {
  var tmp : int;
  call tmp := add1(x);
  call r := add1(tmp);
};
procedure add4(x : int) returns (r : int) {
  var tmp : int;
  call tmp := add2(x);
  call r := add2(tmp);
};
procedure go(n : int) returns (m : int) {
  call m := add4(n);
};

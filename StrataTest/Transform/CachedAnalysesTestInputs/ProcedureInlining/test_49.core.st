program Core;
procedure lit_zero() returns (r : int) {
  r := 0;
};
procedure lit_one() returns (r : int) {
  r := 1;
};
procedure choose(flag : bool, a : int, b : int) returns (r : int) {
  if (flag) {
    r := a;
  } else {
    r := b;
  }
};
procedure build(flag : bool) returns (r : int) {
  var z : int;
  var o : int;
  call z := lit_zero();
  call o := lit_one();
  call r := choose(flag, z, o);
};
procedure double_build(f1 : bool, f2 : bool) returns (a : int, b : int) {
  call a := build(f1);
  call b := build(f2);
};
procedure entry(x : bool, y : bool) returns (p : int, q : int) {
  call p, q := double_build(x, y);
};

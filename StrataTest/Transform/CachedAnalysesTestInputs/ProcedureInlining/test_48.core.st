program Core;
procedure incr(x : int) returns (r : int) {
  r := x + 1;
};
procedure step2(x : int) returns (r : int) {
  var t : int;
  call t := incr(x);
  call r := incr(t);
};
procedure step3(x : int) returns (r : int) {
  var t : int;
  call t := step2(x);
  call r := incr(t);
};
procedure step4(x : int) returns (r : int) {
  var t : int;
  call t := step3(x);
  call r := incr(t);
};
procedure step5(x : int) returns (r : int) {
  var t : int;
  call t := step4(x);
  call r := incr(t);
};
procedure run(n : int) returns (m : int) {
  call m := step5(n);
};

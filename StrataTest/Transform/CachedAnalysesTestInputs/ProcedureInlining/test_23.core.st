program Core;
procedure noop() returns () {
};
procedure step1(x : int) returns (y : int) {
  call noop();
  y := x + 1;
};
procedure step2(x : int) returns (y : int) {
  var tmp : int;
  call tmp := step1(x);
  y := tmp + 1;
};
procedure run(n : int) returns (r : int) {
  call r := step2(n);
};

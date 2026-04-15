program Core;
procedure leaf_a(x : int) returns (r : int) {
  r := x + 1;
};
procedure leaf_b(x : int) returns (r : int) {
  r := x + 2;
};
procedure mid(x : int) returns (r : int) {
  var a : int;
  var b : int;
  call a := leaf_a(x);
  call b := leaf_b(x);
  r := a + b;
};
procedure upper(x : int) returns (r : int) {
  call r := mid(x);
};
procedure top(x : int) returns (r : int) {
  call r := upper(x);
};

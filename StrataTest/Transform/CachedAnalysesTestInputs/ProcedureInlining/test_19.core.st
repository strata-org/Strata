program Core;
procedure triple(x : int) returns (r : int) {
  r := x * 3;
};
procedure add_triple(a : int, b : int) returns (c : int) {
  var ta : int;
  call ta := triple(a);
  c := ta + b;
};
procedure run(n : int, m : int) returns (out : int) {
  call out := add_triple(n, m);
};

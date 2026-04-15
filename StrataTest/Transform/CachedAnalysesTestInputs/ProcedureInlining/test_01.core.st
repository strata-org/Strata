program Core;
procedure add(x : int, y : int) returns (r : int) {
  r := x + y;
};
procedure use_add(a : int, b : int) returns (c : int) {
  call c := add(a, b);
};

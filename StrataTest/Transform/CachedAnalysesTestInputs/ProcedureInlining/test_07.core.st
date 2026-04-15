program Core;
procedure sub(x : int, y : int) returns (r : int) {
  r := x - y;
};
procedure diff(a : int, b : int) returns (c : int) {
  call c := sub(a, b);
};

program Core;
procedure inc(n : int) returns (m : int) {
  m := n + 1;
};
procedure caller(x : int) returns (y : int) {
  call y := inc(x);
};

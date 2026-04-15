program Core;
procedure base(x : int) returns (y : int) {
  y := x + 1;
};
procedure level2(a : int) returns (b : int) {
  call b := base(a);
};
procedure level1(p : int) returns (q : int) {
  call q := level2(p);
};
procedure top(n : int) returns (r : int) {
  call r := level1(n);
};

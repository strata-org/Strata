program Core;
procedure square(x : int) returns (r : int) {
  r := x * x;
};
procedure compute(a : int) returns (b : int) {
  call b := square(a);
};

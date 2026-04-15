program Core;
procedure double(x : int) returns (r : int) {
  r := x + x;
};
procedure halve(x : int) returns (r : int) {
  r := x / 2;
};
procedure transform(x : int, flag : bool) returns (r : int) {
  if (flag) {
    call r := double(x);
  } else {
    call r := halve(x);
  }
};
procedure apply(n : int, b : bool) returns (m : int) {
  call m := transform(n, b);
};

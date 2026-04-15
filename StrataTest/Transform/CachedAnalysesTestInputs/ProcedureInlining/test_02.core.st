program Core;
procedure negate(x : bool) returns (y : bool) {
  y := !x;
};
procedure wrap_negate(a : bool) returns (b : bool) {
  call b := negate(a);
};

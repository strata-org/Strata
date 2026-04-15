program Core;
procedure zero() returns (r : int) {
  r := 0;
};
procedure get_zero() returns (v : int) {
  call v := zero();
};

program Core;
procedure fa(x : int) returns (r : int) {
  r := x + 1;
};
procedure fb(x : int) returns (r : int) {
  r := x + 2;
};
procedure fan(n : int) returns (a : int, b : int) {
  call a := fa(n);
  call b := fb(n);
};

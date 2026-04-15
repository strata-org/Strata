program Core;
procedure const_five() returns (r : int) {
  r := 5;
};
procedure add_five(x : int) returns (y : int) {
  var five : int;
  call five := const_five();
  y := x + five;
};
procedure main(a : int) returns (b : int) {
  call b := add_five(a);
};

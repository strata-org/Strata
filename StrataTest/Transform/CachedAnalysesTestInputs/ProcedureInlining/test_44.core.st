program Core;
procedure zero() returns (r : int) {
  r := 0;
};
procedure succ(n : int) returns (r : int) {
  r := n + 1;
};
procedure make_one() returns (r : int) {
  var z : int;
  call z := zero();
  call r := succ(z);
};
procedure make_two() returns (r : int) {
  var one : int;
  call one := make_one();
  call r := succ(one);
};
procedure make_three() returns (r : int) {
  var two : int;
  call two := make_two();
  call r := succ(two);
};

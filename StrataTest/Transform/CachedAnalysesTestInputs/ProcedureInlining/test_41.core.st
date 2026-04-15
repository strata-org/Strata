program Core;
procedure bottom(a : int, b : int) returns (r : int) {
  r := a * b;
};
procedure layer3(x : int, y : int) returns (r : int) {
  var s : int;
  s := x + 1;
  call r := bottom(s, y);
};
procedure layer2(x : int, y : int) returns (r : int) {
  var d : int;
  d := y - 1;
  call r := layer3(x, d);
};
procedure layer1(x : int, y : int) returns (r : int) {
  call r := layer2(x, y);
};
procedure entry(n : int, m : int) returns (out : int) {
  call out := layer1(n, m);
};

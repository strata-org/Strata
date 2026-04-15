program Core;
procedure p4(x : int) returns (y : int) {
  y := x + 1;
};
procedure p3(x : int) returns (y : int) {
  call y := p4(x);
};
procedure p2(x : int) returns (y : int) {
  call y := p3(x);
};
procedure p1(x : int) returns (y : int) {
  call y := p2(x);
};
procedure p0(x : int) returns (y : int) {
  call y := p1(x);
};

program Core;
procedure leaf(x : int) returns (r : int) {
  r := x;
};
procedure d4(x : int) returns (r : int) {
  call r := leaf(x);
};
procedure d3(x : int) returns (r : int) {
  var tmp : int;
  call tmp := d4(x);
  r := tmp + 1;
};
procedure d2(x : int) returns (r : int) {
  var tmp : int;
  call tmp := d3(x);
  r := tmp + 1;
};
procedure d1(x : int) returns (r : int) {
  var tmp : int;
  call tmp := d2(x);
  r := tmp + 1;
};
procedure d0(x : int) returns (r : int) {
  var tmp : int;
  call tmp := d1(x);
  r := tmp + 1;
};

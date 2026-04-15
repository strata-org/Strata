program Core;
procedure dec(n : int) returns (m : int) {
  m := n - 1;
};
procedure dec_twice(x : int) returns (y : int) {
  var tmp : int;
  call tmp := dec(x);
  call y := dec(tmp);
};
procedure go(v : int) returns (w : int) {
  call w := dec_twice(v);
};

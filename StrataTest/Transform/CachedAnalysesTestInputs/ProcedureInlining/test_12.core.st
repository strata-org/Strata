program Core;
procedure flip(x : bool) returns (y : bool) {
  y := !x;
};
procedure double_flip(a : bool) returns (b : bool) {
  var tmp : bool;
  call tmp := flip(a);
  call b := flip(tmp);
};
procedure run_flip(v : bool) returns (w : bool) {
  call w := double_flip(v);
};

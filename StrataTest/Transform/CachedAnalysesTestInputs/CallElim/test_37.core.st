program Core;
var g : int;
procedure callee0(x0 : int) returns ()
spec {
  ensures [post_g]: (g == old g + x0);
  modifies g;
} {
  g := g + x0;
};
procedure caller(a : int) returns () spec {
  modifies g;
} {
  call callee0(a);
};

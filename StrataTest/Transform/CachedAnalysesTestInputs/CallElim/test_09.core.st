program Core;
procedure callee0(x0 : int) returns () {
};
procedure caller(a : int) returns () {
  call callee0(a);
};

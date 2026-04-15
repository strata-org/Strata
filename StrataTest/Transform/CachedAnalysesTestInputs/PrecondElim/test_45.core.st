program Core;
procedure inner(x : int) returns (y : int)
{
  y := (x * x) div 4;
};
procedure outer(a : int, b : int) returns (z : int)
{
  var t1 : int;
  var t2 : int;
  call t1 := inner(a);
  call t2 := inner(b);
  z := (t1 + t2) div 2;
};

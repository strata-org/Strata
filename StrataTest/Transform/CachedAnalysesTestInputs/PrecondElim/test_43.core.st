program Core;
procedure proc0(x : int, d : int) returns (y : int)
{
  var t1 : int;
  var t2 : int;
  t1 := x div d;
  t2 := (t1 + x) div (d + 1);
  y := t1 + t2;
};

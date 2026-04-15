program Core;
procedure proc0(x : int, y : int, z : int) returns (r : int)
{
  var a : int;
  var b : int;
  a := (x + y) div z;
  b := (x - y) mod z;
  r := a * b;
};

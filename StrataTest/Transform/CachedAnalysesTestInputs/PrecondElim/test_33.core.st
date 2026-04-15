program Core;
procedure step(x : int) returns (y : int)
{
  y := x div 3;
};
procedure run(a : int) returns (b : int)
{
  var t : int;
  call t := step(a);
  b := t + 1;
};
procedure top(n : int) returns (m : int)
{
  call m := run(n);
};

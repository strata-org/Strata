program Core;
procedure scale(x : int) returns (y : int)
{
  y := x * 3;
};
procedure shrink(x : int) returns (y : int)
{
  y := x div 4;
};
procedure pipeline(a : int) returns (b : int)
{
  var t : int;
  call t := scale(a);
  call b := shrink(t);
};

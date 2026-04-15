program Core;
procedure addOne(x : int) returns (y : int)
{
  y := x + 1;
};
procedure divTwo(x : int) returns (y : int)
{
  y := x div 2;
};
procedure combined(a : int) returns (b : int)
{
  var t : int;
  call t := addOne(a);
  call b := divTwo(t);
};

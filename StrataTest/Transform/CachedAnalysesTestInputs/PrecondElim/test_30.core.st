program Core;
procedure helper(x : int) returns (y : int)
{
  y := x div 2;
};
procedure main0(a : int) returns (b : int)
{
  call b := helper(a);
};

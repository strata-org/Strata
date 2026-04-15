program Core;
procedure half(x : int) returns (y : int)
{
  y := x div 2;
};
procedure quarter(x : int) returns (y : int)
{
  call y := half(x);
  call y := half(y);
};

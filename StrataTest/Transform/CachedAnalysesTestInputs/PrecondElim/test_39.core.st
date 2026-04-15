program Core;
procedure double(x : int) returns (y : int)
{
  y := x + x;
};
procedure halve(x : int) returns (y : int)
{
  y := x div 2;
};
procedure roundTrip(a : int) returns (b : int)
{
  var t : int;
  call t := double(a);
  call b := halve(t);
};
procedure outer(n : int) returns (m : int)
{
  call m := roundTrip(n);
};

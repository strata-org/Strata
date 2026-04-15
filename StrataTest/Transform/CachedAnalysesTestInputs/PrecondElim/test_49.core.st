program Core;
procedure square(x : int) returns (y : int)
{
  y := x * x;
};
procedure normalize(x : int, d : int) returns (y : int)
{
  var s : int;
  call s := square(x);
  y := s div d;
};
procedure blend(a : int, b : int, w : int) returns (r : int)
{
  var na : int;
  var nb : int;
  call na := normalize(a, w);
  call nb := normalize(b, w);
  r := (na + nb) div 2;
};
procedure top(x : int, y : int) returns (z : int)
{
  call z := blend(x, y, 5);
};

program Core;
procedure avg(a : int, b : int) returns (y : int)
{
  y := (a + b) div 2;
};
procedure weightedAvg(x : int, y : int, w : int) returns (r : int)
{
  var s : int;
  call s := avg(x, y);
  r := (s * w) div (w + 1);
};
procedure top(a : int, b : int) returns (z : int)
{
  call z := weightedAvg(a, b, 3);
};

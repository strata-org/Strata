program Core;
procedure proc0(x : int, d : int) returns (y : int)
{
  var q : int;
  q := x div d;
  y := q * d + (x mod d);
};

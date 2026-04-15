program Core;
procedure proc0(a : int, b : int, c : int, d : int) returns (y : int)
{
  var p : int;
  var q : int;
  var r : int;
  p := a div b;
  q := c mod d;
  r := (p + q) div (b + d);
  y := r;
};

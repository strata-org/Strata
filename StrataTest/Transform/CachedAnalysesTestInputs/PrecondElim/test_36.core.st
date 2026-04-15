program Core;
procedure compute(x : int, d : int) returns (q : int, r : int)
{
  q := x div d;
  r := x mod d;
};
procedure verify(n : int) returns (ok : int)
{
  var q : int;
  var r : int;
  call q, r := compute(n, 5);
  ok := q * 5 + r;
};

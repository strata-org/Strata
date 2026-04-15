program Core;
procedure divProc(x : int, d : int) returns (y : int)
{
  y := x div d;
};
procedure modProc(x : int, d : int) returns (y : int)
{
  y := x mod d;
};
procedure caller(n : int) returns (q : int, r : int)
{
  call q := divProc(n, 3);
  call r := modProc(n, 3);
};

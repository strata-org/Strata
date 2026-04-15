program Core;
procedure divBy(x : int, d : int) returns (y : int)
{
  y := x div d;
};
procedure modBy(x : int, d : int) returns (y : int)
{
  y := x mod d;
};
procedure splitA(n : int) returns (a : int)
{
  call a := divBy(n, 2);
};
procedure splitB(n : int) returns (b : int)
{
  call b := modBy(n, 2);
};

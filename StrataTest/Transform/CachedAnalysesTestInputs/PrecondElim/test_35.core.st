program Core;
procedure proc0(x : int) returns (y : int)
{
  y := x mod 7;
};
procedure proc1(a : int) returns (b : int)
{
  call b := proc0(a);
};
procedure proc2(n : int) returns (m : int)
{
  call m := proc1(n);
};

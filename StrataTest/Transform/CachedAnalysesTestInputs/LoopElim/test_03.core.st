program Core;

procedure accumulate(n : int) returns (sum : int)
{
  var i : int;
  sum := 0;
  i := 1;
  while (i <= n)
  {
    sum := sum + i;
    i := i + 1;
  }
};

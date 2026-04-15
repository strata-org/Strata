program Core;

procedure inc(n : int) returns (r : int)
{
  var i : int;
  r := 0;
  i := 0;
  while (i < n)
  {
    r := r + 1;
    i := i + 1;
  }
};

procedure dec(n : int) returns (r : int)
{
  r := n;
  while (r > 0)
  {
    r := r - 1;
  }
};

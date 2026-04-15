program Core;

procedure countDown(n : int) returns (r : int)
{
  var i : int;
  i := n;
  r := 0;
  while (i > 0)
  {
    r := r + i;
    i := i - 1;
  }
};

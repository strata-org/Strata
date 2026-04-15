program Core;

procedure skipLoop(n : int) returns (r : int)
{
  var i : int;
  r := 0;
  i := 0;
  while (i < n)
  {
    i := i + 2;
    r := r + 1;
  }
};

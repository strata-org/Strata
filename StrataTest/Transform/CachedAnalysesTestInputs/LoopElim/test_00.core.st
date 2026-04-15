program Core;

procedure simpleLoop(n : int) returns (r : int)
{
  var i : int;
  i := 0;
  r := 0;
  while (i < n)
  {
    r := r + 1;
    i := i + 1;
  }
};

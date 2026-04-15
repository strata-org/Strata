program Core;

procedure findMax(a : int, b : int, n : int) returns (m : int)
{
  var i : int;
  m := a;
  i := 0;
  while (i < n)
  {
    if (b > m) {
      m := b;
    }
    i := i + 1;
  }
};

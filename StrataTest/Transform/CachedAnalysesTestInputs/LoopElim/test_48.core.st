program Core;

procedure sequentialAndNested(n : int, m : int) returns (r1 : int, r2 : int)
spec {
  requires (n >= 0);
  requires (m >= 0);
}
{
  var i : int;
  var j : int;
  r1 := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant r1 == i
  {
    r1 := r1 + 1;
    i := i + 1;
  }
  r2 := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
  {
    j := 0;
    while (j < m)
      decreases m - j
      invariant j <= m
    {
      r2 := r2 + 1;
      j := j + 1;
    }
    i := i + 1;
  }
};

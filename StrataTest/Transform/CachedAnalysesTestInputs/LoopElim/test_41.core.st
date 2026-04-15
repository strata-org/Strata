program Core;

procedure nestedWithDecreases(n : int, m : int) returns (total : int)
spec {
  requires (n >= 0);
  requires (m >= 0);
}
{
  var i : int;
  var j : int;
  total := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant total >= 0
  {
    j := 0;
    while (j < m)
      decreases m - j
      invariant j <= m
    {
      total := total + 1;
      j := j + 1;
    }
    i := i + 1;
  }
};

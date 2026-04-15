program Core;

procedure triangleNested(n : int) returns (count : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  var j : int;
  count := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
  {
    j := 0;
    while (j < i)
      decreases i - j
      invariant j <= i
    {
      count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
};

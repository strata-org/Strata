program Core;

procedure nestedAccumulate(n : int) returns (s : int, p : int)
spec {
  requires (n >= 1);
}
{
  var i : int;
  var j : int;
  var rowSum : int;
  s := 0;
  p := 1;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant s >= 0
    invariant p >= 1
  {
    rowSum := 0;
    j := 0;
    while (j <= i)
      decreases i - j + 1
      invariant j <= i + 1
      invariant rowSum >= 0
    {
      rowSum := rowSum + j;
      j := j + 1;
    }
    s := s + rowSum;
    if (rowSum > 0) {
      p := p * 2;
    }
    i := i + 1;
  }
};

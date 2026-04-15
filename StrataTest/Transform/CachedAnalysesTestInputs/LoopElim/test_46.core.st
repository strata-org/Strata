program Core;

procedure matMulLike(n : int) returns (total : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  var j : int;
  var k : int;
  var partial : int;
  total := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
  {
    j := 0;
    while (j < n)
      decreases n - j
      invariant j <= n
    {
      partial := 0;
      k := 0;
      while (k < n)
        decreases n - k
        invariant k <= n
        invariant partial >= 0
      {
        partial := partial + 1;
        k := k + 1;
      }
      total := total + partial;
      j := j + 1;
    }
    i := i + 1;
  }
};

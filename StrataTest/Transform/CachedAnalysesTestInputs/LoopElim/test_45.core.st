program Core;

procedure tripleNested(a : int, b : int, c : int) returns (count : int)
spec {
  requires (a >= 0);
  requires (b >= 0);
  requires (c >= 0);
}
{
  var i : int;
  var j : int;
  var k : int;
  count := 0;
  i := 0;
  while (i < a)
    invariant i <= a
  {
    j := 0;
    while (j < b)
      invariant j <= b
    {
      k := 0;
      while (k < c)
        invariant k <= c
      {
        count := count + 1;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
};

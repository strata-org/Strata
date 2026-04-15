program Core;

procedure nestedWithConditional(rows : int, cols : int) returns (evens : int, odds : int)
spec {
  requires (rows >= 0);
  requires (cols >= 0);
}
{
  var i : int;
  var j : int;
  var val : int;
  evens := 0;
  odds := 0;
  i := 0;
  while (i < rows)
    invariant i <= rows
    invariant evens >= 0
    invariant odds >= 0
  {
    j := 0;
    while (j < cols)
      invariant j <= cols
    {
      val := i + j;
      if ((val mod 2) == 0) {
        evens := evens + 1;
      } else {
        odds := odds + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
};

program Core;

procedure decreasingLoop(n : int) returns (r : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  r := 0;
  i := n;
  while (i > 0)
    invariant i >= 0
  {
    r := r + 1;
    i := i - 1;
  }
};

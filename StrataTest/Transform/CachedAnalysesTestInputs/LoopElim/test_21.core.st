program Core;

procedure countDownTerm(n : int) returns (r : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  r := 0;
  i := n;
  while (i > 0)
    decreases i
    invariant i >= 0
    invariant r >= 0
  {
    r := r + 1;
    i := i - 1;
  }
};

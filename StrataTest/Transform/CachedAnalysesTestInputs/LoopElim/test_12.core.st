program Core;

procedure nonNegAccum(n : int) returns (r : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  r := 0;
  i := 0;
  while (i < n)
    invariant r >= 0
  {
    r := r + 1;
    i := i + 1;
  }
};

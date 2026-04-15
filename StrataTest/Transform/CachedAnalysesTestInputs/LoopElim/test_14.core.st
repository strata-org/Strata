program Core;

procedure doubleAccum(n : int) returns (r : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  r := 0;
  i := 0;
  while (i < n)
    invariant r == 2 * i
  {
    r := r + 2;
    i := i + 1;
  }
};

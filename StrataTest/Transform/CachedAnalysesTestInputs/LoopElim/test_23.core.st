program Core;

procedure triangular(n : int) returns (t : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  t := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant ((i * (i - 1)) div 2 == t)
  {
    t := t + i;
    i := i + 1;
  }
};

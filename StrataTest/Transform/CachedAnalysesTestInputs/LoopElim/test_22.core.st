program Core;

procedure factorial(n : int) returns (f : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  f := 1;
  i := 1;
  while (i <= n)
    decreases n - i + 1
    invariant i >= 1
    invariant f >= 1
  {
    f := f * i;
    i := i + 1;
  }
};

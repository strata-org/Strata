program Core;

procedure sumTerminating(n : int) returns (s : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  s := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant s >= 0
  {
    s := s + i;
    i := i + 1;
  }
};

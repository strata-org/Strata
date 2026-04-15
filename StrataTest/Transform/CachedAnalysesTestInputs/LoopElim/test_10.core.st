program Core;

procedure sumWithInv(n : int) returns (s : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  s := 0;
  i := 0;
  while (i < n)
    invariant i <= n
  {
    s := s + i;
    i := i + 1;
  }
};

program Core;

procedure countWithInvs(n : int) returns (c : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  c := 0;
  i := 0;
  while (i < n)
    invariant i <= n
    invariant c == i
  {
    c := c + 1;
    i := i + 1;
  }
};

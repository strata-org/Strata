program Core;

procedure sumUp(n : int) returns (s : int)
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

procedure sumDown(n : int) returns (s : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  s := 0;
  i := n;
  while (i > 0)
    invariant i >= 0
  {
    s := s + i;
    i := i - 1;
  }
};

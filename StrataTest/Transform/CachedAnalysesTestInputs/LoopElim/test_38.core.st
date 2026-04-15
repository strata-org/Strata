program Core;

procedure seqSum(n : int) returns (s1 : int, s2 : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  s1 := 0;
  i := 0;
  while (i < n)
    invariant i <= n
  {
    s1 := s1 + i;
    i := i + 1;
  }
  s2 := 0;
  i := 0;
  while (i < n)
    invariant i <= n
  {
    s2 := s2 + i * i;
    i := i + 1;
  }
};

procedure seqProd(n : int) returns (p : int)
spec {
  requires (n >= 1);
}
{
  var i : int;
  p := 1;
  i := 1;
  while (i <= n)
    invariant i >= 1
    invariant p >= 1
  {
    p := p * i;
    i := i + 1;
  }
};

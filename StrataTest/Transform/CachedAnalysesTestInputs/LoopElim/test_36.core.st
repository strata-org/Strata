program Core;

procedure evenCount(n : int) returns (ec : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  ec := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
  {
    if ((i mod 2) == 0) {
      ec := ec + 1;
    }
    i := i + 1;
  }
};

procedure oddCount(n : int) returns (oc : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  oc := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
  {
    if ((i mod 2) == 1) {
      oc := oc + 1;
    }
    i := i + 1;
  }
};

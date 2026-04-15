program Core;

procedure initArray(n : int) returns (count : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  count := 0;
  i := 0;
  while (i < n)
    invariant i <= n
    invariant count == i
  {
    count := count + 1;
    i := i + 1;
  }
};

procedure clearArray(n : int) returns (count : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  count := n;
  i := 0;
  while (i < n)
    invariant i <= n
    invariant count == n - i
  {
    count := count - 1;
    i := i + 1;
  }
};

procedure copyArray(n : int) returns (copied : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  copied := 0;
  i := 0;
  while (i < n)
    invariant i <= n
  {
    copied := copied + 1;
    i := i + 1;
  }
};

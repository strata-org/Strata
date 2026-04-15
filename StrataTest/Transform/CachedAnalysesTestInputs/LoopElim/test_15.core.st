program Core;

procedure twoVarInvariant(n : int) returns (a : int, b : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  a := 0;
  b := 0;
  i := 0;
  while (i < n)
    invariant a == i
    invariant b == i
  {
    a := a + 1;
    b := b + 1;
    i := i + 1;
  }
};

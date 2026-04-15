program Core;

procedure fibLike(n : int) returns (a : int)
spec {
  requires (n >= 0);
}
{
  var b : int;
  var i : int;
  var tmp : int;
  a := 0;
  b := 1;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant a >= 0
    invariant b >= 1
  {
    tmp := a + b;
    a := b;
    b := tmp;
    i := i + 1;
  }
};

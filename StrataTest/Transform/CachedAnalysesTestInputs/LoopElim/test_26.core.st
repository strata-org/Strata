program Core;

procedure gcdLike(a : int, b : int) returns (g : int)
spec {
  requires (a > 0);
  requires (b >= 0);
}
{
  var x : int;
  var y : int;
  x := a;
  y := b;
  while (y > 0)
    decreases y
    invariant x >= 0
    invariant y >= 0
  {
    var t : int;
    t := y;
    y := x mod y;
    x := t;
  }
  g := x;
};

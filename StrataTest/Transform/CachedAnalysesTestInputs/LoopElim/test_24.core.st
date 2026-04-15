program Core;

procedure mulTerminating(a : int, b : int) returns (p : int)
spec {
  requires (a >= 0);
  requires (b >= 0);
}
{
  var i : int;
  p := 0;
  i := 0;
  while (i < b)
    decreases b - i
    invariant p == a * i
    invariant i <= b
  {
    p := p + a;
    i := i + 1;
  }
};

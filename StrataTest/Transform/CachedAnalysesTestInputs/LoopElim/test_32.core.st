program Core;

procedure addLoop(a : int, b : int) returns (r : int)
spec {
  requires (b >= 0);
}
{
  var i : int;
  r := a;
  i := 0;
  while (i < b)
    decreases b - i
    invariant r == a + i
    invariant i <= b
  {
    r := r + 1;
    i := i + 1;
  }
};

procedure subLoop(a : int, b : int) returns (r : int)
spec {
  requires (b >= 0);
}
{
  var i : int;
  r := a;
  i := 0;
  while (i < b)
    decreases b - i
    invariant r == a - i
    invariant i <= b
  {
    r := r - 1;
    i := i + 1;
  }
};

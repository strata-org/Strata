program Core;

procedure convergeToZero(start : int) returns (steps : int)
spec {
  requires (start >= 0);
}
{
  var x : int;
  x := start;
  steps := 0;
  while (x > 0)
    decreases x
    invariant x >= 0
  {
    x := x - 1;
    steps := steps + 1;
  }
};

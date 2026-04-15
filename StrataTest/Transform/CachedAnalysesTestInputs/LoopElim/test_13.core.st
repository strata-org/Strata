program Core;

procedure boundedIncrement(lo : int, hi : int) returns (x : int)
spec {
  requires (lo <= hi);
}
{
  x := lo;
  while (x < hi)
    invariant x >= lo
    invariant x <= hi
  {
    x := x + 1;
  }
};

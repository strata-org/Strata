program Core;

procedure absVal(x : int) returns (r : int)
{
  var v : int;
  if (x >= 0) {
    v := x;
  } else {
    v := 0 - x;
  }
  r := 0;
  while (r < v)
  {
    r := r + 1;
  }
};

procedure negate(x : int) returns (r : int)
spec {
  requires (x >= 0);
}
{
  var i : int;
  r := 0;
  i := 0;
  while (i < x)
    invariant i <= x
    invariant r == 0 - i
  {
    r := r - 1;
    i := i + 1;
  }
};

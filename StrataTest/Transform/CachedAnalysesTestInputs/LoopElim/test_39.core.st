program Core;

procedure sumPositive(a : int, b : int) returns (s : int)
spec {
  requires (a >= 0);
  requires (b >= a);
}
{
  var i : int;
  s := 0;
  i := a;
  while (i < b)
    decreases b - i
    invariant i >= a
    invariant i <= b
  {
    s := s + i;
    i := i + 1;
  }
};

procedure sumNegative(a : int, b : int) returns (s : int)
spec {
  requires (a <= 0);
  requires (b <= a);
}
{
  var i : int;
  s := 0;
  i := a;
  while (i > b)
    decreases i - b
    invariant i <= a
    invariant i >= b
  {
    s := s + i;
    i := i - 1;
  }
};

procedure combineResults(x : int) returns (r : int)
spec {
  requires (x >= 0);
}
{
  var i : int;
  r := 0;
  i := 0;
  while (i < x)
  {
    r := r + 2;
    i := i + 1;
  }
};

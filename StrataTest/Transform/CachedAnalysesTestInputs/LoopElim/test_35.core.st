program Core;

procedure minLoop(a : int, b : int) returns (m : int)
spec {
  requires (a >= 0);
  requires (b >= 0);
}
{
  var i : int;
  m := a;
  i := 0;
  while (i < b)
    invariant i <= b
  {
    if (m > b - i) {
      m := b - i;
    }
    i := i + 1;
  }
};

procedure maxLoop(a : int, b : int) returns (m : int)
spec {
  requires (a >= 0);
  requires (b >= 0);
}
{
  var i : int;
  m := 0;
  i := 0;
  while (i < a + b)
    invariant i <= a + b
  {
    if (i > m) {
      m := i;
    }
    i := i + 1;
  }
};

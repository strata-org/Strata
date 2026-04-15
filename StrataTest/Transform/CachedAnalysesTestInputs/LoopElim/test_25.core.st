program Core;

procedure divBySubtract(a : int, b : int) returns (q : int)
spec {
  requires (a >= 0);
  requires (b > 0);
}
{
  var rem : int;
  q := 0;
  rem := a;
  while (rem >= b)
    decreases rem
    invariant rem >= 0
    invariant a == q * b + rem
  {
    rem := rem - b;
    q := q + 1;
  }
};

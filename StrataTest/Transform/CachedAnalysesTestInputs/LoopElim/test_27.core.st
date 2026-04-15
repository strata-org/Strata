program Core;

procedure expBySquaring(base : int, exp : int) returns (result : int)
spec {
  requires (exp >= 0);
}
{
  var b : int;
  var e : int;
  result := 1;
  b := base;
  e := exp;
  while (e > 0)
    decreases e
    invariant e >= 0
    invariant result >= 0
  {
    if ((e mod 2) == 1) {
      result := result * b;
    }
    b := b * b;
    e := e div 2;
  }
};

program Core;

procedure complexMultiProc(n : int) returns (result : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  var j : int;
  var sum : int;
  var max : int;
  result := 0;
  max := 0;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant result >= 0
    invariant max >= 0
  {
    sum := 0;
    j := 0;
    while (j < n)
      decreases n - j
      invariant j <= n
      invariant sum >= 0
    {
      sum := sum + j;
      j := j + 1;
    }
    if (sum > max) {
      max := sum;
    }
    result := result + sum;
    i := i + 1;
  }
};

procedure flatComplex(a : int, b : int) returns (r : int)
spec {
  requires (a >= 0);
  requires (b >= 0);
}
{
  var i : int;
  var phase : int;
  r := 0;
  phase := 0;
  i := 0;
  while (i < a + b)
    decreases a + b - i
    invariant i <= a + b
    invariant r >= 0
  {
    if (i < a) {
      r := r + 1;
      phase := 1;
    } else {
      r := r + 2;
      phase := 2;
    }
    i := i + 1;
  }
};

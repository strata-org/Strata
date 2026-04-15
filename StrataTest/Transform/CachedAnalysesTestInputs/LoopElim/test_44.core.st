program Core;

procedure complexBody(n : int) returns (r : int)
spec {
  requires (n >= 0);
}
{
  var i : int;
  var acc : int;
  var temp : int;
  r := 0;
  acc := 1;
  i := 0;
  while (i < n)
    decreases n - i
    invariant i <= n
    invariant acc >= 1
  {
    temp := acc * 2;
    if (temp > 100) {
      acc := 1;
    } else {
      acc := temp;
    }
    r := r + acc;
    i := i + 1;
  }
};

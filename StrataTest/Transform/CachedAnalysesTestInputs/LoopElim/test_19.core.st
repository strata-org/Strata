program Core;

procedure halveLoop(n : int) returns (count : int)
spec {
  requires (n >= 1);
}
{
  var x : int;
  x := n;
  count := 0;
  while (x >= 2)
    invariant x >= 1
  {
    x := x div 2;
    count := count + 1;
  }
};

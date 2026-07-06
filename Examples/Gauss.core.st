program Core;

procedure sum(n : int, out s : int)
spec {
  //requires (n >= 0);
  ensures (s == ((n * (n + 1)) / 2));
}
{
  var i : int;
  i := 0;
  s := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
    invariant s == (i * (i + 1)) / 2
  {
    i := (i + 1);
    s := (s + i);
  }
};

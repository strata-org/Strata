program Core;

var g : int;

procedure helper(x : int) returns (r : int)
spec {
  ensures (r > x);
  modifies g;
}
{
  g := x;
  r := x + 1;
};

procedure checker(a : int) returns (result : int)
spec {
  requires (a > 0);
  ensures (result > a);
}
{
  result := a + 1;
  assert (result > a);
};

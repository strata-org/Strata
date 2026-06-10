procedure add(x: int, y: int) returns (r: int)
  requires x >= 0
  opaque
  ensures r >= x
{
  r := x + y;
};

procedure main()
  opaque
{
  var a: int := 42;
  assert a > 0;
};

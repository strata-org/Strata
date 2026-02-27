procedure add(x: int, y: int) returns (r: int)
  requires x >= 0
  ensures r >= x
{
  r := x + y;
}

procedure main() {
  var a: int := 42;
  assert a > 0;
}

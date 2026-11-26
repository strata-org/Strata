// An opaque callee is checked on its own: a caller sees only its contract, and its body is
// checked under its precondition.

procedure half(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures r > 0
{
  assert x > 0;
  assert x > 1;
  r := x
};

procedure main()
  opaque
{
  var a: int := half(4);
  assert a > 0;
  assert a == 4
};

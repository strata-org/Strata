// A generic opaque procedure: main sees ident only through its contract, and ident's body is
// checked once for each type at which main calls it (a GOTO program has no type variables).

procedure ident<T>(x: T) returns (r: T)
  opaque
{
  assert false;
  r := x
};

procedure main()
  opaque
{
  var a: int := ident(3);
  assert a == 3
};

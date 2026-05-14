// Test non-deterministic conditions in if and while statements
procedure nondet_if()
  modifies x;
  ensures x >= 0;
{
  var x : int;
  x := 0;
  if * {
    x := 1;
  } else {
    x := 2;
  }
  assert x >= 0;
}

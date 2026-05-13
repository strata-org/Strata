// Test: 2-target gotos emit nondet goto syntax.

procedure TwoTargetNondet()
{
  var x: int;

  entry:
    x := 0;
    goto left, right;

  left:
    assume x == 0;
    x := 1;
    goto join;

  right:
    assume x == 0;
    x := 2;
    goto join;

  join:
    assert x == 1 || x == 2;
    return;
}

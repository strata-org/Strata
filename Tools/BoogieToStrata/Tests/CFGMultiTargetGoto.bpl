// Test: 3+ target gotos are encoded as nested binary nondet.

procedure ThreeTargetGoto()
{
  var x: int;

  entry:
    x := 0;
    goto a, b, c;

  a:
    x := 1;
    goto done;

  b:
    x := 2;
    goto done;

  c:
    x := 3;
    goto done;

  done:
    assert x >= 1 && x <= 3;
    return;
}

procedure FourTargetGoto()
{
  var x: int;

  entry:
    x := 0;
    goto a, b, c, d;

  a:
    x := 1;
    goto done;

  b:
    x := 2;
    goto done;

  c:
    x := 3;
    goto done;

  d:
    x := 4;
    goto done;

  done:
    assert x >= 1 && x <= 4;
    return;
}

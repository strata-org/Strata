// Test for forward goto translation to exit semantics.
// Each procedure uses only forward gotos (no back edges).

procedure SimpleForwardGoto()
{
  var x: int;

  L0:
    x := 1;
    goto L2;

  L1:
    x := 2;
    goto L2;

  L2:
    assert x >= 1;
    return;
}

procedure DiamondGoto(b: bool)
{
  var x: int;

  entry:
    x := 0;
    goto left;

  left:
    x := x + 1;
    goto join;

  right:
    x := x + 2;
    goto join;

  join:
    assert x >= 1;
    return;
}

procedure ChainedForwardGotos()
{
  var x: int;

  A:
    x := 0;
    goto B;

  B:
    x := x + 1;
    goto C;

  C:
    x := x + 1;
    goto D;

  D:
    assert x == 2;
    return;
}

procedure SkipBlocks()
{
  var x: int;

  start:
    x := 10;
    goto done;

  middle:
    x := -1;
    goto done;

  done:
    assert x == 10;
    return;
}

// Test: per-procedure auto-detect. StructuredProc has no gotos (emit structured).
// GotoProc has gotos (emit CFG). Both in the same file.

procedure StructuredProc(x: int) returns (r: int)
{
  if (x > 0) {
    r := x;
  } else {
    r := 0 - x;
  }
}

procedure GotoProc()
{
  var y: int;

  start:
    y := 42;
    goto finish;

  finish:
    assert y == 42;
    return;
}

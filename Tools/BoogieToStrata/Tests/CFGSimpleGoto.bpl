// Test: procedures with single-target gotos emit CFG syntax.
// All gotos have exactly one target (unconditional jumps).

procedure SimpleChain()
{
  var x: int;

  entry:
    x := 0;
    goto next;

  next:
    x := x + 1;
    goto done;

  done:
    assert x == 1;
    return;
}

// Test: backward goto (loop pattern).

procedure LoopViaGoto(n: int)
{
  var i: int;

  entry:
    i := 0;
    goto head;

  head:
    goto body, exit;

  body:
    assume i < n;
    i := i + 1;
    goto head;

  exit:
    assume i >= n;
    assert i >= 0;
    return;
}

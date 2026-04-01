// Test: goto from inside nested if-branch to sibling block (cross-nesting exit).
// Also tests backward goto forming a loop (back-edge to earlier block).
// These patterns require wrapper blocks that extend across nesting boundaries.

type ref;

var g: int;

// Cross-nesting forward goto: goto from inside if-branch to sibling block
procedure CrossNestingForward(x: int)
  modifies g;
{
  var y: int;

  entry:
    y := 0;
    goto check;

  check:
    if (x > 0) {
      y := x;
      goto done;
    }
    y := -x;
    goto done;

  done:
    g := y;
    assert g >= 0;
    return;
}

// Backward goto: bug only visible with multiple loop iterations.
// The old wrapper-extension approach did not model the loop, so a single-pass
// symbolic execution would see x go from 1 to 2 and the assertion would
// (incorrectly) pass. With a proper while-loop encoding the verifier must
// consider arbitrary iterations, so x can exceed 2 and the assertion correctly
// fails.
procedure BackwardGotoBuggy(n: int)
  modifies g;
{
  var x: int;

  entry:
    x := 1;
    goto loop_head;

  loop_head:
    if (x >= n) {
      goto loop_exit;
    }
    x := x * 2;
    goto loop_head;

  loop_exit:
    g := x;
    assert g <= 2;  // BUG: only true for 0-1 iterations
    return;
}

// Backward goto forming a loop: goto from later block back to earlier block
procedure BackwardGotoLoop(n: int)
  modifies g;
{
  var i: int;

  entry:
    i := 0;
    goto loop_head;

  loop_head:
    if (i >= n) {
      goto loop_exit;
    }
    i := i + 1;
    goto loop_head;

  loop_exit:
    g := i;
    assert g >= 0;
    return;
}

// Combined: cross-nesting goto inside a loop body
procedure CrossNestingInLoop(n: int, x: int)
  modifies g;
{
  var i: int;
  var sum: int;

  entry:
    i := 0;
    sum := 0;
    goto loop_head;

  loop_head:
    if (i >= n) {
      goto loop_exit;
    }
    if (x > 0) {
      sum := sum + x;
      goto loop_inc;
    }
    sum := sum - x;
    goto loop_inc;

  loop_inc:
    i := i + 1;
    goto loop_head;

  loop_exit:
    g := sum;
    return;
}

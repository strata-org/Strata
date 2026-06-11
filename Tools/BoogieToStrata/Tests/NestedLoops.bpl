// Test: nested backward gotos forming nested loops.
// The outer loop iterates over i, the inner loop iterates over j.
// This pattern requires nested while(true) encoding without label shadowing.

type ref;

var g: int;

// Nested loops via backward gotos: outer loop over i, inner loop over j.
// Sum of 0..n-1 for each outer iteration, accumulated in sum.
procedure NestedLoops(n: int, m: int)
  modifies g;
{
  var i: int;
  var j: int;
  var sum: int;

  entry:
    i := 0;
    sum := 0;
    goto outer_head;

  outer_head:
    if (i >= n) {
      goto outer_exit;
    }
    j := 0;
    goto inner_head;

  inner_head:
    if (j >= m) {
      goto inner_exit;
    }
    sum := sum + 1;
    j := j + 1;
    goto inner_head;

  inner_exit:
    i := i + 1;
    goto outer_head;

  outer_exit:
    g := sum;
    return;
}

// Nested loops with cross-nesting goto from inner loop body to outer loop block
procedure NestedLoopsCrossNesting(n: int, m: int, x: int)
  modifies g;
{
  var i: int;
  var j: int;
  var sum: int;

  entry:
    i := 0;
    sum := 0;
    goto outer_head;

  outer_head:
    if (i >= n) {
      goto outer_exit;
    }
    j := 0;
    goto inner_head;

  inner_head:
    if (j >= m) {
      goto inner_exit;
    }
    if (x > 0) {
      sum := sum + x;
      goto inner_inc;
    }
    sum := sum - x;
    goto inner_inc;

  inner_inc:
    j := j + 1;
    goto inner_head;

  inner_exit:
    i := i + 1;
    goto outer_head;

  outer_exit:
    g := sum;
    return;
}

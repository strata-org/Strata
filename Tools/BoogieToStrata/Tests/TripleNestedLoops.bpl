// Test: triple-nested backward gotos forming three levels of loops.
// Verifies that multi-level delegation of forward targets through
// nested EmitLoopRegion calls works correctly.

type ref;

var g: int;

// Triple-nested loops via backward gotos.
procedure TripleNestedLoops(a: int, b: int, c: int)
  modifies g;
{
  var i: int;
  var j: int;
  var k: int;
  var sum: int;

  entry:
    i := 0;
    sum := 0;
    goto outer_head;

  outer_head:
    if (i >= a) {
      goto outer_exit;
    }
    j := 0;
    goto middle_head;

  middle_head:
    if (j >= b) {
      goto middle_exit;
    }
    k := 0;
    goto inner_head;

  inner_head:
    if (k >= c) {
      goto inner_exit;
    }
    sum := sum + 1;
    k := k + 1;
    goto inner_head;

  inner_exit:
    j := j + 1;
    goto middle_head;

  middle_exit:
    i := i + 1;
    goto outer_head;

  outer_exit:
    g := sum;
    return;
}

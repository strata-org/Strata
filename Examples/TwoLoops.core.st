program Core;

const N : int;
axiom [ax_N]: (0 <= N);

// Minimal reproducer for the duplicate-label bug in Stmt.removeLoopsM.
//
// Two top-level blocks, each containing one loop. With the original
// p.body.map Stmt.removeLoops, the counter resets to 0 for each
// top-level statement, so both loops receive loop_num = 0 and produce
// clashing labels (assume_invariant_0, not_guard_0, invariant_0, ...).
//
// After the fix (Block.removeLoopsM threads the counter), the loops
// receive loop_num = 0 and 1 respectively.

procedure TwoLoops() returns (result : int)
{
  var i : int;
  var j : int;

  i := 0;
  while (i < N)
  invariant ((0 <= i) && (i <= N))
  {
      i := (i + 1);
  }

  j := 0;
  while ((j < N))
  invariant ((0 <= j) && (j <= N))
  {
      j := (j + 1);
  }
  
};

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:proposal-rw2022`
- `verus-examples:rw2022_script`
- `vlir-tests:tests/LoopSimpleWithSpec`
- Gap: `decreases` preservation
-/

private def decreasesMetadataSeed : Strata.Program :=
#strata
program Boole;

// Target shape: this loop should carry semantic `decreases n - i` metadata.
// Today Boole keeps only the working loop/invariant fragment and leaves the
// intended measure as a comment.

procedure loop_measure_seed(n: int) returns (i: int)
spec {
  requires 0 <= n;
  ensures i == n;
}
{
  i := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    // TODO(feature:decreases): preserve `decreases n - i` as semantic metadata.
  {
    i := i + 1;
  }
};
#end

#eval Strata.Boole.verify "cvc5" decreasesMetadataSeed

example : Strata.smtVCsCorrect decreasesMetadataSeed := by
  gen_smt_vcs
  all_goals (try grind)

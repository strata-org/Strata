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
- Gap: Boole lowering does not yet preserve loop `decreases` into Core
-/

private def decreasesMetadataSeed : Strata.Program :=
#strata
program Boole;

// Core now has loop measures. The remaining gap is in the Boole frontend:
// `while_statement` currently lowers with measure = `none`, so this loop's
// intended `decreases n - i` is still kept only as a comment here.

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
    // TODO(feature:decreases): lower this to Core's loop measure field.
  {
    i := i + 1;
  }
};
#end

#eval Strata.Boole.verify "cvc5" decreasesMetadataSeed

example : Strata.smtVCsCorrect decreasesMetadataSeed := by
  gen_smt_vcs
  all_goals (try grind)

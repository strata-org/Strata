/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:trigger_loops` (`choose_example`, `quantifier_example`)
- Verus link:
  `trigger_loops`: https://github.com/verus-lang/verus/blob/main/examples/trigger_loops.rs
- Gap: `choose` operator not faithfully translated
- Intended encoding: `havoc z; assume (∃ z' . g(z')) ==> g(z);`
- Status: implemented — `w := choose z: T . pred(z)` desugars to
  `havoc w; assume pred[z/w]` in the Boole lowering.
-/

private def chooseOperatorSeed : Strata.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

procedure choose_seed(x: int) returns (w: int)
spec {
  requires ∃ z: int . good(z, x);
  ensures good(w, x);
}
{
  w := choose z: int :: good(z, x);
};
#end

/-- info:
Obligation: choose_seed_ensures_1_809
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseOperatorSeed (options := .quiet)

example : Strata.smtVCsCorrect chooseOperatorSeed := by
  gen_smt_vcs
  all_goals (try grind)

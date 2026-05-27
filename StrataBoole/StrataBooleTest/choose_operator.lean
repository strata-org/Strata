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
- Status: implemented — `w := choose z: T :: pred(z)` desugars to:
    assert ∃ z : T . pred(z);   -- existence obligation (soundness guard)
    havoc w;
    assume pred[z/w];
  The existence assertion prevents `assume false` false positives when
  `pred` is unsatisfiable.
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
Obligation: choose_2_876_exists
Property: assert
Result: ✅ pass

Obligation: choose_seed_ensures_1_850
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseOperatorSeed (options := .quiet)

example : Strata.smtVCsCorrect chooseOperatorSeed := by
  gen_smt_vcs
  all_goals (try grind)

-- Regression: an unsatisfiable predicate must be caught by the existence
-- assertion, not silently turned into `assume false` (which would make every
-- subsequent obligation a false positive).
private def chooseUnsatSeed : Strata.Program :=
#strata
program Boole;

procedure choose_unsat() returns (w: int)
spec {
  ensures true;
}
{
  w := choose z: int :: z != z;
};
#end

/-- info:
Obligation: choose_1_1591_exists
Property: assert
Result: ❌ fail

Obligation: choose_unsat_ensures_0_1571
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseUnsatSeed (options := .quiet)

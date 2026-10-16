/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)

---------------------------------------------------------------------

/-!
## `gen_smt_vcs` on programs with function preconditions

A function declared with `requires` is only well-formed at call sites that
establish the precondition; `Core.verify` runs `precondElimPipelinePhase`,
which factors each such call into a well-formedness obligation.
`Core.genVCs` (the reflection path behind `gen_smt_vcs`) used to skip that
phase, so `extractObligations` rejected the program ("function ... still
carries a precondition") and the tactic reported "Failed to generate VCs".

The proof closes each obligation *by name* rather than with `all_goals`, so it
pins the set of obligations in both directions: a dropped one fails with
"Case tag ... not found", an unexpected one with "unsolved goals". `all_goals`
alone would not notice a dropped one — it closes whatever happens to be there.
`set_r_calls_safeDiv_0` is the obligation `precondElim` contributes: the check
that `safeDiv`'s `requires` holds at the call site in `halve`.
-/

namespace Strata

private def funcPrecondPgm : Program :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ int.safeDiv(x, y) }

procedure halve(n : int, out r : int)
spec {
  requires int.gt(n, 0);
  ensures int.le(int.mul(r, 2), n);
}
{
  r := safeDiv(n, 2);
  r := r;
};
#end

theorem halveCorrect : smtVCsCorrect funcPrecondPgm := by
  gen_smt_vcs
  case safeDiv_body_calls_Int.SafeDiv_0 => grind
  case set_r_calls_safeDiv_0 => grind
  case halve_ensures_1 => grind

end Strata

---------------------------------------------------------------------

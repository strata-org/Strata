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
This test pins the fix: the goals below include the well-formedness check
for `safeDiv`'s precondition, and every goal closes.
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
  all_goals grind

end Strata

---------------------------------------------------------------------

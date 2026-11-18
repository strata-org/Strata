/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)

/-!
## `gen_smt_vcs` on integer division by zero

SMT-LIB leaves `div` and `mod` by a zero divisor unspecified, so a goal that
uses them quantifies over the model's values at zero, `divByZero` and
`modByZero`, once for the whole VC.
-/

namespace Strata

/-- Facts that hold in every model. -/
private def divZeroValidPgm : Program :=
#strata
program Core;

procedure P(x : int) {
  assert [same_div]: int.div(x, 0) == int.div(x, 0);
  assert [modT_zero]: int.modT(x, 0) == x;
  assert [divT_sign]: int.divT(5, 0) == int.divT(int.neg(5), 0);
  assert [div_nonzero]: int.div(6, 2) == 3;
};
#end

/-- The original probe: Lean's `5 / 0 = 0` is not a fact of SMT-LIB. -/
private def divZeroProbePgm : Program :=
#strata
program Core;

procedure P() {
  assert [div_zero_probe]: int.div(5, 0) == 0;
};
#end

/-- `divT(a, 0)` is `divByZero |a|` (the `a * b ≥ 0` branch of the encoding
`tdiv(a, b) = ite(a * b ≥ 0, q, -q)` with `q = div(|a|, |b|)`, in
`Core.SMT.Encoder`'s `Int.DivT` case), so `divT(5, 0)` and `divT(-5, 0)` agree in
every model; `modT(x, 0) = x - 0 * tdiv(x, 0) = x`. -/
theorem divZeroValidPgm_correct : smtVCsCorrect divZeroValidPgm := by
  gen_smt_vcs
  all_goals simp

/-- The probe's only goal is the proposition below, which is false: a model may
give `5 div 0` any value, not only Lean's `0`. -/
private def divZeroProbeGoal : Prop :=
  ∀ (divByZero _modByZero : Int → Int), (if (0 : Int) = 0 then divByZero 5 else 5 / 0) = 0

example (h : divZeroProbeGoal) : smtVCsCorrect divZeroProbePgm := by
  gen_smt_vcs
  exact h

example : ¬ divZeroProbeGoal := fun h => by
  simpa using h (fun _ => 1) id

end Strata

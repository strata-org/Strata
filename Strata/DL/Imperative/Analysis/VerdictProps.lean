/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Analysis.Verdict
public import Strata.Util.Relations

/-! # Per-assertion verdicts: properties

## Key results

- `VerdictCorrect.valid_not_failed`: no assertion has both a correct `valid`
  verdict and a correct `failed` one.
- `ValidityReflected.refl`, `ValidityReflected.trans`: validity reflection is
  reflexive and transitive.
-/

public section

namespace Strata.Analysis

open Imperative Strata.Logic

variable {P : PureExpr} {Idx : Type} {EL : Idx → EventLang P (Event P)}

/-- **`valid` and `failed` exclude each other**: no assertion has both a correct
    `valid` verdict and a correct `failed` one. -/
theorem VerdictCorrect.valid_not_failed {I : ConditionInterp P} {E : ProgramEntries EL}
    {p : E.Program} {a : AssertId P} {e : E.Entry} (hv : VerdictCorrect I E p a .valid) :
    ¬ VerdictCorrect I E p a (.failed e) :=
  fun ⟨he, n, trace, hr, hf⟩ => hf (hv e he n trace hr)

/-- Validity reflection is reflexive. -/
theorem ValidityReflected.refl (I : ConditionInterp P) : IsReflexive (ValidityReflected I) :=
  fun _ _ ha => ha

/-- Validity reflection is transitive. -/
theorem ValidityReflected.trans (I : ConditionInterp P) : IsTransitive (ValidityReflected I) :=
  fun _ _ _ h₁ h₂ a ha => h₁ a (h₂ a ha)

end Strata.Analysis

end -- public section

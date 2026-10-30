/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.CmdProps

/-! # Evaluation of the expressions the WP and SSA phases build

The evaluation of the Boolean literals (`ev_tt`, `ev_ff`), results are values (`ev_value`),
and the only free variable of a variable reference is the variable (`fv_var`).

Key theorems: `ev_tt`, `ev_ff`, `ev_value`, `fv_var`.
Key definitions: `ev`. -/

namespace Imperative
namespace WP

public section

variable {P : PureExpr} [HasBool P] [HasFvar P]

/-- The expression language's partial evaluator `P.eval`, under the short name the
    proofs use; `none` when the expression has no value. -/
abbrev ev (F : P.Factory) (σ : SemanticStore P) (e : P.Expr) : Option P.Expr := P.eval F σ e

section
omit [HasFvar P]

/-- `true` evaluates to `true`. -/
theorem ev_tt [HasFvars P] [LawfulHasVal P] {F : P.Factory}
    (hVal : WellFormedSemanticEvalVal (P := P) F) (σ : SemanticStore P) : ev F σ tt = some tt :=
  hVal.identityOnValues _ σ (HasBool.boolIsVal F).1

/-- `false` evaluates to `false`. -/
theorem ev_ff [HasFvars P] [LawfulHasVal P] {F : P.Factory}
    (hVal : WellFormedSemanticEvalVal (P := P) F) (σ : SemanticStore P) : ev F σ ff = some ff :=
  hVal.identityOnValues _ σ (HasBool.boolIsVal F).2

/-- The result of an evaluation in a well-formed store is a value. -/
theorem ev_value {F : P.Factory} (hVal : WellFormedSemanticEvalVal (P := P) F) {σ : SemanticStore P}
    {e v : P.Expr} (hC : WellFormedStore σ F) (h : ev F σ e = some v) : HasVal.value F v :=
  hVal.outputsAreValues e v σ hC h

/-- The Boolean literals `tt` and `ff` differ. -/
theorem tt_ne_ff' : (tt : P.Expr) ≠ ff := HasBool.tt_is_not_ff

/-- The Boolean literals `ff` and `tt` differ. -/
theorem ff_ne_tt' : (ff : P.Expr) ≠ tt := HasBool.tt_is_not_ff.symm

end

variable [HasFvars P] [HasSubstFvar P] {F : P.Factory}

omit [HasBool P] [HasSubstFvar P] in
/-- The only free variable of a variable reference is the variable. -/
theorem fv_var [LawfulHasFvars P] {x y : P.Ident} {ty : Option P.Ty}
    (h : y ∈ HasFvars.getFvars (var x ty)) : y = x := by
  cases ty <;> simp only [var] at h <;>
    grind [LawfulHasFvars.mkFvar_getFvars, LawfulHasFvars.mkTypedFvar_getFvars]

end -- public section

end WP
end Imperative

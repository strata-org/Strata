/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.CmdProps

/-! # Evaluation of the expressions the WP and SSA phases build

The language of the phases with strict conditionals (`WPIteLang`: a conditional evaluates when
both of its branches do, to values of one type); the evaluation of a conditional
(`ev_ite_true`, `ev_ite_false`, `ev_ite_inv`) and of variable
references in a well-formed store (`ev_var`, `ev_bvar`); and, under the factory laws
`WellFormedSemanticEvalBase`, evaluation depends only on the free variables (`ev_congr`) and
evaluating after substituting variables holding the values of the substituted variables is
evaluating the original (`ev_substVars`).

Key definitions: `WPIteLang`.

Key theorems: `ev_ite_true`, `ev_ite_false`, `ev_ite_inv`, `ev_var`, `ev_bvar`, `ev_congr`,
`ev_substVars`. -/

namespace Imperative
namespace WP

public section

variable {P : PureExpr} [HasBool P] [HasFvar P]

/-- **Strict conditionals of the language of the WP and SSA phases.**  For a `WPLang`, the
    introduction laws of a conditional whose branches both evaluate, to values of one type: it
    evaluates like the branch its condition selects.  An evaluator that gives a conditional a
    value only when both of its branches have one (such as Core's denotational evaluator) has
    these laws. -/
class WPIteLang (P : PureExpr) [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
    [HasSubstFvar P] [WPLang P] : Prop where
  /-- A conditional whose condition evaluates to `true` and whose branches evaluate to values
      of one type evaluates to the value of the `then` branch. -/
  ev_ite_true : ∀ {F σ c t e v w ty}, P.eval F σ c = some (HasBool.ttVal F) →
    P.eval F σ t = some v → P.eval F σ e = some w → HasVal.valueOfTy F v ty →
    HasVal.valueOfTy F w ty → P.eval F σ (WPOps.ite c t e) = some v
  /-- A conditional whose condition evaluates to `false` and whose branches evaluate to values
      of one type evaluates to the value of the `else` branch. -/
  ev_ite_false : ∀ {F σ c t e v w ty}, P.eval F σ c = some (HasBool.ffVal F) →
    P.eval F σ t = some w → P.eval F σ e = some v → HasVal.valueOfTy F v ty →
    HasVal.valueOfTy F w ty → P.eval F σ (WPOps.ite c t e) = some v

section
variable [DecidableEq P.Ident] [HasFvars P] [HasSubstFvar P] [WPLang P] [WPIteLang P]
  {F : P.Factory}
  {σ : SemanticStore P} {c t e : P.Expr} {v w : P.Val} {ty : P.Ty}

/-- An `ite` whose condition evaluates to `true` and whose `else` branch evaluates to a value
    of the type of the `then` branch's evaluates like its `then` branch. -/
theorem ev_ite_true (hc : P.eval F σ c = some (HasBool.ttVal F)) (ht : P.eval F σ t = some v)
    (he : P.eval F σ e = some w) (hv : HasVal.valueOfTy F v ty) (hw : HasVal.valueOfTy F w ty) :
    P.eval F σ (WPOps.ite c t e) = some v := WPIteLang.ev_ite_true hc ht he hv hw

/-- An `ite` whose condition evaluates to `false` and whose `then` branch evaluates to a value
    of the type of the `else` branch's evaluates like its `else` branch. -/
theorem ev_ite_false (hc : P.eval F σ c = some (HasBool.ffVal F)) (ht : P.eval F σ t = some w)
    (he : P.eval F σ e = some v) (hv : HasVal.valueOfTy F v ty) (hw : HasVal.valueOfTy F w ty) :
    P.eval F σ (WPOps.ite c t e) = some v := WPIteLang.ev_ite_false hc ht he hv hw

/-- An `ite` whose condition evaluates to `true`, whose `then` branch evaluates to a Boolean
    value `v` and whose `else` branch evaluates to a Boolean value evaluates to `v`. -/
theorem ev_ite_true_b (hc : P.eval F σ c = some (HasBool.ttVal F)) (ht : P.eval F σ t = some v)
    (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F)
    (he : P.eval F σ e = some (HasBool.ttVal F) ∨ P.eval F σ e = some (HasBool.ffVal F)) :
    P.eval F σ (WPOps.ite c t e) = some v := by
  have hb := HasBool.boolIsValOfTy (P := P) F
  rcases hv with rfl | rfl <;> rcases he with he | he <;>
    first
    | exact WPIteLang.ev_ite_true hc ht he hb.1 hb.1
    | exact WPIteLang.ev_ite_true hc ht he hb.1 hb.2
    | exact WPIteLang.ev_ite_true hc ht he hb.2 hb.1
    | exact WPIteLang.ev_ite_true hc ht he hb.2 hb.2

/-- An `ite` whose condition evaluates to `false`, whose `else` branch evaluates to a Boolean
    value `v` and whose `then` branch evaluates to a Boolean value evaluates to `v`. -/
theorem ev_ite_false_b (hc : P.eval F σ c = some (HasBool.ffVal F)) (he : P.eval F σ e = some v)
    (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F)
    (ht : P.eval F σ t = some (HasBool.ttVal F) ∨ P.eval F σ t = some (HasBool.ffVal F)) :
    P.eval F σ (WPOps.ite c t e) = some v := by
  have hb := HasBool.boolIsValOfTy (P := P) F
  rcases hv with rfl | rfl <;> rcases ht with ht | ht <;>
    first
    | exact WPIteLang.ev_ite_false hc ht he hb.1 hb.1
    | exact WPIteLang.ev_ite_false hc ht he hb.1 hb.2
    | exact WPIteLang.ev_ite_false hc ht he hb.2 hb.1
    | exact WPIteLang.ev_ite_false hc ht he hb.2 hb.2

end

section
variable [DecidableEq P.Ident] [HasFvars P] [HasSubstFvar P] [WPLang P] {F : P.Factory}
  {σ : SemanticStore P} {c t e : P.Expr} {v : P.Val}

/-- An `ite` that evaluates has a condition evaluating to `tt` and a `then` branch with the
    same value, or a condition evaluating to `ff` and an `else` branch with the same value. -/
theorem ev_ite_inv (h : P.eval F σ (WPOps.ite c t e) = some v) :
    (P.eval F σ c = some (HasBool.ttVal F) ∧ P.eval F σ t = some v) ∨
      (P.eval F σ c = some (HasBool.ffVal F) ∧ P.eval F σ e = some v) :=
  WPLang.ev_ite_inv h

end

/-- A variable evaluates to its value in a well-formed store. -/
theorem ev_var [HasOps P] [LawfulHasFvar P] {F : P.Factory}
    (hVar : WellFormedSemanticEvalVar (P := P) F)
    {σ : SemanticStore P} (hC : WellFormedStore σ F) {r : P.Ident} {ty : Option P.Ty} {v : P.Val}
    (hr : σ r = some v) : P.eval F σ (HasFvar.mkVar r ty) = some v := by
  refine (hVar _ r σ hC ?_).trans hr
  cases ty <;> simp [HasFvar.mkVar, LawfulHasFvar.getFvar_mkFvar, LawfulHasFvar.getFvar_mkTypedFvar]

/-- A Boolean variable evaluates to its value in a well-formed store. -/
theorem ev_bvar [HasOps P] [LawfulHasFvar P] {F : P.Factory}
    (hVar : WellFormedSemanticEvalVar (P := P) F)
    {σ : SemanticStore P} (hC : WellFormedStore σ F) {r : P.Ident} {v : P.Val}
    (hr : σ r = some v) : P.eval F σ (HasFvar.mkBoolVar r) = some v := ev_var hVar hC hr

variable [HasFvars P] [HasSubstFvar P] {F : P.Factory}

/-- Two well-formed stores that agree on the free variables of `e` evaluate `e` alike, under
    the factory laws. -/
theorem ev_congr (hF : WellFormedSemanticEvalBase F) {σ σ2 : SemanticStore P}
    (hC : WellFormedStore σ F) (hC2 : WellFormedStore σ2 F) (e : P.Expr)
    (h : ∀ x ∈ HasFvars.getFvars e, σ x = σ2 x) : P.eval F σ e = P.eval F σ2 e :=
  hF.exprCongr e σ σ2 hC hC2 h

/-- Evaluating after substituting variables for variables: when each substituted variable `k`
    is replaced by a variable `y` (bare or annotated) holding `k`'s value in `σ`, and the
    variables not substituted agree, evaluation in `σ'` of the substituted expression is
    evaluation in `σ` of the original (both stores well formed, under the factory laws). -/
theorem ev_substVars [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P] {F : P.Factory}
    (hF : WellFormedSemanticEvalBase F)
    {σ σ' : SemanticStore P} (hσ' : WellFormedStore σ' F) (hσ : WellFormedStore σ F)
    (sm : Map P.Ident P.Expr) (e : P.Expr)
    (hsm : ∀ k v, Map.find? sm k = some v →
      ∃ y, (v = HasFvar.mkFvar y ∨ ∃ ty, v = HasFvar.mkTypedFvar y ty) ∧ σ' y = σ k ∧
        (σ k).isSome)
    (hrest : ∀ x ∈ HasFvars.getFvars e, Map.find? sm x = none → σ' x = σ x) :
    P.eval F σ' (HasSubstFvar.substFvars e sm) = P.eval F σ e := by
  have hfind : ∀ k, @Map.find? P.Ident P.Expr P.EqIdent sm k = Map.find? sm k := fun _ => by congr
  rw [hF.rename e σ' sm hσ' fun k w hk => by
    grind [LawfulHasFvar.getFvar_mkFvar, LawfulHasFvar.getFvar_mkTypedFvar]]
  refine hF.exprCongr e _ σ (fun x v hx => ?_) hσ fun x hx => ?_
  · grind [substStoreExpr, WellFormedStore]
  · grind [substStoreExpr, LawfulHasFvar.getFvar_mkFvar, LawfulHasFvar.getFvar_mkTypedFvar]

end -- public section

end WP
end Imperative

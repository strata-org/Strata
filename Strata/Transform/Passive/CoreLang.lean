/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.Languages.Core.Statement
public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprDenoteEvalProps
public import Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprWF

/-! # Core as a language of the WP and SSA phases

The `WPOps` instance of Core expressions: identifier names, the conditional `.ite`, the view of a
conditional and of a Boolean literal (`LExpr.denoteBool`), the number of nodes (`LExpr.size`),
and the substitution by a lookup function (`LExpr.substFvarsBy`); and the `WPLang` instance,
their laws, from the Lambda facts about evaluation and substitution.

Key definitions: `iteView?`, the `WPOps Expression` and `WPLang Expression` instances.

Key theorems: `iteView?_size` — the parts of a conditional are smaller than it. -/

open Imperative Lambda

namespace Core
namespace WP

public section

/-- The parts of a Core conditional. -/
@[expose] def iteView? : Expression.Expr → Option
    (Expression.Expr × Expression.Expr × Expression.Expr)
  | .ite _ c t f => some (c, t, f)
  | _ => none

/-- The parts of a Core conditional are smaller than it. -/
theorem iteView?_size {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    LExpr.size _ c < LExpr.size _ e ∧ LExpr.size _ t < LExpr.size _ e ∧
      LExpr.size _ f < LExpr.size _ e := by
  cases e <;> cases h; simp only [LExpr.size]; omega

/-- A Core expression with the parts `c`, `t`, `f` of a conditional is that conditional. -/
private theorem iteView?_eq_ite {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    e = .ite () c t f := by
  cases e <;> cases h <;> rfl

/-- A Core expression with the Boolean value `b` is the literal `b`. -/
private theorem denoteBool_eq_lit {e : Expression.Expr} {b : Bool}
    (h : LExpr.denoteBool e = some b) :
    e = if b then HasBool.tt (P := Expression) else HasBool.ff (P := Expression) :=
  match e, h with
  | .const _ (.boolConst b), rfl => by cases b <;> rfl

/-- The operations of the WP and SSA phases on Core expressions. -/
instance : Imperative.WP.WPOps Expression where
  name x := x.name
  ite c t e := .ite () c t e
  iteView? := iteView?
  size := LExpr.size _
  iteView?_size := iteView?_size
  boolLit? := LExpr.denoteBool
  substFn := LExpr.substFvarsBy
  tyBEq a b := decide (a = b)

/-- The laws of the operations of the WP and SSA phases on Core expressions. -/
instance : Imperative.WP.WPLang Expression where
  getFvars_tt := rfl
  getFvars_ff := rfl
  getFvars_ite c t e y := by
    change y ∈ LExpr.LExpr.getVars (LExpr.ite () c t e) ↔ _
    simp [HasFvars.getFvars, LExpr.LExpr.getVars]
  getFvars_substFvars e sm y h := by
    simp only [HasFvars.getFvars, getVars_eq_freeVars_idents] at h ⊢
    exact LExpr.freeVars_substFvars sm e y h
  getFvar_getFvars {e} {y} h := by
    cases e <;> simp_all [HasFvar.getFvar, HasFvars.getFvars, LExpr.LExpr.getVars]
  ev_ite_congr {F σ σ' c t e c' t' e' v} h hc ht he := by
    obtain ⟨b, vt, ve, h1, h2, h3, hs, rfl⟩ := (LExpr.denoteEval_ite_iff (T := CoreLParams)).mp h
    exact (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr
        ⟨b, vt, ve, hc _ h1, ht _ h2, he _ h3, hs, rfl⟩
  ev_ite_inv {F σ c t e v} h := by
    obtain ⟨b, vt, ve, h1, h2, h3, -, rfl⟩ := (LExpr.denoteEval_ite_iff (T := CoreLParams)).mp h
    cases b
    · exact .inr ⟨h1, h3⟩
    · exact .inl ⟨h1, h2⟩
  iteView?_eq h := by exact iteView?_eq_ite h
  boolLit?_eq h := by exact denoteBool_eq_lit h
  substFn_eq e look sm h := by
    simp only [HasSubstFvar.substFvars, LExpr.substFvars_eq_substFvarsBy]
    refine LExpr.substFvarsBy_congr e _ _ fun x hx => h x ?_
    simpa [HasFvars.getFvars, getVars_eq_freeVars_idents] using hx
  substFvars_nil e := by
    change Lambda.LExpr.substFvars e [] = e
    unfold Lambda.LExpr.substFvars
    rfl
  tyBEq_eq h := of_decide_eq_true h
  getTypedFvars_ite c t e p h := by
    change p ∈ Expression.typedFvars (LExpr.ite () c t e) at h
    simpa [HasFvars.getTypedFvars, Expression.typedFvars, LExpr.freeVars, List.filterMap_append,
      or_assoc] using h
  getTypedFvars_substFn e g p h := by
    change p ∈ Expression.typedFvars (LExpr.substFvarsBy e g) at h
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap,
      Option.map_eq_some_iff] at h ⊢
    obtain ⟨⟨x, τ?⟩, hx, τ, rfl, rfl⟩ := h
    rcases LExpr.mem_freeVars_substFvarsBy hx with ⟨hx, hg⟩ | ⟨y, tyy, r, hy, hg, hr⟩
    · exact .inl ⟨⟨_, hx, τ, rfl, rfl⟩, hg⟩
    · refine .inr ⟨y, r, ?_, hg, ⟨_, hr, τ, rfl, rfl⟩⟩
      change y ∈ LExpr.LExpr.getVars e
      rw [getVars_eq_freeVars_idents]
      exact List.mem_map.2 ⟨_, hy, rfl⟩

end -- public section

end WP
end Core

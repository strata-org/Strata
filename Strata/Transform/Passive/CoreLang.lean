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

/-- A conditional recognized by `iteView?` evaluates like the canonical conditional of its parts;
    the root location does not affect `Expression.eval` (`denoteEval`). -/
private theorem iteView?_eval_core {F : Expression.Factory} {σ : Imperative.SemanticStore Expression}
    {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    Expression.eval F σ e = Expression.eval F σ (.ite valueLoc c t f) := by
  cases e <;> simp only [iteView?] at h
  case ite m a b c' =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply Option.ext; intro v
    simp only [Lambda.LExpr.denoteEval_ite_iff]
  all_goals exact absurd h (by simp)

/-- A conditional recognized by `iteView?` has the free variables of the canonical conditional of
    its parts (the root location does not affect free variables). -/
private theorem iteView?_getFvars_core {e c t f : Expression.Expr} (y : Expression.Ident)
    (h : iteView? e = some (c, t, f)) :
    (y ∈ HasFvars.getFvars e ↔ y ∈ HasFvars.getFvars (.ite valueLoc c t f : Expression.Expr)) := by
  cases e <;> simp only [iteView?] at h
  case ite m a b c' =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [HasFvars.getFvars, LExpr.LExpr.getVars]
  all_goals exact absurd h (by simp)

/-- The operators of a conditional recognized by `iteView?` are those of its parts. -/
theorem iteView?_getOps {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    HasOps.getOps e = HasOps.getOps c ++ HasOps.getOps t ++ HasOps.getOps f := by
  cases e <;> cases h <;> rfl

/-- A Core expression that `boolLit?` reads as `b` evaluates like the literal `b`. -/
private theorem boolLit?_eval_core {F : Expression.Factory} {σ : Imperative.SemanticStore Expression}
    {e : Expression.Expr} {b : Bool} (h : LExpr.denoteBool e = some b) :
    Expression.eval F σ e =
      Expression.eval F σ (if b then HasBool.tt (P := Expression) else HasBool.ff (P := Expression)) := by
  unfold LExpr.denoteBool at h
  split at h
  · rename_i m b0
    rw [Option.some.injEq] at h; subst h
    cases b0 <;>
      simp [HasBool.tt, HasBool.ff, Core.true, Core.false, Lambda.LExpr.boolConst,
        Lambda.LExpr.denoteEval_boolConst]
  · exact absurd h (by simp)

/-- The operations of the WP and SSA phases on Core expressions. -/
instance : Imperative.WP.WPOps Expression where
  name x := x.name
  ite c t e := .ite valueLoc c t e
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
    change y ∈ LExpr.LExpr.getVars (LExpr.ite valueLoc c t e) ↔ _
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
  iteView?_eval h := by exact iteView?_eval_core h
  iteView?_getFvars y h := by exact iteView?_getFvars_core y h
  boolLit?_eval h := by exact boolLit?_eval_core h
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
    change p ∈ Expression.typedFvars (LExpr.ite valueLoc c t e) at h
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

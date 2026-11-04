/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps

/-! # `Imperative.HasTyping` for Core

A Core expression has type `ty` under a variable typing `Γ` when `ty` is a
ground monomorphic type `τ`, `Γ` types every free variable, and the expression,
with every free variable annotated by its `Γ` type, has type `τ`.  This is the
judgment Core's denotational evaluator (`Lambda.LExpr.denoteEval`) needs to
succeed, so `LawfulHasTyping` holds.  Nothing yet connects the judgment to type
inference: `Core.Specification.Analysis.TypeCheckWellTypes` states that connection.

- `Core.Expression.HasType` — the typing judgment
- `Core.eval_of_hasType` — type soundness
- `Core.valueOfTy_bool` — Boolean values are `true` and `false`
-/

public section

namespace Core

open Imperative

/-- The Core typing judgment: `e` has the ground monomorphic type of `ty` when
    its free variables are annotated with their `Γ` types. -/
@[expose] def Expression.HasType (Γ : VarTyping Expression) (e : Expression.Expr)
    (ty : Expression.Ty) : Prop :=
  ∃ τ, ty.toMonoType? = some τ ∧ τ.IsGround ∧
    (∀ x ∈ Lambda.LExpr.LExpr.getVars e, (Γ x).isSome) ∧
    (e.annotateFvars (fun x => (Γ x).bind Lambda.LTy.toMonoType?)).HasTypeA [] τ

instance : HasTyping Expression where
  HasType _ := Expression.HasType

/-- **Type soundness.**  A well-typed Core expression evaluates, in a store
    conforming to its typing, to a value of its type. -/
theorem eval_of_hasType (f : Expression.Factory) (Γ : VarTyping Expression)
    (σ : CoreStore) (e : Expression.Expr) (ty : Expression.Ty)
    (he : Expression.HasType Γ e ty) (hσ : StoreHasTyping f σ Γ) :
    ∃ v, Expression.eval f σ e = some v ∧ HasVal.valueOfTy f v ty := by
  obtain ⟨τ, hτ, hg, hdef, hT⟩ := he
  -- Each free variable is bound to a value of the model at its `Γ` type, so the
  -- store's annotation agrees with `Γ`'s on the free variables.
  have hslot : ∀ x ∈ Lambda.LExpr.LExpr.getVars e, ∃ v, σ x = some v ∧ v.tc = f.model.tcInterp ∧
      (Γ x).bind Lambda.LTy.toMonoType? = some v.sort.toMonoTy := by
    intro x hx
    obtain ⟨tyx, hΓ⟩ := Option.isSome_iff_exists.mp (hdef x hx)
    obtain ⟨v, hv, htc, hmono⟩ := hσ x tyx hΓ
    exact ⟨v, hv, htc, by simpa [hΓ] using hmono⟩
  have hann : e.annotateFvars (fun x => (Γ x).bind Lambda.LTy.toMonoType?) =
      e.annotateFvars (Lambda.ValStore.ann (T := CoreLParams) σ) := by
    apply Lambda.LExpr.annotateFvars_congr
    intro x tyx hx
    obtain ⟨v, hv, -, hmono⟩ := hslot x (Lambda.LExpr.mem_getVars_of_mem_freeVars hx)
    simp [hmono, Lambda.ValStore.ann, hv]
  rw [hann] at hT
  have hd : Lambda.ValStore.Defines (T := CoreLParams) σ f.model.tcInterp e := fun x hx => by
    obtain ⟨v, hv, htc, -⟩ := hslot x hx
    exact ⟨v, hv, htc⟩
  refine ⟨_, Lambda.LExpr.denoteEval_of_hasTypeA hd hT hg, rfl, ?_⟩
  show ty.toMonoType? = some (τ.substTyVars f.tyVarVal).toMonoTy
  rw [hg.substTyVars_eq f.tyVarVal Lambda.refTyVarVal, hg, hτ]

/-- The values of Core's Boolean type are `true` and `false`. -/
theorem valueOfTy_bool (f : Expression.Factory) (v : Expression.Val)
    (h : HasVal.valueOfTy f v (HasBool.boolTy (P := Expression))) :
    v = HasBool.ttVal f ∨ v = HasBool.ffVal f := by
  obtain ⟨tc, s, val⟩ := v
  obtain ⟨htc, hs⟩ := h
  dsimp only at htc
  subst htc
  have hs' : s.toMonoTy = (Lambda.LSort.bool).toMonoTy := by
    have := hs.symm.trans boolTy_toMonoType
    exact (Option.some.inj this).trans rfl
  obtain rfl := Lambda.LSort.toMonoTy_injective hs'
  cases (val : Bool) with
  | true => exact .inl rfl
  | false => exact .inr rfl

instance : LawfulHasTyping Expression where
  eval_of_hasType := eval_of_hasType
  valueOfTy_bool := valueOfTy_bool

end Core

end -- public section

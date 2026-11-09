/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LTy

/-! # `Imperative.HasTyping` for Core

A Core expression has type `ty` under a variable typing `Γ` when `ty` is a
ground monomorphic type `τ`, `Γ` types every free variable, and the expression,
with every free variable annotated by its `Γ` type, has type `τ`.  This is the
judgment Core's denotational evaluator (`Lambda.LExpr.denoteEval`) needs to
succeed, so `LawfulHasTyping` holds.  Nothing yet connects the judgment to type
inference: `Core.Specification.Analysis.TypeCheckWellTypes` states that connection.

- `Core.Expression.HasType` — the typing judgment
- `Core.eval_of_hasType` — type soundness
- `Core.storeHasTyping_of_annotates`, `Core.eval_of_annotates` — a store conforming to a
  typing that agrees with an expression's annotations conforms to the typing those
  annotations give, so a well-typed, well-annotated expression evaluates
- `Core.annotateFvars_store_eq_self` — in such a store, evaluation's annotation from the
  stored sorts gives back the program's annotations
- `Core.valueOfTy_unique` — a value has at most one type
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

/-- **The store agrees with the annotations.**  In a store conforming to `Γ`, when `Γ`
    gives every annotated free-variable occurrence of `e` its annotation, the store also
    conforms to the typing that `e`'s own annotations give. -/
theorem storeHasTyping_of_annotates (f : Expression.Factory) (Γ : VarTyping Expression)
    (σ : CoreStore) (e : Expression.Expr) (hσ : StoreHasTyping f σ Γ)
    (hann : Γ.annotates (HasFvars.getTypedFvars (P := Expression) e)) :
    StoreHasTyping f σ (Expression.annotationTyping e) := by
  intro x ty hx
  unfold Expression.annotationTyping at hx
  cases hl : (Lambda.LExpr.freeVars e).lookup x with
  | none => simp [hl] at hx
  | some τ? =>
    cases τ? with
    | none => simp [hl] at hx
    | some τ =>
      simp only [hl, Option.bind_some, Option.map_some, Option.some.injEq] at hx
      subst hx
      obtain ⟨l₁, l₂, hsplit, -⟩ := List.lookup_eq_some_iff.mp hl
      have hmem : (x, some τ) ∈ Lambda.LExpr.freeVars e := by simp [hsplit]
      refine hσ x _ (hann x _ ?_)
      simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap]
      exact ⟨(x, some τ), hmem, rfl⟩

/-- **A well-annotated expression evaluates.**  In a store conforming to `Γ`, an expression
    whose annotated free-variable occurrences carry the types `Γ` gives them, and which has
    type `ty` under its own annotations (`Expression.HasType`, the judgment
    `TypeCheckWellTypes` asks of type-checked programs), evaluates to a value of type `ty`. -/
theorem eval_of_annotates (f : Expression.Factory) (Γ : VarTyping Expression)
    (σ : CoreStore) (e : Expression.Expr) (ty : Expression.Ty) (hσ : StoreHasTyping f σ Γ)
    (hann : Γ.annotates (HasFvars.getTypedFvars (P := Expression) e))
    (he : Expression.HasType (Expression.annotationTyping e) e ty) :
    ∃ v, Expression.eval f σ e = some v ∧ HasVal.valueOfTy f v ty :=
  eval_of_hasType f _ σ e ty he (storeHasTyping_of_annotates f Γ σ e hσ hann)

/-- **Evaluation reads the program's annotations.**  In a store conforming to `Γ`, annotating
    a fully annotated expression whose annotations carry the types `Γ` gives them with the
    sorts of the stored values gives back the expression. -/
theorem annotateFvars_store_eq_self (f : Expression.Factory) (Γ : VarTyping Expression)
    (σ : CoreStore) (e : Expression.Expr) (hσ : StoreHasTyping f σ Γ)
    (hfull : ∀ x τ?, (x, τ?) ∈ Lambda.LExpr.freeVars e → τ?.isSome)
    (hann : Γ.annotates (HasFvars.getTypedFvars (P := Expression) e)) :
    e.annotateFvars (Lambda.ValStore.ann (T := CoreLParams) σ) = e := by
  apply Lambda.LExpr.annotateFvars_eq_self
  intro x τ? hx
  obtain ⟨τ, rfl⟩ := Option.isSome_iff_exists.mp (hfull x τ? hx)
  have hΓ : Γ x = some (Lambda.LTy.forAll [] τ) := hann x _ (by
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap]
    exact ⟨(x, some τ), hx, rfl⟩)
  obtain ⟨v, hv, -, hmono⟩ := hσ x _ hΓ
  simp only [Lambda.LTy.toMonoType?, Option.some.injEq] at hmono
  exact ⟨τ, rfl, by simp [Lambda.ValStore.ann, hv, hmono]⟩

/-- A Core value has at most one type. -/
theorem valueOfTy_unique {f : Expression.Factory} {v : Expression.Val} {T₁ T₂ : Expression.Ty}
    (h₁ : HasVal.valueOfTy f v T₁) (h₂ : HasVal.valueOfTy f v T₂) : T₁ = T₂ := by
  obtain ⟨-, h₁⟩ := h₁
  obtain ⟨-, h₂⟩ := h₂
  rcases T₁ with ⟨_ | _, τ₁⟩ <;> rcases T₂ with ⟨_ | _, τ₂⟩ <;>
    simp_all [Lambda.LTy.toMonoType?]

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

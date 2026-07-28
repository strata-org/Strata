/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTy

/-!
## Properties of Lambda Mono- and Poly-Types

Theorems about the type definitions in `Strata.DL.Lambda.LTy` (`LMonoTy` / `LTy`
and their `mkArrow'`, `destructArrow`, `isArrow`, `size`, and `freeVars`
operations). Definitions, instances, the `@[induction_eliminator]`, and
`@[simp]` normalization lemmas remain in `LTy`.

### Arrow types (`mkArrow'` / `destructArrow` / `isArrow`)
`mkArrow'` is injective in its return type and argument list
(`mkArrow'_injective`), `destructArrow` never returns the empty list
(`destructArrow_non_empty`), and `isArrow` reflects back into the `arrow`
constructor (`isArrow_some`).

### Type size
`LMonoTy.size` is strictly positive (`size_gt_zero`), and an element's size is
bounded by the size of a list containing it (`size_lt_of_mem`) — the facts used
for well-founded recursion over types.

### Free type variables (`LMonoTys.freeVars`)
The free variables of a list of monotypes relate elementwise to the list's free
variables: subset containment (`freeVars_subset`, `freeVars_mem_subset`) and the
existence of a witnessing element (`freeVars_exists`).
-/

namespace Lambda
open Std (ToFormat Format format)

/-! ### Arrow types: `mkArrow'` / `destructArrow` / `isArrow` -/

theorem LMonoTy.mkArrow'_injective {ret₁ ret₂ : LMonoTy} {ins₁ ins₂ : List LMonoTy}
    (h_len : ins₁.length = ins₂.length)
    (h : LMonoTy.mkArrow' ret₁ ins₁ = LMonoTy.mkArrow' ret₂ ins₂)
    : ret₁ = ret₂ ∧ ins₁ = ins₂ := by
  induction ins₁ generalizing ins₂ with
  | nil =>
    cases ins₂ with
    | nil => simp [mkArrow'] at h; exact ⟨h, rfl⟩
    | cons => simp at h_len
  | cons x xs ih =>
    cases ins₂ with
    | nil => simp at h_len
    | cons y ys =>
      simp [mkArrow', LMonoTy.arrow] at h h_len
      have ⟨h_ret, h_tl⟩ := ih h_len h.2
      exact ⟨h_ret, by rw [h.1, h_tl]⟩

public theorem LMonoTy.destructArrow_non_empty (mty : LMonoTy) :
  (mty.destructArrow) ≠ [] := by
  unfold destructArrow; split <;> simp_all

theorem LMonoTy.isArrow_some {t t1 t2 : LMonoTy} :
    t.isArrow = some (t1, t2) → t = .arrow t1 t2 := by
  simp [LMonoTy.arrow, isArrow]
  cases t <;> grind

/-! ### Type size -/

theorem LMonoTy.size_gt_zero :
  0 < LMonoTy.size ty := by
  induction ty <;>  simp_all [LMonoTy.size]
  unfold LMonoTys.size; split
  simp_all; omega

theorem LMonoTy.size_lt_of_mem {ty: LMonoTy} {tys: LMonoTys} (h: ty ∈ tys):
  ty.size <= tys.size := by
  induction tys <;> simp only[LMonoTys.size]<;> grind

/-! ### Free type variables: `LMonoTys.freeVars` -/

/-- If `v ∈ LMonoTys.freeVars tys` and every element's free vars are in `S`,
then `v ∈ S`. -/
theorem LMonoTys.freeVars_subset
    {tys : List LMonoTy} {S : List TyIdentifier}
    (h : ∀ ty, ty ∈ tys → LMonoTy.freeVars ty ⊆ S)
    {v : TyIdentifier}
    (hv : v ∈ LMonoTys.freeVars tys)
    : v ∈ S := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl hmem => exact h ty (.head _) hmem
    | inr hmem => exact ih (fun t ht => h t (.tail _ ht)) hmem

/-- Each element's free vars are a subset of the whole list's free vars. -/
theorem LMonoTys.freeVars_mem_subset
    {ty : LMonoTy} {tys : List LMonoTy}
    (ht : ty ∈ tys)
    : LMonoTy.freeVars ty ⊆ LMonoTys.freeVars tys := by
  induction tys with
  | nil => contradiction
  | cons x rest ih =>
    simp only [LMonoTys.freeVars_of_cons]
    grind

/-- If `v ∈ LMonoTys.freeVars tys`, then some element of `tys` contains `v`. -/
theorem LMonoTys.freeVars_exists
    {v : TyIdentifier} {tys : List LMonoTy}
    (hv : v ∈ LMonoTys.freeVars tys)
    : ∃ ty, ty ∈ tys ∧ v ∈ LMonoTy.freeVars ty := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl h => exact ⟨ty, .head _, h⟩
    | inr h => obtain ⟨t, ht, htv⟩ := ih h; exact ⟨t, .tail _ ht, htv⟩

end Lambda

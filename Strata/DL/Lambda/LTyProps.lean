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

/-- An iterated arrow has a property that arrows build when its result type and every argument
    type have it. -/
theorem LMonoTy.mkArrow'_of_arrow (P : LMonoTy → Prop)
    (h_arrow : ∀ a b, P a → P b → P (LMonoTy.arrow a b)) (out : LMonoTy) (ms : LMonoTys)
    (hout : P out) (hms : ∀ t ∈ ms, P t) : P (LMonoTy.mkArrow' out ms) := by
  induction ms with
  | nil => exact hout
  | cons t rest ih =>
    rw [LMonoTy.mkArrow'_cons]
    exact h_arrow _ _ (hms t List.mem_cons_self)
      (ih (fun s hs => hms s (List.mem_cons_of_mem t hs)))

theorem LMonoTy.destructArrow_non_empty (mty : LMonoTy) :
  (mty.destructArrow) ≠ [] := by
  unfold destructArrow; split <;> simp_all

theorem LMonoTy.isArrow_some {t t1 t2 : LMonoTy} :
    t.isArrow = some (t1, t2) → t = .arrow t1 t2 := by
  simp [LMonoTy.arrow, isArrow]
  cases t <;> grind

/-- `LMonoTy.destructArrow` returns its input alone unless the input is an `arrow` application. -/
theorem destructArrow_eq_self_or_arrow (mty : LMonoTy) :
    LMonoTy.destructArrow mty = [mty] ∨
      ∃ t1 trest, mty = LMonoTy.tcons "arrow" (t1 :: trest) := by
  unfold LMonoTy.destructArrow
  split
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

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

/-- A list of type variables, read as types, has exactly those variables free. -/
theorem freeVars_map_ftvar (l : List TyIdentifier) :
    LMonoTys.freeVars (l.map LMonoTy.ftvar) = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, LMonoTys.freeVars, LMonoTy.freeVars, ih, List.cons_append,
      List.nil_append]

/-- A scheme quantifying nothing has exactly its body's free variables. -/
theorem LTy.freeVars_forAll_nil (t : LMonoTy) :
    LTy.freeVars (.forAll [] t) = LMonoTy.freeVars t := by
  simp [LTy.freeVars, List.removeAll]

/-- A monomorphic scheme quantifies nothing. -/
theorem LTy.eq_forAll_nil_of_isMonoType {t : LTy} (h : t.isMonoType = true) :
    ∃ m, t = .forAll [] m := by
  cases t with
  | forAll vs m =>
    have hvs : vs = [] := List.isEmpty_iff.mp h
    exact ⟨m, by rw [hvs]⟩

/-- Mapping the body of a monomorphic scheme preserves its empty binder list. -/
theorem mapLTyTys_of_isMonoType (f : LMonoTy → LMonoTy) (t : LTy) (h : LTy.isMonoType t) :
    mapLTyTys f t = LTy.forAll [] (f (LTy.toMonoType t h)) := by
  cases t with
  | forAll vs mm =>
    have hvs : vs = [] := List.isEmpty_iff.mp h
    subst hvs
    rfl

/-! ### Free variables of arrow types -/

/-- A function type has exactly the type variables of its argument and result. -/
theorem freeVars_arrow (t1 t2 : LMonoTy) :
    LMonoTy.freeVars (LMonoTy.arrow t1 t2)
      = LMonoTy.freeVars t1 ++ LMonoTy.freeVars t2 := by
  simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil]

/-- Every free variable of an iterated arrow result is free in the whole arrow. -/
theorem mem_freeVars_mkArrow'_output (τ : LMonoTy) (v : TyIdentifier) :
    ∀ ms : LMonoTys, v ∈ LMonoTy.freeVars τ → v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' τ ms) := by
  intro ms
  induction ms with
  | nil => intro hv; simpa using hv
  | cons m rest ih =>
    intro hv
    rw [LMonoTy.mkArrow'_cons]
    simp only [LMonoTy.freeVars, LMonoTys.freeVars_of_cons, List.mem_append]
    exact Or.inr (Or.inl (ih hv))

/-- Every free variable of an iterated arrow input is free in the whole arrow. -/
theorem mem_freeVars_mkArrow'_input (τ : LMonoTy) (v : TyIdentifier) :
    ∀ (ms : LMonoTys) (ty : LMonoTy), ty ∈ ms → v ∈ LMonoTy.freeVars ty →
      v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' τ ms) := by
  intro ms
  induction ms with
  | nil => intro ty hty _; simp at hty
  | cons m rest ih =>
    intro ty hty hv
    rw [LMonoTy.mkArrow'_cons]
    simp only [LMonoTy.freeVars, LMonoTys.freeVars_of_cons, List.mem_append]
    rcases List.mem_cons.mp hty with rfl | hty'
    · exact Or.inl hv
    · exact Or.inr (Or.inl (ih ty hty' hv))

/-- A free variable of an iterated arrow occurs in its result or one of its inputs. -/
theorem freeVars_mkArrow'_cases (τ : LMonoTy) (v : TyIdentifier) :
    ∀ ms : LMonoTys, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' τ ms) →
      v ∈ LMonoTy.freeVars τ ∨ ∃ ty ∈ ms, v ∈ LMonoTy.freeVars ty := by
  intro ms
  induction ms with
  | nil => intro hv; exact Or.inl (by simpa using hv)
  | cons m rest ih =>
    intro hv
    rw [LMonoTy.mkArrow'_cons] at hv
    simp only [LMonoTy.freeVars, LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with hm | hrest
    · exact Or.inr ⟨m, List.mem_cons_self .., hm⟩
    · rcases hrest with harr | hnil
      · rcases ih harr with hout | ⟨ty, hty, hvty⟩
        · exact Or.inl hout
        · exact Or.inr ⟨ty, List.mem_cons_of_mem m hty, hvty⟩
      · exact absurd hnil (by simp [LMonoTys.freeVars])

/-- An iterated function type keeps its type variables within any set containing those of
    its result and of each argument. -/
theorem freeVars_mkArrow'_subset (τ : LMonoTy) (ms : LMonoTys) (S : List TyIdentifier)
    (hout : ∀ v ∈ LMonoTy.freeVars τ, v ∈ S)
    (hms : ∀ t ∈ ms, ∀ v ∈ LMonoTy.freeVars t, v ∈ S) :
    ∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' τ ms), v ∈ S := by
  intro v hv
  rcases freeVars_mkArrow'_cases τ v ms hv with h | ⟨t, ht, hvt⟩
  · exact hout v h
  · exact hms t ht v hvt

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StoreRelations
import all Strata.DL.Imperative.StoreRelations
public import Strata.DL.Imperative.StoreProps

---------------------------------------------------------------------

namespace Imperative

/-! # Metatheory of the store relations

Properties of `StoreAgreement`, `StoreProjected`, and `StoreExtendsWith`.
The underlying definedness, substitution, and generated-name reservation laws
live in `StoreProps`. This module remains independent of command and statement
semantics:

- `StoreAgreement.refl` / `StoreAgreement.trans` / `storeAgreement_iff` /
  `storeAgreement_supplies_mono_premise`, the `storeAgreement_storeWith` update law
  (a `SemanticStore.update` at a source-undefined slot preserves `StoreAgreement`),
  the `StoreProjected` reflexivity / transitivity / lookup-supply laws, and the
  `StoreExtendsWith` equality-at-false / reflexivity / forgetful /
  monotonicity / composition / lookup / update laws (`eq_of_false`, `refl`,
  `toStoreAgreement`, `mono`, `trans_union`, `trans`,
  `lookup_eq_of_not_extra`, `update_target`, `update_both`).

The statement-level `StoreExtendsWith.projectStore` and
`StoreAgreement.of_projectStore` / `of_projectStore_parents` scope-projection laws
live in `StmtSemanticsProps`.
-/

public section

/-! ## Store comparison properties -/

/-- Store agreement is reflexive: every store agrees with itself. -/
theorem StoreAgreement.refl {P : PureExpr} (σ : SemanticStore P) :
    StoreAgreement σ σ :=
  fun _ _ => rfl

/-- `StoreAgreement` supplies the pointwise-extension premise of
`WellFormedSemanticEvalMono`: whatever the source store defines, the target
store defines identically. -/
theorem storeAgreement_supplies_mono_premise {P : PureExpr}
    (σ_struct σ_cfg : SemanticStore P) (h_agree : StoreAgreement σ_struct σ_cfg) :
    ∀ x w, σ_struct x = some w → σ_cfg x = some w := by
  intro x w hw
  have h_def : isDefined σ_struct [x] := fun v hv => by
    rw [List.mem_singleton.mp hv, hw]; rfl
  rw [← h_agree x h_def]; exact hw

/-- Asymmetric store agreement composes transitively through a middle store. -/
theorem StoreAgreement.trans {P : PureExpr} {σ₁ σ₂ σ₃ : SemanticStore P}
    (h₁ : StoreAgreement σ₁ σ₂) (h₂ : StoreAgreement σ₂ σ₃) :
    StoreAgreement σ₁ σ₃ := by
  intro x h_def₁
  have h12 : σ₁ x = σ₂ x := h₁ x h_def₁
  have h_def₂ : isDefined σ₂ [x] := fun v hv => by
    rw [List.mem_singleton.mp hv, ← h12]; exact h_def₁ x (List.mem_singleton.mpr rfl)
  exact h12.trans (h₂ x h_def₂)

/-- A `SemanticStore.update` at a slot the source store leaves undefined preserves
`StoreAgreement` with the source: the only changed slot is `ident`, which the
source store does not define (one-directionality of `StoreAgreement`). -/
theorem storeAgreement_storeWith {P : PureExpr} [DecidableEq P.Ident]
    (σ_src σ_tgt : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (h_agree : StoreAgreement σ_src σ_tgt)
    (h_src_none : σ_src ident = none) :
    StoreAgreement σ_src (SemanticStore.update σ_tgt ident b) := by
  intro x h_def
  have h_x_def : (σ_src x).isSome = true := h_def x (List.mem_singleton.mpr rfl)
  have h_ne : x ≠ ident := by
    rintro rfl; rw [h_src_none] at h_x_def; exact absurd h_x_def (by simp)
  rw [h_agree x h_def]
  simp [SemanticStore.update, h_ne]

/-- `σ` agrees with `σ'` wherever `σ` is defined exactly when, at every
variable, `σ` has the value of `σ'` or is undefined. -/
theorem storeAgreement_iff {P : PureExpr} {σ σ' : SemanticStore P} :
    StoreAgreement σ σ' ↔ ∀ x, σ x = σ' x ∨ σ x = none := by
  refine ⟨fun h x => ?_, fun h x hx => (h x).resolve_right fun h0 => ?_⟩
  · cases hσ : σ x with
    | none => exact .inr rfl
    | some v =>
      exact .inl (hσ ▸ h x fun y hy => by
        simp [List.mem_singleton.mp hy, hσ])
  · simpa [h0] using hx x (List.mem_singleton_self x)

namespace StoreProjected

/-- Every store is a projection of itself. -/
theorem refl {P : PureExpr} (store : SemanticStore P) :
    StoreProjected store store :=
  StoreAgreement.refl store

/-- Store projection composes through an intermediate store. -/
theorem trans {P : PureExpr} {source middle projected : SemanticStore P}
    (h₁ : StoreProjected source middle)
    (h₂ : StoreProjected middle projected) :
    StoreProjected source projected :=
  StoreAgreement.trans h₂ h₁

/-- A retained binding in a projected store has the same binding in its source. -/
theorem supplies_mono_premise {P : PureExpr}
    {source projected : SemanticStore P}
    (h : StoreProjected source projected) :
    ∀ ident value, projected ident = some value → source ident = some value :=
  storeAgreement_supplies_mono_premise projected source h

end StoreProjected

/-- A store extension with no permitted target-only bindings is equality. -/
theorem StoreExtendsWith.eq_of_false {P : PureExpr}
    {source target : SemanticStore P}
    (h : StoreExtendsWith (fun _ => False) source target) :
    source = target := by
  funext ident
  cases hsource : source ident with
  | some value =>
      rw [← hsource]
      exact h.1 ident (by simp [isDefined, hsource])
  | none =>
      cases htarget : target ident with
      | none => rfl
      | some _ => simpa [hsource] using h.2 ident (by simp [htarget])

namespace StoreExtendsWith

/-- A classified extension agrees at any register that is not eligible
for a target-only binding. -/
theorem lookup_eq_of_not_extra {P : PureExpr} {Extra : P.Ident → Prop}
    {source target : SemanticStore P} (h : StoreExtendsWith Extra source target)
    {ident : P.Ident} (hnot : ¬ Extra ident) :
    source ident = target ident := by
  cases hsource : source ident with
  | some value =>
      rw [← hsource]
      exact h.1 ident (by simp [isDefined, hsource])
  | none =>
      cases htarget : target ident with
      | none => rfl
      | some _ =>
          rcases h.2 ident (by simp [htarget]) with hsome | hextra
          · simp [hsource] at hsome
          · exact absurd hextra hnot

/-- Every store extends itself without requiring an extra-register class. -/
theorem refl {P : PureExpr} (Extra : P.Ident → Prop) (store : SemanticStore P) :
    StoreExtendsWith Extra store store :=
  ⟨StoreAgreement.refl _, fun _ h => Or.inl h⟩

/-- Forgetting target-only classification recovers ordinary store agreement. -/
theorem toStoreAgreement {P : PureExpr} {Extra : P.Ident → Prop}
    {source target : SemanticStore P} (h : StoreExtendsWith Extra source target) :
    StoreAgreement source target :=
  h.1

/-- Widening the accepted class of target-only registers preserves extension. -/
theorem mono {P : PureExpr} {Extra Extra' : P.Ident → Prop}
    (hsub : ∀ ident, Extra ident → Extra' ident)
    {source target : SemanticStore P}
    (h : StoreExtendsWith Extra source target) :
    StoreExtendsWith Extra' source target :=
  ⟨h.1, fun ident hsome => (h.2 ident hsome).imp_right (hsub ident)⟩

/-- Consecutive extensions compose, classifying extras introduced by either
stage with the union of their classes. -/
theorem trans_union {P : PureExpr}
    {Extra₁ Extra₂ : P.Ident → Prop}
    {source middle target : SemanticStore P}
    (h₁ : StoreExtendsWith Extra₁ source middle)
    (h₂ : StoreExtendsWith Extra₂ middle target) :
    StoreExtendsWith (fun ident => Extra₁ ident ∨ Extra₂ ident) source target := by
  refine ⟨StoreAgreement.trans h₁.1 h₂.1, ?_⟩
  intro ident htarget
  rcases h₂.2 ident htarget with hmiddle | hextra₂
  · rcases h₁.2 ident hmiddle with hsource | hextra₁
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hextra₁)
  · exact Or.inr (Or.inr hextra₂)

/-- Consecutive extensions using the same class compose. -/
theorem trans {P : PureExpr} {Extra : P.Ident → Prop}
    {source middle target : SemanticStore P}
    (h₁ : StoreExtendsWith Extra source middle)
    (h₂ : StoreExtendsWith Extra middle target) :
    StoreExtendsWith Extra source target :=
  (trans_union h₁ h₂).mono (fun _ h => h.elim id id)

/-- Adding one classified binding at a source-undefined register preserves
store extension. -/
theorem update_target {P : PureExpr} [DecidableEq P.Ident]
    {Extra : P.Ident → Prop} {source target : SemanticStore P}
    {ident : P.Ident} {value : P.Expr}
    (h : StoreExtendsWith Extra source target)
    (hsource : source ident = none) (hextra : Extra ident) :
    StoreExtendsWith Extra source (SemanticStore.update target ident value) := by
  refine ⟨storeAgreement_storeWith source target ident value h.1 hsource, ?_⟩
  intro x hsome
  by_cases hx : x = ident
  · subst x
    exact Or.inr hextra
  · have htarget : (target x).isSome = true := by
      simpa [SemanticStore.update, hx] using hsome
    exact h.2 x htarget

/-- Updating the same register to the same value in both stores preserves a
classified extension. -/
theorem update_both {P : PureExpr} [DecidableEq P.Ident]
    {Extra : P.Ident → Prop} {source target : SemanticStore P}
    {ident : P.Ident} {value : P.Expr}
    (h : StoreExtendsWith Extra source target) :
    StoreExtendsWith Extra
      (SemanticStore.update source ident value)
      (SemanticStore.update target ident value) := by
  refine ⟨?_, ?_⟩
  · intro x hdefined
    by_cases hx : x = ident
    · subst x
      simp [SemanticStore.update]
    · simp only [SemanticStore.update, hx]
      exact h.1 x (fun y hy => by
        simpa [List.mem_singleton.mp hy, SemanticStore.update, hx] using
          hdefined x (List.mem_singleton.mpr rfl))
  · intro x hsome
    by_cases hx : x = ident
    · subst x
      exact Or.inl (by simp [SemanticStore.update])
    · simp only [SemanticStore.update, hx] at hsome ⊢
      exact h.2 x hsome

end StoreExtendsWith

end -- public section

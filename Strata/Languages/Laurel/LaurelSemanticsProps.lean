/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelSemantics

/-!
# Properties of Laurel Operational Semantics

Determinism, store monotonicity, and progress properties for the
direct Laurel operational semantics.
-/

namespace Strata.Laurel

/-! ## Store Monotonicity -/

theorem UpdateStore_def_monotone {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue}
    {vs : List Identifier} :
    (∀ y, y ∈ vs → (σ y).isSome) →
    UpdateStore σ x v σ' →
    (∀ y, y ∈ vs → (σ' y).isSome) := by
  intro Hdef Hup y Hy
  cases Hup with
  | update Hold Hnew Hrest =>
    by_cases heq : x = y
    · subst heq; simp [Hnew]
    · rw [Hrest y heq]; exact Hdef y Hy

theorem InitStore_def_monotone {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue}
    {vs : List Identifier} :
    (∀ y, y ∈ vs → (σ y).isSome) →
    InitStore σ x v σ' →
    (∀ y, y ∈ vs → (σ' y).isSome) := by
  intro Hdef Hinit y Hy
  cases Hinit with
  | init Hnone Hnew Hrest =>
    by_cases heq : x = y
    · subst heq; simp [Hnew]
    · rw [Hrest y heq]; exact Hdef y Hy

/-! ## Determinism of Store Operations -/

theorem UpdateStore_deterministic {σ σ₁ σ₂ : LaurelStore} {x : Identifier} {v : LaurelValue} :
    UpdateStore σ x v σ₁ →
    UpdateStore σ x v σ₂ →
    σ₁ = σ₂ := by
  intro H1 H2
  cases H1 with | update _ Hnew1 Hrest1 =>
  cases H2 with | update _ Hnew2 Hrest2 =>
  funext y
  by_cases heq : x = y
  · subst heq; simp_all
  · rw [Hrest1 y heq, Hrest2 y heq]

theorem InitStore_deterministic {σ σ₁ σ₂ : LaurelStore} {x : Identifier} {v : LaurelValue} :
    InitStore σ x v σ₁ →
    InitStore σ x v σ₂ →
    σ₁ = σ₂ := by
  intro H1 H2
  cases H1 with | init _ Hnew1 Hrest1 =>
  cases H2 with | init _ Hnew2 Hrest2 =>
  funext y
  by_cases heq : x = y
  · subst heq; simp_all
  · rw [Hrest1 y heq, Hrest2 y heq]

/-! ## catchExit Properties -/

theorem catchExit_normal (label : Option Identifier) (v : LaurelValue) :
    catchExit label (.normal v) = .normal v := by
  cases label <;> simp [catchExit]

theorem catchExit_return (label : Option Identifier) (rv : Option LaurelValue) :
    catchExit label (.ret rv) = .ret rv := by
  cases label <;> simp [catchExit]

theorem catchExit_none_passthrough (o : Outcome) :
    catchExit none o = o := by
  simp [catchExit]

/-! ## evalPrimOp Determinism -/

theorem evalPrimOp_deterministic (op : Operation) (args : List LaurelValue) :
    ∀ v₁ v₂, evalPrimOp op args = some v₁ → evalPrimOp op args = some v₂ → v₁ = v₂ := by
  intros v₁ v₂ H1 H2; rw [H1] at H2; exact Option.some.inj H2

/-! ## Determinism of Evaluation -/

/-
Theorem: Laurel evaluation is deterministic.

For the full relation, if a statement evaluates to two results under the
same evaluator, procedure environment, heap, and store, those results are equal.

Proof sketch: By mutual induction on the evaluation derivation.
Each constructor uniquely determines the outcome given the same inputs.

Note: Full proof requires mutual induction over EvalLaurelStmt and
EvalLaurelBlock simultaneously. The proof is admitted here; the store
operation determinism lemmas above are the key building blocks.
-/

mutual
theorem EvalLaurelStmt_deterministic :
    EvalLaurelStmt δ π h σ s h₁ σ₁ o₁ →
    EvalLaurelStmt δ π h σ s h₂ σ₂ o₂ →
    h₁ = h₂ ∧ σ₁ = σ₂ ∧ o₁ = o₂ := by
  sorry

theorem EvalLaurelBlock_deterministic :
    EvalLaurelBlock δ π h σ ss h₁ σ₁ o₁ →
    EvalLaurelBlock δ π h σ ss h₂ σ₂ o₂ →
    h₁ = h₂ ∧ σ₁ = σ₂ ∧ o₁ = o₂ := by
  sorry
end

/-! ## Block Value Semantics -/

theorem empty_block_void :
    EvalLaurelBlock δ π h σ [] h σ (.normal .vVoid) :=
  EvalLaurelBlock.nil

theorem singleton_block_value :
    EvalLaurelStmt δ π h σ s h' σ' (.normal v) →
    EvalLaurelBlock δ π h σ [s] h' σ' (.normal v) :=
  EvalLaurelBlock.last_normal

end Strata.Laurel

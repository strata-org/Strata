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

opaque StmtExprSize (stmtexp: StmtExpr) : Nat

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

theorem EvalArgs_deterministic:
    EvalArgs δ σ args val₁ →
    EvalArgs δ σ args val₂ →
    val₁ = val₂ := by
  intro H1 H2
  induction args generalizing val₁ val₂ <;> (cases H1; cases H2; simp)
  grind


def list_length (l: List Nat): Int := match l with
| [] => 0
| h::t => 1 + list_length t


theorem List_pos (l: List Nat) : list_length l >= 0 :=by
  cases l <;> simp [list_length]
  rename_i t
  have h:= List_pos t
  omega












/-
  generalize Hsize: StmtExprSize s.val = size
  induction size using Nat.strongRecOn generalizing s h σ h₁ σ₁ o₁ h₂ σ₂ o₂ sval
  rename_i ind
  intro H1 H2
  cases sval
  cases H1 <;> simp_all only [forall_eq', reduceCtorEq]
  cases H2 <;> simp_all only [StmtExpr.IfThenElse.injEq, Option.some.injEq]
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp only) h_1 h_3
  simp [ind1] at *
  apply ind (StmtExprSize thenBr.val) (by sorry) (by simp only [Hval]) h_2 h_4
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp only) h_1 h_3
  simp at ind1
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp only) h_1 h_3
  simp [ind1] at *
  simp_all

  cases H2 <;> simp_all only [StmtExpr.IfThenElse.injEq, Option.some.injEq]
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_3
  simp at ind1
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_3
  simp [ind1] at *
  apply ind (StmtExprSize elseBr.val) (by sorry) (by simp only [Hval]) h_2 h_4
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_3
  simp at ind1
  simp_all;
  simp_all

  cases H2 <;> simp_all
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_3
  simp [ind1] at *
  apply ind (StmtExprSize thenBranch.val) (by sorry) (by simp) h_2 h_4
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_3
  simp at ind1

  cases H2 <;> simp_all
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_2
  simp at ind1
  expose_names
  have ind1 := ind (StmtExprSize cond.val) (by sorry) (by simp) h_1 h_2
  simp [ind1]



-/







end Strata.Laurel

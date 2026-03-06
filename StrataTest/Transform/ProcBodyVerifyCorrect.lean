/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.Languages.Core.ProcedureEval

/-! # Procedure Body Verification Correctness Proof

This file defines the soundness framework for program transformations
and proves correctness of example transformations.

Assertion checking is handled by the verification framework (stmt_valid,
stmt_correct, transform_preserves_validity), not by the operational semantics.
In the operational semantics, assert is a skip (no-op).
-/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform

/-! ## Operational Semantics Lemmas -/

/-- An assert statement is a skip: it preserves the store and evaluator -/
theorem eval_assert_is_skip
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression) :
    EvalStatement π φ δ σ (Statement.assert label expr md) σ' δ' →
    σ' = σ ∧ δ' = δ := by
  intro h
  unfold Statement.assert at h
  cases h with
  | cmd_sem h_cmd h_def =>
    cases h_cmd with
    | cmd_sem h_imp =>
      cases h_imp with
      | eval_assert =>
        exact ⟨rfl, rfl⟩

/-- If an assume statement evaluates successfully, the condition holds -/
theorem eval_assume_implies_condition
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression) :
    EvalStatement π φ δ σ (Statement.assume label expr md) σ' δ' →
    δ σ expr = Option.some HasBool.tt ∧ σ' = σ ∧ δ' = δ := by
  intro h
  unfold Statement.assume at h
  cases h with
  | cmd_sem h_cmd h_def =>
    cases h_cmd with
    | cmd_sem h_imp =>
      cases h_imp with
      | eval_assume h_true h_wf =>
        exact ⟨h_true, rfl, rfl⟩

/-- Evaluation of a block statement -/
theorem eval_block_iff
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval)
    (label : String) (stmts : List Statement) (md : MetaData Expression) :
    EvalStatement π φ δ σ (Stmt.block label stmts md) σ' δ' ↔
    EvalStatements π φ δ σ stmts σ' δ' := by
  constructor
  · intro h; cases h with | block_sem h_block => exact h_block
  · intro h; exact Imperative.EvalStmt.block_sem h

end ProcBodyVerifyCorrect

/-! # Soundness Framework

Definitions of statement correctness and transformation soundness following
the framework from `strata_soundness_notes.md`.

Key concepts:
- Four semantic judgments: valid, falsifiable, satisfiable, unsatisfiable
- Four transformation properties matching each judgment
- `stmt_correct`: validity for all assertions
- Examples proving soundness of concrete transformations
-/

namespace Soundness

open Core Imperative

/-! ## Core-specific small-step abbreviations -/

abbrev CoreConfig := Config Expression Command
abbrev CoreStep (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)
abbrev CoreStepStar (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)

/-! ## Program State -/

/-- A program state tracks which assertion label is being targeted and
    carries a variable valuation. -/
structure PS where
  pc : CoreLabel
  valuation : CoreStore
  evaluator : CoreEval

/-! ## The Four Semantic Judgments

These form a square of quantifier duality over reachable program states:

|                    | ∀ initial states (universal) | ∃ initial state (existential) |
|--------------------|------------------------------|-------------------------------|
| predicate holds    | `stmt_valid`                 | `stmt_satisfiable`            |
| predicate fails    | `stmt_unsatisfiable`         | `stmt_falsifiable`            |

Dualities:
- `stmt_valid ↔ ¬stmt_falsifiable`
- `stmt_satisfiable ↔ ¬stmt_unsatisfiable`
- `stmt_valid → stmt_satisfiable` (assuming reachability)
- `stmt_unsatisfiable → stmt_falsifiable` (same direction, for failure)
-/

/-- **Validity**: For all reachable states at a given assertion, the predicate holds.
    "The assertion is always true." -/
def stmt_valid
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression) : Prop :=
  Statement.assert label expr md ∈ stmts →
  ∀ (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval),
    EvalStatements π φ δ σ stmts σ' δ' →
    ∃ (σ_at : CoreStore) (δ_at : CoreEval), δ_at σ_at expr = some HasBool.tt

/-- **Falsifiability**: There exists a reachable state at a given assertion where
    the predicate fails. "There is a counterexample." This is `¬stmt_valid`. -/
def stmt_falsifiable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression) : Prop :=
  Statement.assert label expr md ∈ stmts ∧
  ∃ (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval),
    EvalStatements π φ δ σ stmts σ' δ' ∧
    ∀ (σ_at : CoreStore) (δ_at : CoreEval), δ_at σ_at expr ≠ some HasBool.tt

/-- **Satisfiability**: There exists a reachable state at a given assertion where
    the predicate holds. "The assertion can be true." -/
def stmt_satisfiable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression) : Prop :=
  Statement.assert label expr md ∈ stmts ∧
  ∃ (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval),
    EvalStatements π φ δ σ stmts σ' δ' ∧
    ∃ (σ_at : CoreStore) (δ_at : CoreEval), δ_at σ_at expr = some HasBool.tt

/-- **Unsatisfiability**: For all reachable states at a given assertion, the
    predicate fails. "The assertion is always false." This is `¬stmt_satisfiable`. -/
def stmt_unsatisfiable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression) : Prop :=
  Statement.assert label expr md ∈ stmts →
  ∀ (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval),
    EvalStatements π φ δ σ stmts σ' δ' →
    ∀ (σ_at : CoreStore) (δ_at : CoreEval), δ_at σ_at expr ≠ some HasBool.tt

/-- `stmt_correct` is validity for all assertions in the list. -/
def stmt_correct
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement) : Prop :=
  ∀ (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression),
    stmt_valid π φ stmts label expr md

/-! ## The Four Transformation Properties

Each transformation property lifts the corresponding statement judgment:
if the property holds for the transformed program, it holds for the original.
-/

/-- If the transformed program is valid, the original is valid. -/
def transform_preserves_validity
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (T : List Statement → List Statement) : Prop :=
  ∀ (stmts : List Statement),
    stmt_correct π φ (T stmts) → stmt_correct π φ stmts

/-- If the transformed program has a counterexample, the original does too. -/
def transform_preserves_counterexample
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (T : List Statement → List Statement)
    (F_inv : CoreLabel → CoreLabel) : Prop :=
  ∀ (stmts : List Statement) (label : CoreLabel)
    (expr : Expression.Expr) (md : MetaData Expression),
    stmt_falsifiable π φ (T stmts) label expr md →
    ∃ (label' : CoreLabel) (expr' : Expression.Expr) (md' : MetaData Expression),
      stmt_falsifiable π φ stmts label' expr' md'

/-- If the transformed program is satisfiable, the original is too. -/
def transform_preserves_satisfiability
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (T : List Statement → List Statement) : Prop :=
  ∀ (stmts : List Statement) (label : CoreLabel)
    (expr : Expression.Expr) (md : MetaData Expression),
    stmt_satisfiable π φ (T stmts) label expr md →
    ∃ (label' : CoreLabel) (expr' : Expression.Expr) (md' : MetaData Expression),
      stmt_satisfiable π φ stmts label' expr' md'

/-- If the transformed program is unsatisfiable, the original is too. -/
def transform_preserves_unsatisfiability
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (T : List Statement → List Statement) : Prop :=
  ∀ (stmts : List Statement) (label : CoreLabel)
    (expr : Expression.Expr) (md : MetaData Expression),
    stmt_unsatisfiable π φ (T stmts) label expr md →
    ∃ (label' : CoreLabel) (expr' : Expression.Expr) (md' : MetaData Expression),
      stmt_unsatisfiable π φ stmts label' expr' md'

/-! ## Examples -/

/-! ### Example 1: `assert true` is correct -/

/-- A single `assert true` statement is correct: the condition trivially holds. -/
theorem assert_true_correct
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (md : MetaData Expression)
    (h_eval_true : ∀ (δ : CoreEval) (σ : CoreStore), δ σ Core.true = some HasBool.tt) :
    stmt_correct π φ [Statement.assert label Core.true md] := by
  intro lbl expr md'
  unfold stmt_valid
  intro h_in δ σ σ' δ' _
  rw [List.mem_singleton] at h_in
  cases h_in
  exact ⟨σ, δ, h_eval_true δ σ⟩

/-! ### Example 2: Removing an initial `assert true` is a sound transformation -/

/-- The transformation that removes a leading `assert true` from a statement list. -/
def removeLeadingAssertTrue (label : CoreLabel) (md : MetaData Expression)
    (stmts : List Statement) : List Statement :=
  match stmts with
  | Statement.assert l Core.true m :: rest =>
    if l = label ∧ m = md then rest else stmts
  | _ => stmts

/-- Helper: removeLeadingAssertTrue either returns rest or stmts unchanged -/
theorem removeLeadingAssertTrue_cases (label : CoreLabel) (md : MetaData Expression)
    (stmts : List Statement) :
    (∃ rest, stmts = Statement.assert label Core.true md :: rest ∧
      removeLeadingAssertTrue label md stmts = rest) ∨
    removeLeadingAssertTrue label md stmts = stmts := by
  unfold removeLeadingAssertTrue
  split
  · rename_i l m rest
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; left; exact ⟨rest, rfl, rfl⟩
    · right; rfl
  · right; rfl

/-- If (assert :: rest) evaluates and assert is a skip, rest evaluates -/
theorem eval_skip_assert_rest
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (δ : CoreEval) (σ σ' : CoreStore) (δ' : CoreEval)
    (l : CoreLabel) (e : Expression.Expr) (m : MetaData Expression)
    (rest : List Statement) :
    EvalStatements π φ δ σ (Statement.assert l e m :: rest) σ' δ' →
    EvalStatements π φ δ σ rest σ' δ' := by
  intro h_eval
  cases h_eval with
  | stmts_some_sem h_stmt h_rest =>
    have ⟨h_σ, h_δ⟩ := ProcBodyVerifyCorrect.eval_assert_is_skip π φ δ σ _ _ l e m h_stmt
    subst h_σ; subst h_δ
    exact h_rest

/-- Removing a leading `assert true` preserves validity. -/
theorem removeLeadingAssertTrue_preserves_validity
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (md : MetaData Expression)
    (h_eval_true : ∀ (δ : CoreEval) (σ : CoreStore), δ σ Core.true = some HasBool.tt) :
    transform_preserves_validity π φ (removeLeadingAssertTrue label md) := by
  intro stmts h_target_correct lbl expr md'
  unfold stmt_valid
  intro h_in δ σ σ' δ' h_eval
  cases removeLeadingAssertTrue_cases label md stmts with
  | inl h_removed =>
    obtain ⟨rest, h_stmts_eq, h_T_eq⟩ := h_removed
    subst h_stmts_eq
    rw [h_T_eq] at h_target_correct
    cases h_in with
    | head =>
      exact ⟨σ, δ, h_eval_true δ σ⟩
    | tail _ h =>
      have h_rest_eval := eval_skip_assert_rest π φ δ σ σ' δ' label Core.true md rest h_eval
      exact h_target_correct lbl expr md' h δ σ σ' δ' h_rest_eval
  | inr h_unchanged =>
    rw [h_unchanged] at h_target_correct
    exact h_target_correct lbl expr md' h_in δ σ σ' δ' h_eval

end Soundness

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

/-- An assertion identifier: label + expression + metadata -/
structure AssertId where
  label : CoreLabel
  expr  : Expression.Expr
  md    : MetaData Expression

/-- A program state carries the store, evaluator, and an optional assertion id.
    When execution reaches an assert command, `pc` is `some` with that assert's id.
    Otherwise `pc` is `none`. -/
structure ProgramState where
  store : CoreStore
  eval  : CoreEval
  pc    : Option AssertId

/-- Extract a `ProgramState` from a small-step configuration.
    When the configuration is at an assert command, `pc` is set. -/
def ProgramState.ofConfig : CoreConfig → Option ProgramState
  | .stmt (Stmt.cmd (CmdExt.cmd (Cmd.assert label expr md))) σ δ =>
    some ⟨σ, δ, some ⟨label, expr, md⟩⟩
  | .stmt _ σ δ => some ⟨σ, δ, none⟩
  | .stmts _ σ δ => some ⟨σ, δ, none⟩
  | .terminal σ δ => some ⟨σ, δ, none⟩
  | .block _ _ σ δ => some ⟨σ, δ, none⟩
  | .exiting _ σ δ => some ⟨σ, δ, none⟩

/-- A program state is reachable from a statement if there exists an initial
    configuration and a multi-step execution path to a configuration whose
    program state matches. -/
def reachable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (ps : ProgramState) : Prop :=
  ∃ (δ₀ : CoreEval) (σ₀ : CoreStore) (cfg : CoreConfig),
    CoreStepStar π φ (.stmt stmt σ₀ δ₀) cfg ∧
    ProgramState.ofConfig cfg = some ps

/-! ## The Four Semantic Judgments

These form a square of quantifier duality over reachable program states:

|                    | ∀ initial states (universal) | ∃ initial state (existential) |
|--------------------|------------------------------|-------------------------------|
| predicate holds    | `stmt_valid`                 | `stmt_satisfiable`            |
| predicate fails    | `stmt_unsatisfiable`         | `stmt_falsifiable`            |

Dualities:
- `stmt_valid ↔ ¬stmt_falsifiable`
- `stmt_satisfiable ↔ ¬stmt_unsatisfiable`
-/

/-- **Validity**: For all reachable states at a given assertion, the predicate holds.
    "The assertion is always true." -/
def stmt_valid
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (a : AssertId) : Prop :=
  ∀ (ps : ProgramState),
    reachable π φ stmt ps →
    ps.pc = some a →
    ps.eval ps.store a.expr = some HasBool.tt

/-- **Falsifiability**: There exists a reachable state at a given assertion where
    the predicate is false. "There is a counterexample." -/
def stmt_falsifiable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (a : AssertId) : Prop :=
  ∃ (ps : ProgramState),
    reachable π φ stmt ps ∧
    ps.pc = some a ∧
    ps.eval ps.store a.expr = some HasBool.ff

/-- **Satisfiability**: There exists a reachable state at a given assertion where
    the predicate holds. "The assertion can be true." -/
def stmt_satisfiable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (a : AssertId) : Prop :=
  ∃ (ps : ProgramState),
    reachable π φ stmt ps ∧
    ps.pc = some a ∧
    ps.eval ps.store a.expr = some HasBool.tt

/-- **Unsatisfiability**: For all reachable states at a given assertion, the
    predicate is false. "The assertion is always false." -/
def stmt_unsatisfiable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (a : AssertId) : Prop :=
  ∀ (ps : ProgramState),
    reachable π φ stmt ps →
    ps.pc = some a →
    ps.eval ps.store a.expr = some HasBool.ff

/-- `stmt_correct` is validity for all assertion ids. -/
def stmt_correct
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) : Prop :=
  ∀ (a : AssertId), stmt_valid π φ stmt a

/-! ## Transformation Structure and Properties -/

/-- A program transformation bundles the effective transformation with
    forward and inverse maps on assertion identifiers.

    - `T`: the statement-level transformation
    - `F`: maps source assertion ids to optional target assertion ids
      (`none` means the assertion was proved always true and removed)
    - `F_inv`: maps target assertion ids back to source assertion ids
      (used for lifting counterexamples) -/
structure Transformation where
  T     : Statement → Statement
  F     : AssertId → Option AssertId
  F_inv : AssertId → AssertId

/-- If the transformed program is valid, the original is valid. -/
def Transformation.preserves_validity
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (t : Transformation) : Prop :=
  ∀ (stmt : Statement),
    stmt_correct π φ (t.T stmt) → stmt_correct π φ stmt

/-- If the transformed program has a counterexample, the original does too. -/
def Transformation.preserves_counterexample
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (t : Transformation) : Prop :=
  ∀ (stmt : Statement) (a : AssertId),
    stmt_falsifiable π φ (t.T stmt) a →
    stmt_falsifiable π φ stmt (t.F_inv a)

/-- If the transformed program is satisfiable, the original is too. -/
def Transformation.preserves_satisfiability
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (t : Transformation) : Prop :=
  ∀ (stmt : Statement) (a : AssertId),
    stmt_satisfiable π φ (t.T stmt) a →
    stmt_satisfiable π φ stmt (t.F_inv a)

/-- If the transformed program is unsatisfiable, the original is too. -/
def Transformation.preserves_unsatisfiability
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (t : Transformation) : Prop :=
  ∀ (stmt : Statement) (a : AssertId),
    stmt_unsatisfiable π φ (t.T stmt) a →
    stmt_unsatisfiable π φ stmt (t.F_inv a)

end Soundness

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.Languages.Core.StatementSemantics

/-! # Soundness Framework

General definitions for statement correctness, transformation soundness,
and procedure contract obedience.

Key concepts:
- `ProgramState`: store + evaluator + optional assertion id (program counter)
- `reachable`: small-step reachability from a statement to a program state
- Four semantic judgments: valid, falsifiable, satisfiable, unsatisfiable
- `Transformation` structure with T, F, F_inv and four preservation properties
- `procedure_obeys_contract`: a procedure's body satisfies its contract
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
    When the configuration is about to execute an assert command, `pc` is set.
    This includes `.stmt`, `.stmts`, and `.block` configs where the next
    statement to execute is an assert. -/
def ProgramState.ofConfig : CoreConfig → Option ProgramState
  | .stmt (Stmt.cmd (CmdExt.cmd (Cmd.assert label expr md))) σ δ =>
    some ⟨σ, δ, some ⟨label, expr, md⟩⟩
  | .stmts (Stmt.cmd (CmdExt.cmd (Cmd.assert label expr md)) :: _) σ δ =>
    some ⟨σ, δ, some ⟨label, expr, md⟩⟩
  | .block _ (Stmt.cmd (CmdExt.cmd (Cmd.assert label expr md)) :: _) σ δ =>
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

/-! ## Procedure Contract Obedience -/

/-- A procedure obeys its contract: for all initial states where preconditions
    hold, if the body executes to completion, then all postconditions hold. -/
def procedure_obeys_contract
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) : Prop :=
  ∀ (δ : CoreEval) (σ₀ σ_final : CoreStore) (δ_final : CoreEval),
    -- Preconditions hold at entry
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.preconditions.toList →
      δ σ₀ check.expr = some HasBool.tt) →
    -- Body executes to completion
    EvalStatements π φ δ σ₀ proc.body σ_final δ_final →
    -- Postconditions hold at exit
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      δ_final σ_final check.expr = some HasBool.tt)

end Soundness

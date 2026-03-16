/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.Languages.Core.StatementSemantics

/-! # Soundness Framework

General definitions for statement correctness, transformation soundness,
and procedure contract obedience. Uses small-step semantics throughout.
-/

namespace Strata.Soundness

open Core Imperative

/-! ## Core-specific small-step abbreviations -/

abbrev CoreConfig := Config Expression Command
abbrev CoreStep (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)
abbrev CoreStepStar (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)

/-! ## Assertion Identity -/

/-- An assertion identifier: label + expression + metadata -/
structure AssertId where
  label : CoreLabel
  expr  : Expression.Expr
  md    : MetaData Expression

/-! ## Program State -/

/-- A program state at an assertion: carries the store, evaluator, and assertion id. -/
structure ProgramState where
  store : CoreStore
  eval  : CoreEval
  pc    : AssertId

/-- Extract a `ProgramState` from a small-step configuration.
    Returns `some` only when at an assert command. -/
def ProgramState.ofConfig : CoreConfig → Option ProgramState
  | .stmt (Stmt.cmd (CmdExt.cmd (Cmd.assert label expr md))) σ δ =>
    some ⟨σ, δ, ⟨label, expr, md⟩⟩
  | .stmts (Stmt.cmd (CmdExt.cmd (Cmd.assert label expr md)) :: _) σ δ =>
    some ⟨σ, δ, ⟨label, expr, md⟩⟩
  | .block _ inner => ProgramState.ofConfig inner
  | .seq inner _ => ProgramState.ofConfig inner
  | _ => none

/-- A program state is reachable from a statement if there exists an initial
    configuration and a multi-step execution path to a configuration whose
    program state matches. -/
def reachable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (ps : ProgramState) : Prop :=
  ∃ (δ₀ : CoreEval) (σ₀ : CoreStore) (cfg : CoreConfig),
    CoreStepStar π φ (.stmt stmt σ₀ δ₀) cfg ∧
    ProgramState.ofConfig cfg = some ps

/-! ## Statement Correctness -/

/-- **Validity**: For all reachable states at a given assertion, the predicate holds. -/
def stmt_valid
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) (a : AssertId) : Prop :=
  ∀ (ps : ProgramState),
    reachable π φ stmt ps →
    ps.pc = a →
    ps.eval ps.store a.expr = some HasBool.tt

/-- `stmt_correct` is validity for all assertion ids. -/
def stmt_correct
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) : Prop :=
  ∀ (a : AssertId), stmt_valid π φ stmt a

/-! ## Procedure Contract Obedience -/

/-- A procedure obeys its contract: for all initial states where preconditions
    hold, if the body executes to a terminal state, then all postconditions
    hold at exit. Uses small-step semantics. -/
def procedure_obeys_contract
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) : Prop :=
  ∀ (δ : CoreEval) (σ₀ σ_final : CoreStore) (δ_final : CoreEval),
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.preconditions.toList →
      δ σ₀ check.expr = some HasBool.tt) →
    CoreStepStar π φ (.stmts proc.body σ₀ δ) (.terminal σ_final δ_final) →
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      δ_final σ_final check.expr = some HasBool.tt)

/-! ## Transformation Structure -/

/-- A program transformation bundles the effective transformation with
    forward and inverse maps on assertion identifiers. -/
structure Transformation where
  T     : Statement → Statement
  F     : AssertId → Option AssertId
  F_inv : AssertId → AssertId

end Strata.Soundness

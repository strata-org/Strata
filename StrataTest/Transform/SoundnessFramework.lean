/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.Languages.Core.StatementSemantics

/-! # Soundness Framework

General definitions for statement correctness, transformation soundness,
and procedure contract obedience.
-/

namespace Soundness

open Core Imperative

/-! ## Assertion Identity -/

/-- An assertion identifier: label + expression + metadata -/
structure AssertId where
  label : CoreLabel
  expr  : Expression.Expr
  md    : MetaData Expression

/-! ## Reachability and Correctness (Big-Step)

An assert in a statement list is reachable if the prefix before it
evaluates (big-step) to some state. The assert's condition is then
checked at that state. -/

/-- An assert is reachable in a statement list if the prefix before it evaluates. -/
def reachable_in_stmts
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement) (a : AssertId) (σ : CoreStore) (δ : CoreEval) : Prop :=
  ∃ (δ₀ : CoreEval) (σ₀ : CoreStore) (before after : List Statement),
    stmts = before ++ [Statement.assert a.label a.expr a.md] ++ after ∧
    EvalStatements π φ δ₀ σ₀ before σ δ

/-- A statement list is correct if for every reachable assert, the condition holds. -/
def stmts_correct
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement) : Prop :=
  ∀ (a : AssertId) (σ : CoreStore) (δ : CoreEval),
    reachable_in_stmts π φ stmts a σ δ →
    δ σ a.expr = some HasBool.tt

/-- A block statement is correct if its body (statement list) is correct. -/
def stmt_correct
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmt : Statement) : Prop :=
  match stmt with
  | Stmt.block _ stmts _ => stmts_correct π φ stmts
  | _ => True  -- non-block statements: no assertions to check

/-! ## Procedure Contract Obedience -/

/-- A procedure obeys its contract: for all initial states where preconditions
    hold, if the body executes to completion, then all postconditions hold. -/
def procedure_obeys_contract
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) : Prop :=
  ∀ (δ : CoreEval) (σ₀ σ_final : CoreStore) (δ_final : CoreEval),
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.preconditions.toList →
      δ σ₀ check.expr = some HasBool.tt) →
    EvalStatements π φ δ σ₀ proc.body σ_final δ_final →
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

end Soundness

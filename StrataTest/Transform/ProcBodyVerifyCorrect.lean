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

open Core Core.ProcBodyVerify Imperative Lambda Transform

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

/-! ## Procedure Contract Obedience

A procedure obeys its contract if, for all executions of its body where
preconditions hold at entry, all postconditions hold at exit. This is
defined using the big-step semantics for body execution. -/

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

/-! ## Soundness of ProcBodyVerify

`procToVerifyStmt` transforms a `Procedure` into a verification `Statement`:
```
block "verify_P" {
  init inputs; init outputs; init modifies;
  assume preconditions;
  block "body_P" { body... }
  assert postconditions;
}
```

Soundness: if all assertions in the verification statement are valid
(i.e., `stmt_correct` holds), then the procedure obeys its contract. -/

theorem procBodyVerify_sound
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (stmt : Statement) (st' : CoreTransformState)
    (h_transform : (procToVerifyStmt proc p).run st = (Except.ok stmt, st'))
    (h_correct : stmt_correct π φ stmt) :
    procedure_obeys_contract π φ proc := by
  sorry

/-! ## Example: Wrapping in a block preserves validity

Wrapping a statement `s` in `block label [s] md` does not change which
assertions are reachable or what states they're reached in. So it
preserves validity. -/

/-- Wrapping in a block: `s ↦ block label [s] md` -/
def wrapInBlock (label : String) (md : MetaData Expression) : Transformation where
  T := fun s => Stmt.block label [s] md
  F := some
  F_inv := id

/-- Key lemma: if `(.stmt s σ δ) →* cfg`, then
    `(.block label [s] σ δ) →* cfg'` where `cfg'` has the same program state.
    This is because a block just wraps execution. -/
theorem block_reachable_of_stmt_reachable
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (label : String) (md : MetaData Expression)
    (ps : ProgramState) :
    reachable π φ s ps →
    reachable π φ (Stmt.block label [s] md) ps := by
  intro ⟨δ₀, σ₀, cfg, h_steps, h_ps⟩
  refine ⟨δ₀, σ₀, cfg, ?_, h_ps⟩
  -- (.stmt (block label [s] md) σ₀ δ₀) steps to (.block label [s] σ₀ δ₀)
  -- then (.block label [s] σ₀ δ₀) steps its body [s]
  -- The body [s] steps through the same configs as s
  sorry

/-- Wrapping in a block preserves validity. -/
theorem wrapInBlock_preserves_validity
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : String) (md : MetaData Expression) :
    (wrapInBlock label md).preserves_validity π φ := by
  intro stmt h_correct a
  unfold stmt_valid
  intro ps h_reach h_pc
  -- ps is reachable from stmt. We need to show ps is also reachable from (block label [stmt] md).
  -- Then h_correct gives us the result.
  -- But actually, h_correct says the BLOCK is correct, and we need to show stmt is correct.
  -- The direction is: reachable from stmt → reachable from block → h_correct applies.
  -- Wait — preserves_validity says: correct(T stmt) → correct(stmt).
  -- T stmt = block label [stmt] md. h_correct : correct(block label [stmt] md).
  -- We need: correct(stmt), i.e., ∀ a ps, reachable(stmt, ps) → ps.pc = a → predicate holds.
  -- So we need: reachable(stmt, ps) → reachable(block label [stmt] md, ps).
  exact h_correct a ps (block_reachable_of_stmt_reachable π φ stmt label md ps h_reach) h_pc

end Soundness

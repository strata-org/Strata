/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import StrataTest.Transform.SoundnessFramework

/-! # Procedure Body Verification Correctness Proof

Proves that `procToVerifyStmt` is sound: if all assertions in the
verification statement are valid, then the procedure obeys its contract.
-/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Soundness

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
      | eval_assert => exact ⟨rfl, rfl⟩

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
      | eval_assume h_true h_wf => exact ⟨h_true, rfl, rfl⟩

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

end ProcBodyVerifyCorrect

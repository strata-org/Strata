/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.StmtSemantics

/-! # Tests for the small-step `StepStmt` semantics -/

namespace StepStmtTest
open Imperative

---------------------------------------------------------------------

/-! ## A minimal `PureExpr` instantiation

`Expr` has just `.tt` / `.ff` / `.not`, which is enough for loop guards and
satisfies the `HasBool` / `HasNot` typeclass requirements of `StepStmt`. -/

inductive Expr where
  | tt
  | ff
  | not (e : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- Types — only a boolean type is needed for this test. -/
inductive Ty where
  | Bool
  deriving DecidableEq, Repr, Inhabited

abbrev MiniPureExpr : PureExpr :=
  { Ident := String,
    EqIdent := instDecidableEqString,
    Expr := Expr,
    Ty := Ty,
    ExprMetadata := Unit,
    TyEnv := Unit,
    TyContext := Unit,
    EvalEnv := Unit }

instance : HasBool MiniPureExpr where
  tt := .tt
  ff := .ff
  tt_is_not_ff := by intro h; cases h
  boolTy := .Bool
  isTrue := fun e => match e with | .tt => true | _ => false
  isFalse := fun e => match e with | .ff => true | _ => false

instance : HasNot MiniPureExpr where
  not := .not

---------------------------------------------------------------------

/-! ## Evaluator and well-formedness setup -/

/-- Normalise an `Expr` into a boolean constant by folding `.not`s.
    Closed `.tt` and `.ff` stay; `.not .tt` collapses to `.ff`, and so on. -/
def Expr.normBool : Expr → Expr
  | .tt => .tt
  | .ff => .ff
  | .not e =>
    match Expr.normBool e with
    | .tt => .ff
    | .ff => .tt
    | e'  => .not e'

theorem Expr.normBool_not_tt_iff_ff (e : Expr) :
    Expr.normBool (Expr.not e) = Expr.ff ↔ Expr.normBool e = Expr.tt := by
  show (match Expr.normBool e with
        | Expr.tt => Expr.ff | Expr.ff => Expr.tt | e' => Expr.not e') = Expr.ff ↔ _
  cases Expr.normBool e <;> simp

theorem Expr.normBool_not_ff_iff_tt (e : Expr) :
    Expr.normBool (Expr.not e) = Expr.tt ↔ Expr.normBool e = Expr.ff := by
  show (match Expr.normBool e with
        | Expr.tt => Expr.ff | Expr.ff => Expr.tt | e' => Expr.not e') = Expr.tt ↔ _
  cases Expr.normBool e <;> simp

/-- The store is not used — all expressions in this test are closed. -/
def miniEval : SemanticEval MiniPureExpr :=
  fun _σ e => some e.normBool

theorem miniEval_wfBool : WellFormedSemanticEvalBool miniEval := by
  unfold WellFormedSemanticEvalBool; intro σ e
  show (_ = some Expr.tt ↔ _ = some Expr.ff) ∧ (_ = some Expr.ff ↔ _ = some Expr.tt)
  simp only [miniEval, Option.some.injEq]
  exact ⟨(Expr.normBool_not_tt_iff_ff e).symm, (Expr.normBool_not_ff_iff_tt e).symm⟩

/-- Empty store: no identifier is defined. -/
def emptyStore : SemanticStore MiniPureExpr := fun _ => none

/-- Initial execution environment. -/
def ρ₀ : Env MiniPureExpr :=
  { store := emptyStore, eval := miniEval, hasFailure := false }

/-- `ExtendEval` is irrelevant to this test, but we need a value. -/
def miniExtendEval : ExtendEval MiniPureExpr :=
  fun δ _ _ => δ

/-- Arbitrary command type — unused, but `Stmt` needs something. -/
abbrev CmdT := Unit

/-- `EvalCmd` is trivially false since the program contains no commands. -/
def noCmd : EvalCmdParam MiniPureExpr CmdT := fun _ _ _ _ _ => False

---------------------------------------------------------------------

/-! ## Test: `loop { exit }` exactly exits the loop, not the outer block.

A minimal program `loop { exit }` is shown to step to `.terminal`.  This
verifies that an unlabeled `exit` inside the body terminates just the
loop (and not the enclosing block).
-/

/-- The test program: a deterministic `while (true)` loop whose only body
    statement is an unlabeled `exit`. -/
def prog : Stmt MiniPureExpr CmdT :=
  .loop (.det .tt) none [] [.exit none .empty] .empty

/-- The test: `.stmt prog ρ₀ →* .terminal ρ₀` -/
theorem progReachesTerminal :
    StepStmtStar MiniPureExpr noCmd miniExtendEval
      (.stmt prog ρ₀) (.terminal ρ₀) := by
  -- Each step explicitly named; Lean fills the rest.
  have htt : ρ₀.eval ρ₀.store HasBool.tt = some HasBool.tt := rfl
  -- Step 1: step_loop_enter with hasInvFailure = false.
  refine .step _ _ _
    (StepStmt.step_loop_enter (hasInvFailure := false) htt ?inv_bool ?inv_iff
      miniEval_wfBool) ?rest
  · intro _ hmem; nomatch hmem
  · constructor <;> intro h
    · cases h
    · rcases h with ⟨_, hmem, _⟩; nomatch hmem
  -- Post-state: ρ₀' = {ρ₀ with hasFailure := ρ₀.hasFailure || false} definitionally equal to ρ₀.
  -- Step 2: step_block_body (step_stmts_cons).
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) ?rest2
  -- Step 3: step_block_body (step_seq_inner step_exit).
  refine .step _ _ _
    (StepStmt.step_block_body (StepStmt.step_seq_inner StepStmt.step_exit)) ?rest3
  -- Step 4: step_block_body step_seq_exit.
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_seq_exit) ?rest4
  -- Step 5: step_block_exit_none.
  exact .step _ _ _ StepStmt.step_block_exit_none (.refl _)

---------------------------------------------------------------------

/-! ## Test: `block L { if tt then { exit } else { skip } }` terminates
    with the exit caught by the outer block via the then-branch. -/

def progIteThen : Stmt MiniPureExpr CmdT :=
  .block "L"
    [.ite (.det .tt) [.exit none .empty] [] .empty]
    .empty

/-- The test: `.stmt progIteThen ρ₀ →* .terminal ρ₀` via the `then` branch. -/
theorem progIteThenReachesTerminal :
    StepStmtStar MiniPureExpr noCmd miniExtendEval
      (.stmt progIteThen ρ₀) (.terminal ρ₀) := by
  have htt : ρ₀.eval ρ₀.store HasBool.tt = some HasBool.tt := rfl
  -- Step 1: step_block — enter the outer block.
  refine .step _ _ _ StepStmt.step_block ?rest1
  -- Step 2: step_block_body (step_stmts_cons) — break the singleton stmts list.
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) ?rest2
  -- Step 3: step_block_body (step_seq_inner step_ite_true) — take the then branch.
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner (StepStmt.step_ite_true htt miniEval_wfBool))) ?rest3
  -- Step 4: step_block_body (step_seq_inner step_stmts_cons) — destructure the then body.
  refine .step _ _ _
    (StepStmt.step_block_body (StepStmt.step_seq_inner StepStmt.step_stmts_cons)) ?rest4
  -- Step 5: step_block_body (step_seq_inner (step_seq_inner step_exit)) — fire the exit.
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner (StepStmt.step_seq_inner StepStmt.step_exit))) ?rest5
  -- Step 6: step_block_body (step_seq_inner step_seq_exit) — propagate past the inner seq.
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner StepStmt.step_seq_exit)) ?rest6
  -- Step 7: step_block_body step_seq_exit — propagate past the outer seq.
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_seq_exit) ?rest7
  -- Step 8: step_block_exit_none — the outer block catches the unlabeled exit.
  exact .step _ _ _ StepStmt.step_block_exit_none (.refl _)

---------------------------------------------------------------------

/-! ## Test: `block L { if ff then { skip } else { exit } }` terminates
    with the exit caught by the outer block via the else-branch. -/

def progIteElse : Stmt MiniPureExpr CmdT :=
  .block "L"
    [.ite (.det .ff) [] [.exit none .empty] .empty]
    .empty

/-- The test: `.stmt progIteElse ρ₀ →* .terminal ρ₀` via the `else` branch. -/
theorem progIteElseReachesTerminal :
    StepStmtStar MiniPureExpr noCmd miniExtendEval
      (.stmt progIteElse ρ₀) (.terminal ρ₀) := by
  have hff : ρ₀.eval ρ₀.store HasBool.ff = some HasBool.ff := rfl
  refine .step _ _ _ StepStmt.step_block ?rest1
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) ?rest2
  -- step_ite_false — take the else branch.
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner (StepStmt.step_ite_false hff miniEval_wfBool))) ?rest3
  refine .step _ _ _
    (StepStmt.step_block_body (StepStmt.step_seq_inner StepStmt.step_stmts_cons)) ?rest4
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner (StepStmt.step_seq_inner StepStmt.step_exit))) ?rest5
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner StepStmt.step_seq_exit)) ?rest6
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_seq_exit) ?rest7
  exact .step _ _ _ StepStmt.step_block_exit_none (.refl _)

---------------------------------------------------------------------

end StepStmtTest

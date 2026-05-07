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

/-! ## touchedVars tests

Verify that `Stmt.touchedVars` includes both read and write variables
(= `modifiedOrDefinedVars ++ getVars`), while `Stmt.modifiedOrDefinedVars`
only includes the write-set. -/

/-- `HasVarsPure` for `Expr`: our expressions have no free variables
    (they are all closed boolean constants). -/
instance : HasVarsPure MiniPureExpr Expr where
  getVars _ := []

/-- `HasVarsPure` for `Cmd MiniPureExpr`: delegate to `Cmd.getVars`. -/
instance : HasVarsPure MiniPureExpr (Cmd MiniPureExpr) where
  getVars := Cmd.getVars

/-- Test: `init x : Bool := tt` has `modifiedOrDefinedVars = ["x"]`
    and `touchedVars = ["x"]` (since `.tt` has no free variables). -/
example : (Stmt.cmd (P := MiniPureExpr)
    (Cmd.init (P := MiniPureExpr) "x" .Bool (.det .tt) .empty)).modifiedOrDefinedVars
    = ["x"] := by native_decide

example : (Stmt.cmd (P := MiniPureExpr)
    (Cmd.init (P := MiniPureExpr) "x" .Bool (.det .tt) .empty)).touchedVars
    = ["x"] := by native_decide

/-- Test: `set x := tt` has `modifiedOrDefinedVars = ["x"]`
    and `touchedVars = ["x"]` (since `.tt` has no free variables). -/
example : (Stmt.cmd (P := MiniPureExpr)
    (Cmd.set (P := MiniPureExpr) "x" (.det .tt) .empty)).modifiedOrDefinedVars
    = ["x"] := by native_decide

example : (Stmt.cmd (P := MiniPureExpr)
    (Cmd.set (P := MiniPureExpr) "x" (.det .tt) .empty)).touchedVars
    = ["x"] := by native_decide

/-- Now extend `Expr` to include a variable reference so we can test
    that `getVars` picks up read variables. -/
inductive Expr2 where
  | tt
  | ff
  | not (e : Expr2)
  | var (name : String)
  deriving DecidableEq, Repr, Inhabited

abbrev MiniPureExpr2 : PureExpr :=
  { Ident := String,
    EqIdent := instDecidableEqString,
    Expr := Expr2,
    Ty := Ty,
    ExprMetadata := Unit,
    TyEnv := Unit,
    TyContext := Unit,
    EvalEnv := Unit }

instance : HasBool MiniPureExpr2 where
  tt := .tt
  ff := .ff
  tt_is_not_ff := by intro h; cases h
  boolTy := .Bool

instance : HasNot MiniPureExpr2 where
  not := .not

/-- Get free variables from `Expr2`. -/
def Expr2.getVars : Expr2 → List String
  | .var n => [n]
  | .not e => e.getVars
  | _ => []

/-- `HasVarsPure` for `Expr2`: only `.var` contributes a variable. -/
instance : HasVarsPure MiniPureExpr2 Expr2 where
  getVars := Expr2.getVars

instance : HasVarsPure MiniPureExpr2 (Cmd MiniPureExpr2) where
  getVars := Cmd.getVars

/-- Test: `set x := var "y"` has `modifiedOrDefinedVars = ["x"]` (write-set only)
    but `touchedVars = ["x", "y"]` (includes the read variable "y"). -/
example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.set (P := MiniPureExpr2) "x" (.det (.var "y")) .empty)).modifiedOrDefinedVars
    = ["x"] := by native_decide

example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.set (P := MiniPureExpr2) "x" (.det (.var "y")) .empty)).touchedVars
    = ["x", "y"] := by native_decide

/-- Test: `init z : Bool := var "w"` has `modifiedOrDefinedVars = ["z"]`
    but `touchedVars = ["z", "w"]`. -/
example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.init (P := MiniPureExpr2) "z" .Bool (.det (.var "w")) .empty)).modifiedOrDefinedVars
    = ["z"] := by native_decide

example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.init (P := MiniPureExpr2) "z" .Bool (.det (.var "w")) .empty)).touchedVars
    = ["z", "w"] := by native_decide

/-- Test: Block touchedVars includes both read and write vars from all stmts. -/
example : (Block.touchedVars (P := MiniPureExpr2) (C := Cmd MiniPureExpr2)
    [.cmd (Cmd.init (P := MiniPureExpr2) "a" .Bool (.det (.var "b")) .empty),
     .cmd (Cmd.set (P := MiniPureExpr2) "c" (.det (.var "d")) .empty)])
    = ["a", "c", "b", "d"] := by native_decide

example : (Block.modifiedOrDefinedVars (P := MiniPureExpr2) (C := Cmd MiniPureExpr2)
    [.cmd (Cmd.init (P := MiniPureExpr2) "a" .Bool (.det (.var "b")) .empty),
     .cmd (Cmd.set (P := MiniPureExpr2) "c" (.det (.var "d")) .empty)])
    = ["a", "c"] := by native_decide

---------------------------------------------------------------------

/-! ## Block scoping tests

Verify that variables `init`'d inside a block are not visible after the
block exits. We step through a program and verify the terminal store
has `none` for block-local variables thanks to `projectStore`. -/

/-- A `HasFvar` instance for `MiniPureExpr` — needed by `EvalCmd`. -/
instance : HasFvar MiniPureExpr where
  mkFvar _ := .tt  -- unused but required
  getFvar _ := none   -- no expression is a free variable reference

/-- `WellFormedSemanticEvalVar` for `miniEval` — trivially holds since
    `getFvar` always returns `none`. -/
theorem miniEval_wfVar : WellFormedSemanticEvalVar (P := MiniPureExpr) miniEval := by
  unfold WellFormedSemanticEvalVar
  intro e v σ hfv
  simp [HasFvar.getFvar] at hfv

/-- The standard `EvalCmd` for `Cmd MiniPureExpr`. -/
def stdEvalCmd : EvalCmdParam MiniPureExpr (Cmd MiniPureExpr) :=
  EvalCmd MiniPureExpr

/-- A store where "x" is defined (maps to `.tt`), everything else is `none`. -/
def storeWithX : SemanticStore MiniPureExpr :=
  fun v => if v == "x" then some .tt else none

/-- Env with "x" defined. -/
def ρ_x : Env MiniPureExpr :=
  { store := storeWithX, eval := miniEval, hasFailure := false }

/-- Program: `block B { init y : Bool := tt }`.
    After stepping, "y" should not be visible (projected away). -/
def progBlockScope : Stmt MiniPureExpr (Cmd MiniPureExpr) :=
  .block "B" [.cmd (.init "y" .Bool (.det .tt) .empty)] .empty

/-- Store that has both "x" and "y" defined. -/
def storeWithXY : SemanticStore MiniPureExpr :=
  fun v => if v == "x" then some .tt
            else if v == "y" then some .tt
            else none

/-- Helper: storeWithXY agrees with storeWithX on all variables except "y". -/
private theorem storeWithXY_frame :
    ∀ v : String, "y" ≠ v → storeWithXY v = storeWithX v := by
  intro v hne
  unfold storeWithXY storeWithX
  simp only [beq_iff_eq]
  split
  · simp
  · split
    · rename_i heq; exact absurd heq.symm hne
    · rfl

/-- After the block exits, the store should have "x" defined but "y" = none. -/
theorem blockScopeTest :
    StepStmtStar MiniPureExpr stdEvalCmd miniExtendEval
      (.stmt progBlockScope ρ_x)
      (.terminal { store := storeWithX, eval := miniEval, hasFailure := false }) := by
  -- Step 1: step_block — enter the block, saving ρ_x.store as σ_parent.
  refine .step _ _ _ StepStmt.step_block ?_
  -- Step 2: step_block_body (step_stmts_cons) — process the singleton list.
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) ?_
  -- Step 3: step_block_body (step_seq_inner step_cmd) — evaluate `init y := tt`.
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner
        (StepStmt.step_cmd
          (EvalCmd.eval_init (P := MiniPureExpr)
            (show miniEval storeWithX .tt = some .tt from rfl)
            (InitState.init
              (show storeWithX "y" = none from rfl)
              (show storeWithXY "y" = some .tt from rfl)
              storeWithXY_frame)
            miniEval_wfVar)))) ?_
  -- Step 4: step_block_body (step_seq_done) — seq is done, go to stmts [].
  refine .step _ _ _
    (StepStmt.step_block_body StepStmt.step_seq_done) ?_
  -- Step 5: step_block_body (step_stmts_nil) — empty list becomes terminal.
  refine .step _ _ _
    (StepStmt.step_block_body StepStmt.step_stmts_nil) ?_
  -- Step 6: step_block_done — project store.
  have hproj : projectStore (P := MiniPureExpr) storeWithX storeWithXY = storeWithX := by
    ext v
    simp [projectStore, storeWithX, storeWithXY]
    split <;> simp_all
  conv => rhs; rw [show Env.mk storeWithX miniEval false =
    { (Env.mk storeWithXY miniEval false) with store := projectStore storeWithX storeWithXY }
    from by simp [hproj]]
  exact .step _ _ _ StepStmt.step_block_done (.refl _)

/-- Directly verify that `projectStore` maps "y" to `none`. -/
example : projectStore (P := MiniPureExpr) storeWithX storeWithXY "y" = none := by
  simp [projectStore, storeWithX, Option.isSome]

/-- Directly verify that `projectStore` preserves "x". -/
example : projectStore (P := MiniPureExpr) storeWithX storeWithXY "x" = some .tt := by
  simp [projectStore, storeWithX, storeWithXY, Option.isSome]

---------------------------------------------------------------------

/-! ## Loop scoping tests

Verify that variables `init`'d inside a loop body are scoped to each
iteration. The loop body is wrapped in an anonymous block, so after
each iteration (and after loop exit) the init'd variable is projected
away.

Program: with "x" already defined, `loop (true) { init y := tt; exit }`
After the loop exits, "y" should not be visible in the final store. -/

/-- Program: `loop (tt) { init y := tt ; exit }`.
    The loop enters one iteration, inits y, then immediately exits.
    The anonymous block wrapper projects "y" away. -/
def progLoopScope : Stmt MiniPureExpr (Cmd MiniPureExpr) :=
  .loop (.det .tt) none [] [.cmd (.init "y" .Bool (.det .tt) .empty), .exit none .empty] .empty

/-- After stepping the loop, the final store should still be `storeWithX`
    (the variable "y" is projected away by the anonymous block). -/
theorem loopScopeTest :
    StepStmtStar MiniPureExpr stdEvalCmd miniExtendEval
      (.stmt progLoopScope ρ_x)
      (.terminal { store := storeWithX, eval := miniEval, hasFailure := false }) := by
  have htt : ρ_x.eval ρ_x.store HasBool.tt = some HasBool.tt := rfl
  -- Step 1: step_loop_enter — guard is true, enter the loop body wrapped in anon block.
  refine .step _ _ _
    (StepStmt.step_loop_enter (hasInvFailure := false) htt ?_ ?_ miniEval_wfBool) ?_
  · intro _ hmem; nomatch hmem
  · constructor <;> intro h
    · cases h
    · rcases h with ⟨_, hmem, _⟩; nomatch hmem
  -- Now config is:
  -- .block .none storeWithX (.stmts [init y; exit; loop...] ρ_x)
  -- Step 2: step_block_body (step_stmts_cons)
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) ?_
  -- Step 3: step_block_body (step_seq_inner step_cmd) — init y := tt
  refine .step _ _ _
    (StepStmt.step_block_body
      (StepStmt.step_seq_inner
        (StepStmt.step_cmd
          (EvalCmd.eval_init (P := MiniPureExpr)
            (show miniEval storeWithX .tt = some .tt from rfl)
            (InitState.init
              (show storeWithX "y" = none from rfl)
              (show storeWithXY "y" = some .tt from rfl)
              storeWithXY_frame)
            miniEval_wfVar)))) ?_
  -- Step 4: step_block_body (step_seq_done) — inner stmt is terminal, advance to rest
  refine .step _ _ _
    (StepStmt.step_block_body StepStmt.step_seq_done) ?_
  -- Step 5: step_block_body (step_stmts_cons) — process [exit, loop...]
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) ?_
  -- Step 6: step_block_body (step_seq_inner step_exit) — fire the exit
  refine .step _ _ _
    (StepStmt.step_block_body (StepStmt.step_seq_inner StepStmt.step_exit)) ?_
  -- Step 7: step_block_body step_seq_exit — propagate exit past remaining stmts
  refine .step _ _ _ (StepStmt.step_block_body StepStmt.step_seq_exit) ?_
  -- Step 8: step_block_exit_none — anonymous block catches unlabeled exit, projects store.
  have hproj : projectStore (P := MiniPureExpr) storeWithX storeWithXY = storeWithX := by
    ext v
    simp [projectStore, storeWithX, storeWithXY]
    split <;> simp_all
  conv => rhs; rw [show Env.mk storeWithX miniEval false =
    { (Env.mk storeWithXY miniEval false) with store := projectStore storeWithX storeWithXY }
    from by simp [hproj]]
  exact .step _ _ _ StepStmt.step_block_exit_none (.refl _)

---------------------------------------------------------------------

end StepStmtTest

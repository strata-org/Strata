/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.StmtSemantics
meta import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.CmdSemantics

meta section

/-! # Tests for the small-step `StepStmtE` semantics -/

namespace StepStmtTest
open Imperative

---------------------------------------------------------------------

/-! ## A minimal `PureExpr` instantiation

`Expr` has just `.tt` / `.ff` / `.not`, which is enough for loop guards and
satisfies the `HasBool` / `HasNot` typeclass requirements of `StepStmtE`. -/

inductive Expr where
  | tt
  | ff
  | not (e : Expr)
  /-- An "operator" reference — opaque to `miniEval` (returns `some (.op n)`),
      but observable to evaluator extensions that could give `.op n` a
      definite boolean value. -/
  | op (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Types — only a boolean type is needed for this test. -/
inductive Ty where
  | Bool
  deriving DecidableEq, Repr, Inhabited

/-- Normalise an `Expr` into a boolean constant by folding `.not`s.
    Closed `.tt` and `.ff` stay; `.not .tt` collapses to `.ff`, and so on.
    `.op` is opaque to the base evaluator and stays as-is. -/
def Expr.normBool : Expr → Expr
  | .tt => .tt
  | .ff => .ff
  | .op n => .op n
  | .not e =>
    match Expr.normBool e with
    | .tt => .ff
    | .ff => .tt
    | e'  => .not e'

abbrev MiniPureExpr : PureExpr :=
  { Ident := String,
    EqIdent := instDecidableEqString,
    Expr := Expr,
    Ty := Ty,
    ExprMetadata := Unit,
    TyEnv := Unit,
    TyContext := Unit,
    Factory := Unit,
    Val := Expr,
    eval := fun _f _σ e => some e.normBool }

instance : HasVal MiniPureExpr where
  value _ _ := True
  valueOfTy _ _ _ := True

instance : HasFvars MiniPureExpr where
  getFvars _ := []
  getTypedFvars _ := []

instance : LawfulHasVal MiniPureExpr where
  valueOfTy_isVal := fun _ _ _ h => h
  valueOfTy_congr := fun _ _ _ _ _ _ _ _ => trivial

instance : HasBool MiniPureExpr where
  tt := .tt
  ff := .ff
  tt_is_not_ff := by intro h; cases h
  boolTy := .Bool
  ttVal _ := .tt
  ffVal _ := .ff
  ttVal_ne_ffVal _ := by intro h; cases h
  boolIsValOfTy := fun _ => ⟨trivial, trivial⟩

instance : HasBoolOps MiniPureExpr where
  not := .not
  and := fun _ _ => .tt
  imp := fun _ _ => .tt

instance : HasInt MiniPureExpr where
  zero := .ff
  intTy := .Bool
  isNumeral := fun _ => true
  isNumeralVal := fun _ => true
  zeroIsNumeral := rfl
  numeralHasNoFvars := fun _ _ => rfl

instance : HasIntOps MiniPureExpr where
  eq := fun _ _ => .tt
  lt := fun _ _ => .ff

---------------------------------------------------------------------

/-! ## Evaluator and well-formedness setup -/

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
  fun _f _σ e => some e.normBool

/-- Empty store: no identifier is defined. -/
def emptyStore : SemanticStore MiniPureExpr := fun _ => none

/-- Initial execution environment. -/
def ρ₀ : Env MiniPureExpr :=
  { store := emptyStore, factory := () }

/-- Arbitrary command type — unused, but `Stmt` needs something. -/
abbrev CmdT := Unit

/-- The command relation is trivially false since the program contains no
commands. -/
def noCmd : EvalCmdParamE MiniPureExpr CmdT Unit := fun _ _ _ _ _ => False

---------------------------------------------------------------------

/-! ## Test: `block "L" { loop { exit "L" } }` exits the loop via labeled exit.

The `exit "L"` propagates out of body's per-iteration block and the loop's
recursive step (mismatch propagates), reaching the labeled outer block.
-/

/-- The test program: a labeled outer block containing a deterministic
    `while (true)` loop whose body is `exit "L"`. -/
def prog : Stmt MiniPureExpr CmdT :=
  .block "L"
    [.loop (.det .tt) none [] [.exit "L" .empty] .empty]
    .empty

/-- The test: `.stmt prog ρ₀ →* .terminal ρ₀` -/
theorem progReachesTerminal :
    StepStmtStarE MiniPureExpr noCmd
      (.stmt prog ρ₀) [] (.terminal ρ₀) := by
  have htt : MiniPureExpr.eval () ρ₀.store HasBool.tt = some (HasBool.ttVal ()) := rfl
  -- Step 1: step_block — enter the outer labeled block.
  refine .step _ [] _ [] _ StepStmtE.step_block ?_
  -- Step 2: step_block_body step_stmts_cons.
  refine .step _ [] _ [] _ (StepStmtE.step_block_body StepStmtE.step_stmts_cons) ?_
  -- Step 3: step_block_body (step_seq_inner step_loop_enter).
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_loop_enter htt))) ?_
  -- Now: outer block (L) > seq > seq > body's block (.none) > stmts [exit "L"]
  -- Step 4: descend into the inner seq, then into the body's block,
  --         then through stmts_cons.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_seq_inner
          (StepStmtE.step_block_body StepStmtE.step_stmts_cons)))) ?_
  -- Step 5: fire the exit "L".
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_seq_inner
          (StepStmtE.step_block_body
            (StepStmtE.step_seq_inner StepStmtE.step_exit))))) ?_
  -- Step 6: step_seq_exit (inner-most seq propagates the exiting).
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_seq_inner
          (StepStmtE.step_block_body StepStmtE.step_seq_exit)))) ?_
  -- Step 7: body's `.block .none` mismatches "L" — propagate via step_block_exit_mismatch.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_seq_inner
          (StepStmtE.step_block_exit_mismatch (by intro h; cases h))))) ?_
  -- Step 8-9: propagate exiting through outer seq layers.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner StepStmtE.step_seq_exit)) ?_
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body StepStmtE.step_seq_exit) ?_
  -- Step 10: outer block "L" matches the exit label.
  -- The store projection equals ρ₀.store since no inits happened.
  have hproj : projectStore (P := MiniPureExpr) ρ₀.store ρ₀.store = ρ₀.store := by
    funext x
    simp only [projectStore, ite_eq_left_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]
    intro h; rfl
  conv => rhs; rw [show ρ₀ = { ρ₀ with store := projectStore ρ₀.store ρ₀.store } from by
    simp [hproj]]
  exact .step _ [] _ [] _ (StepStmtE.step_block_exit_match rfl) (.refl _)

---------------------------------------------------------------------

/-! ## Test: `block L { if tt then { exit } else { skip } }` terminates
    with the exit caught by the outer block via the then-branch. -/

def progIteThen : Stmt MiniPureExpr CmdT :=
  .block "L"
    [.ite (.det .tt) [.exit "L" .empty] [] .empty]
    .empty

/-- The test: `.stmt progIteThen ρ₀ →* .terminal ρ₀` via the `then` branch. -/
theorem progIteThenReachesTerminal :
    StepStmtStarE MiniPureExpr noCmd
      (.stmt progIteThen ρ₀) [] (.terminal ρ₀) := by
  have htt : MiniPureExpr.eval () ρ₀.store HasBool.tt = some (HasBool.ttVal ()) := rfl
  refine .step _ [] _ [] _ StepStmtE.step_block ?_
  refine .step _ [] _ [] _ (StepStmtE.step_block_body StepStmtE.step_stmts_cons) ?_
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner (StepStmtE.step_ite_true htt))) ?_
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner (StepStmtE.step_block_body StepStmtE.step_stmts_cons))) ?_
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_block_body (StepStmtE.step_seq_inner StepStmtE.step_exit)))) ?_
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_block_body StepStmtE.step_seq_exit))) ?_
  -- Inner anonymous block (.none) propagates exit "L" via mismatch.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner (StepStmtE.step_block_exit_mismatch (by simp)))) ?_
  refine .step _ [] _ [] _ (StepStmtE.step_block_body StepStmtE.step_seq_exit) ?_
  -- Outer block "L" matches the labeled exit; project store (identity here).
  have hproj : projectStore (P := MiniPureExpr) ρ₀.store ρ₀.store = ρ₀.store := by
    funext x; simp only [projectStore, ite_eq_left_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]; intro _; rfl
  conv => rhs; rw [show ρ₀ = { ρ₀ with store := projectStore ρ₀.store ρ₀.store } from by
    simp [hproj]]
  exact .step _ [] _ [] _ (StepStmtE.step_block_exit_match rfl) (.refl _)

---------------------------------------------------------------------

/-! ## Test: `block L { if ff then { skip } else { exit } }` terminates
    with the exit caught by the outer block via the else-branch. -/

def progIteElse : Stmt MiniPureExpr CmdT :=
  .block "L"
    [.ite (.det .ff) [] [.exit "L" .empty] .empty]
    .empty

/-- The test: `.stmt progIteElse ρ₀ →* .terminal ρ₀` via the `else` branch. -/
theorem progIteElseReachesTerminal :
    StepStmtStarE MiniPureExpr noCmd
      (.stmt progIteElse ρ₀) [] (.terminal ρ₀) := by
  have hff : MiniPureExpr.eval () ρ₀.store HasBool.ff = some (HasBool.ffVal ()) := rfl
  refine .step _ [] _ [] _ StepStmtE.step_block ?rest1
  refine .step _ [] _ [] _ (StepStmtE.step_block_body StepStmtE.step_stmts_cons) ?rest2
  -- step_ite_false — take the else branch.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner (StepStmtE.step_ite_false hff))) ?rest3
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner (StepStmtE.step_block_body StepStmtE.step_stmts_cons))) ?rest4
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_block_body (StepStmtE.step_seq_inner StepStmtE.step_exit)))) ?rest5
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_block_body StepStmtE.step_seq_exit))) ?rest6
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner (StepStmtE.step_block_exit_mismatch (by simp)))) ?rest7
  refine .step _ [] _ [] _ (StepStmtE.step_block_body StepStmtE.step_seq_exit) ?rest8
  -- Outer block "L" matches the labeled exit; project store (identity here).
  have hproj : projectStore (P := MiniPureExpr) ρ₀.store ρ₀.store = ρ₀.store := by
    funext x; simp only [projectStore, ite_eq_left_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]; intro _; rfl
  conv => rhs; rw [show ρ₀ = { ρ₀ with store := projectStore ρ₀.store ρ₀.store } from by
    simp [hproj]]
  exact .step _ [] _ [] _ (StepStmtE.step_block_exit_match rfl) (.refl _)

---------------------------------------------------------------------

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
    Factory := Unit,
    Val := Expr2,
    eval := fun _f σ e => match e with
      | .var x => σ x
      | _ => some e }

/-- Get free variables from `Expr2`. -/
def Expr2.getVars : Expr2 → List String
  | .var n => [n]
  | .not e => e.getVars
  | _ => []

instance : HasFvars MiniPureExpr2 where
  getFvars := Expr2.getVars
  getTypedFvars _ := []

/-- Values are the variable-free expressions. -/
instance : HasVal MiniPureExpr2 where
  value _ e := e.getVars = []
  valueOfTy _ e _ := e.getVars = []

instance : LawfulHasVal MiniPureExpr2 where
  valueOfTy_isVal := fun _ _ _ h => h
  valueOfTy_congr := fun _ _ _ _ _ _ _ h => h

instance : HasBool MiniPureExpr2 where
  tt := .tt
  ff := .ff
  tt_is_not_ff := by intro h; cases h
  boolTy := .Bool
  ttVal _ := .tt
  ffVal _ := .ff
  ttVal_ne_ffVal _ := by intro h; cases h
  boolIsValOfTy := fun _ => ⟨rfl, rfl⟩

instance : HasBoolOps MiniPureExpr2 where
  not := .not
  and := fun _ _ => .tt
  imp := fun _ _ => .tt

/-- Test: `set x := var "y"` has `modifiedOrDefinedVars = ["x"]` (write-set only)
    but `touchedVars = ["x", "y"]` (includes the read variable "y"). -/
example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.set (P := MiniPureExpr2) "x" (.det (.var "y")) .empty)).modifiedOrDefinedVars false
    =["x"] := by native_decide

example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.set (P := MiniPureExpr2) "x" (.det (.var "y")) .empty)).touchedVars
    = ["x", "y"] := by native_decide

/-- Test: `init z : Bool := var "w"` has `modifiedOrDefinedVars = ["z"]`
    but `touchedVars = ["z", "w"]`. -/
example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.init (P := MiniPureExpr2) "z" .Bool (.det (.var "w")) .empty)).modifiedOrDefinedVars false
    =["z"] := by native_decide

example : (Stmt.cmd (P := MiniPureExpr2)
    (Cmd.init (P := MiniPureExpr2) "z" .Bool (.det (.var "w")) .empty)).touchedVars
    = ["z", "w"] := by native_decide

/-- Test: Block touchedVars includes both read and write vars from all stmts. -/
example : (Block.touchedVars (P := MiniPureExpr2) (C := Cmd MiniPureExpr2)
    [.cmd (Cmd.init (P := MiniPureExpr2) "a" .Bool (.det (.var "b")) .empty),
     .cmd (Cmd.set (P := MiniPureExpr2) "c" (.det (.var "d")) .empty)])
    = ["c", "a", "b", "d"] := by native_decide

example : (Block.modifiedOrDefinedVars (P := MiniPureExpr2) (C := Cmd MiniPureExpr2)
    [.cmd (Cmd.init (P := MiniPureExpr2) "a" .Bool (.det (.var "b")) .empty),
     .cmd (Cmd.set (P := MiniPureExpr2) "c" (.det (.var "d")) .empty)] false)
    = ["c", "a"] := by native_decide

---------------------------------------------------------------------

/-! ## Block scoping tests

Verify that variables `init`'d inside a block are not visible after the
block exits. We step through a program and verify the terminal store
has `none` for block-local variables thanks to `projectStore`. -/

/-- A `HasFvar` instance for `MiniPureExpr` — needed by `EvalCmdE`. -/
instance : HasFvar MiniPureExpr where
  mkFvar _ := .tt  -- unused but required
  mkTypedFvar _ _ := .tt  -- unused but required
  getFvar _ := none   -- no expression is a free variable reference

/-- `WellFormedSemanticEvalVar` for `miniEval` — trivially holds since
    `getFvar` always returns `none`. -/
theorem miniEval_wfVar : WellFormedSemanticEvalVar (P := MiniPureExpr) () := by
  unfold WellFormedSemanticEvalVar
  intro e v σ _hwfs hfv
  simp [HasFvar.getFvar] at hfv

/-- The standard `EvalCmdE` for `Cmd MiniPureExpr`. -/
def stdEvalCmd : EvalCmdParamE MiniPureExpr (Cmd MiniPureExpr) (Event MiniPureExpr) :=
  EvalCmdE (P := MiniPureExpr)

/-- A store where "x" is defined (maps to `.tt`), everything else is `none`. -/
def storeWithX : SemanticStore MiniPureExpr :=
  fun v => if v == "x" then some .tt else none

/-- Env with "x" defined. -/
def ρ_x : Env MiniPureExpr :=
  { store := storeWithX, factory := () }

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
    StepStmtStarE MiniPureExpr stdEvalCmd
      (.stmt progBlockScope ρ_x) []
      (.terminal { store := storeWithX, factory := () }) := by
  -- Step 1: step_block — enter the block, saving ρ_x.store as σ_parent.
  refine .step _ [] _ [] _ StepStmtE.step_block ?_
  -- Step 2: step_block_body (step_stmts_cons) — process the singleton list.
  refine .step _ [] _ [] _ (StepStmtE.step_block_body StepStmtE.step_stmts_cons) ?_
  -- Step 3: step_block_body (step_seq_inner step_cmd) — evaluate `init y := tt`.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body
      (StepStmtE.step_seq_inner
        (StepStmtE.step_cmd
          (EvalCmdE.eval_init (P := MiniPureExpr)
            (show miniEval () storeWithX .tt = some .tt from rfl)
            (InitState.init
              (show storeWithX "y" = none from rfl)
              (show storeWithXY "y" = some .tt from rfl)
              storeWithXY_frame)
            (show HasVal.valueOfTy (P := MiniPureExpr) () .tt .Bool from trivial)
            miniEval_wfVar)))) ?_
  -- Step 4: step_block_body (step_seq_done) — seq is done, go to stmts [].
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body StepStmtE.step_seq_done) ?_
  -- Step 5: step_block_body (step_stmts_nil) — empty list becomes terminal.
  refine .step _ [] _ [] _
    (StepStmtE.step_block_body StepStmtE.step_stmts_nil) ?_
  -- Step 6: step_block_done — project store.
  have hproj : projectStore (P := MiniPureExpr) storeWithX storeWithXY = storeWithX := by
    ext v
    simp [projectStore, storeWithX, storeWithXY]
    split <;> simp_all
  conv => rhs; rw [show Env.mk storeWithX () =
    { (Env.mk storeWithXY ()) with store := projectStore storeWithX storeWithXY }
    from by simp [hproj]]
  exact .step _ [] _ [] _ StepStmtE.step_block_done (.refl _)

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
each iteration the init'd variable is projected away. -/

/-- Program: `loop (nondet) { init y := tt }`.
    The loop enters one iteration, inits y, then exits on the next iteration.
    The anonymous block wrapper projects "y" away. -/
def progLoopScope : Stmt MiniPureExpr (Cmd MiniPureExpr) :=
  .loop .nondet none [] [.cmd (.init "y" .Bool (.det .tt) .empty)] .empty

/-- After stepping the loop through one iteration and exiting, the final
    store should still be `storeWithX` (the variable "y" is projected away
    by the per-iteration anonymous block).  With the new semantics, each
    iteration's body runs in its own block scope. -/
theorem loopScopeTest :
    StepStmtStarE MiniPureExpr stdEvalCmd
      (.stmt progLoopScope ρ_x) []
      (.terminal { store := storeWithX, factory := () }) := by
  -- Step 1: step_loop_nondet_enter — produces:
  --   .seq (.block .none ρ_x.store (.stmts [init y] ρ_x')) [loop ...]
  refine .step _ [] _ [] _
    (StepStmtE.step_loop_nondet_enter) ?_
  -- Step 2: step_seq_inner (step_block_body step_stmts_cons)
  refine .step _ [] _ [] _
    (StepStmtE.step_seq_inner
      (StepStmtE.step_block_body StepStmtE.step_stmts_cons)) ?_
  -- Step 3: step_seq_inner (step_block_body (step_seq_inner step_cmd)) — init y
  refine .step _ [] _ [] _
    (StepStmtE.step_seq_inner
      (StepStmtE.step_block_body
        (StepStmtE.step_seq_inner
          (StepStmtE.step_cmd
            (EvalCmdE.eval_init (P := MiniPureExpr)
              (show miniEval () storeWithX .tt = some .tt from rfl)
              (InitState.init
                (show storeWithX "y" = none from rfl)
                (show storeWithXY "y" = some .tt from rfl)
                storeWithXY_frame)
              (show HasVal.valueOfTy (P := MiniPureExpr) () .tt .Bool from trivial)
              miniEval_wfVar))))) ?_
  -- Step 4: step_seq_inner (step_block_body step_seq_done) — inner stmt terminal
  refine .step _ [] _ [] _
    (StepStmtE.step_seq_inner
      (StepStmtE.step_block_body StepStmtE.step_seq_done)) ?_
  -- Step 5: step_seq_inner (step_block_body step_stmts_nil)
  refine .step _ [] _ [] _
    (StepStmtE.step_seq_inner
      (StepStmtE.step_block_body StepStmtE.step_stmts_nil)) ?_
  -- Step 6: step_seq_inner step_block_done — body's block projects, dropping "y"
  refine .step _ [] _ [] _
    (StepStmtE.step_seq_inner StepStmtE.step_block_done) ?_
  -- After projection, env's store is projectStore storeWithX storeWithXY = storeWithX
  have hproj : projectStore (P := MiniPureExpr) storeWithX storeWithXY = storeWithX := by
    funext v
    simp [projectStore, storeWithX, storeWithXY]
    split <;> simp_all
  -- Step 7: step_seq_done — seq advances with projected env to [loop ...]
  refine .step _ [] _ [] _ StepStmtE.step_seq_done ?_
  -- Step 8: step_stmts_cons
  refine .step _ [] _ [] _ StepStmtE.step_stmts_cons ?_
  -- Step 9: step_seq_inner step_loop_nondet_exit
  refine .step _ [] _ [] _
    (StepStmtE.step_seq_inner
      (StepStmtE.step_loop_nondet_exit)) ?_
  -- Step 10: step_seq_done
  refine .step _ [] _ [] _ StepStmtE.step_seq_done ?_
  -- Step 11: step_stmts_nil — final terminal
  -- The final env's store should be storeWithX after the projection.
  -- Need to reconcile the env shape.
  conv => rhs; rw [show Env.mk storeWithX () =
    Env.mk (projectStore storeWithX storeWithXY) () from by simp [hproj]]
  exact .step _ [] _ [] _ StepStmtE.step_stmts_nil (.refl _)

---------------------------------------------------------------------

/-! ## Test: re-init inside an if-branch gets stuck

`init x := tt; if tt { init x := ff }` gets stuck at the second `init x`
because `InitState` requires the variable to be undefined (`σ x = none`),
but after the first `init`, `x` is already `some .tt`.  This confirms that
block scoping is necessary to re-use a variable name. -/

def progReinitStuck : List (Stmt MiniPureExpr (Cmd MiniPureExpr)) :=
  [.cmd (.init "x" .Bool (.det .tt) .empty),
   .ite (.det .tt) [.cmd (.init "x" .Bool (.det .ff) .empty)] [] .empty]

/-- After executing `init x := tt`, the inner `init x := ff` cannot step
    because `InitState` requires `σ "x" = none` but `σ "x" = some .tt`.
    We show no single step is possible from this configuration. -/
theorem reinit_stuck :
    ¬ ∃ e c₂, StepStmtE MiniPureExpr stdEvalCmd
      (.stmt (.cmd (.init "x" .Bool (.det .ff) .empty)) ρ_x) e c₂ := by
  intro ⟨e, c₂, hstep⟩
  match hstep with
  | .step_cmd (.eval_init _ (.init h_none _ _) _ _) =>
    exact absurd h_none (by simp [ρ_x, storeWithX])

end StepStmtTest
end

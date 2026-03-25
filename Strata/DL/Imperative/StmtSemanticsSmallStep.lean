/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Imperative

public section

/-! ## Small-Step Operational Semantics for Statements

This module defines small-step operational semantics for the Imperative
dialect's statement constructs.

Key design decisions:
- `Config.seq` enables truly small-step processing of statement lists.
  Without it, `step_stmt_cons` required the first statement to reach
  terminal in a single step, which prevented blocks (multi-step) from
  being processed inside statement lists.
- `Config.block` holds an inner `Config` (not a statement list + store),
  allowing blocks to observe the execution state of their body at each step.
- `assert` is a skip in the operational semantics (`eval_assert` has no
  precondition). Assertion checking is handled by the verification framework,
  not by execution.
-/

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of:
- The current statement (or list of statements) being executed
- An execution environment (`Env`) bundling store, evaluator, and failure flag
-/
inductive Config (P : PureExpr) (CmdT : Type) : Type where
  /-- A single statement to execute next. -/
  | stmt : Stmt P CmdT → Env P → Config P CmdT
  /-- A list of statements to execute next, in order. -/
  | stmts : List (Stmt P CmdT) → Env P → Config P CmdT
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : Env P → Config P CmdT
  /-- An exiting configuration, indicating that an exit statement was encountered.
      The optional label identifies which block to exit to. -/
  | exiting : Option String → Env P → Config P CmdT
  /-- A block context: execute the inner config, then consume matching exits.
      The string is the block label. -/
  | block : String → Config P CmdT → Config P CmdT
  /-- A sequence context: execute the first statement (as a sub-config), then
      continue with the remaining statements. -/
  | seq : Config P CmdT → List (Stmt P CmdT) → Config P CmdT

/-! ## Single-step relation

`StepStmt` defines a single execution step from one configuration to another.
The expression evaluator is part of the `Env` and can be extended by
`funcDecl` statements.  The cumulative failure flag in `Env.hasFailure` is
OR-ed with the per-command failure flag at each `step_cmd`.
-/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P]

inductive StepStmt
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P) :
  Config P CmdT → Config P CmdT → Prop where

  /-- A command steps to terminal configuration if it evaluates successfully.
      Commands preserve the evaluator (ρ'.eval = ρ.eval).
      The per-command failure flag `hasAssertFailure` is OR-ed into
      `ρ.hasFailure` to produce the new environment's flag. -/
  | step_cmd :
    EvalCmd ρ.eval ρ.store c σ' hasAssertFailure →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.cmd c) ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure })

  /-- A labeled block steps to a block context that wraps its body as `.stmts`. -/
  | step_block :
    StepStmt EvalCmd extendEval
      (.stmt (.block label ss _) ρ)
      (.block label (.stmts ss ρ))

  /-- If the condition of an `ite` statement evaluates to true, step to the
      then branch. -/
  | step_ite_true :
    ρ.eval ρ.store c = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite c tss ess _) ρ)
      (.stmts tss ρ)

  /-- If the condition of an `ite` statement evaluates to false, step to the
      else branch. -/
  | step_ite_false :
    ρ.eval ρ.store c = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite c tss ess _) ρ)
      (.stmts ess ρ)

  /-- If a loop guard is true, execute the body (followed by the loop again). -/
  | step_loop_enter :
    ρ.eval ρ.store g = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop g m inv body md) ρ)
      (.stmts (body ++ [.loop g m inv body md]) ρ)

  /-- If a loop guard is false, terminate the loop. -/
  | step_loop_exit :
    ρ.eval ρ.store g = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop g m inv body _) ρ)
      (.terminal ρ)

  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
    StepStmt EvalCmd extendEval
      (.stmt (.exit label _) ρ)
      (.exiting label ρ)

  /-- A function declaration extends the evaluator with the new function. -/
  | step_funcDecl [HasSubstFvar P] [HasVarsPure P P.Expr] :
    StepStmt EvalCmd extendEval
      (.stmt (.funcDecl decl md) ρ)
      (.terminal { ρ with eval := extendEval ρ.eval ρ.store decl })

  /-- A type declaration is a no-op at runtime. -/
  | step_typeDecl :
    StepStmt EvalCmd extendEval
      (.stmt (.typeDecl _tc _md) ρ)
      (.terminal ρ)

  /-- An empty list of statements steps to `.terminal` with no state changes. -/
  | step_stmts_nil :
    StepStmt EvalCmd extendEval
      (.stmts [] ρ)
      (.terminal ρ)

  /-- To evaluate a non-empty sequence, enter a seq context that processes
      the first statement while remembering the remaining statements. -/
  | step_stmts_cons :
    StepStmt EvalCmd extendEval
      (.stmts (s :: ss) ρ)
      (.seq (.stmt s ρ) ss)

  /-- A seq context steps its inner config forward. -/
  | step_seq_inner :
    StepStmt EvalCmd extendEval inner inner' →
    ----
    StepStmt EvalCmd extendEval
      (.seq inner ss)
      (.seq inner' ss)

  /-- When the inner config of a seq reaches terminal, continue with the
      remaining statements. -/
  | step_seq_done :
    StepStmt EvalCmd extendEval
      (.seq (.terminal ρ') ss)
      (.stmts ss ρ')

  /-- When the inner config of a seq exits, propagate the exit
      (skip remaining statements). -/
  | step_seq_exit :
    StepStmt EvalCmd extendEval
      (.seq (.exiting label ρ') ss)
      (.exiting label ρ')

  /-- A block context steps its inner body one step forward.
      The inner body can be any config (stmts, seq, etc.). -/
  | step_block_body :
    StepStmt EvalCmd extendEval inner inner' →
    ----
    StepStmt EvalCmd extendEval
      (.block label inner)
      (.block label inner')

  /-- When a block's inner body reaches terminal, the block terminates. -/
  | step_block_done :
    StepStmt EvalCmd extendEval
      (.block label (.terminal ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with no label, the block consumes the exit. -/
  | step_block_exit_none :
    StepStmt EvalCmd extendEval
      (.block label (.exiting .none ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with a matching label, the block consumes it. -/
  | step_block_exit_match :
    l = label →
    ----
    StepStmt EvalCmd extendEval
      (.block label (.exiting (.some l) ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with a non-matching label, the exit propagates. -/
  | step_block_exit_mismatch :
    l ≠ label →
    ----
    StepStmt EvalCmd extendEval
      (.block label (.exiting (.some l) ρ'))
      (.exiting (.some l) ρ')

end

/-! ## Multi-step execution: reflexive transitive closure of single steps. -/

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)

abbrev StepStmtStar :
    Config P CmdT → Config P CmdT → Prop :=
  ReflTrans (StepStmt P EvalCmd extendEval)

/-- A statement evaluates successfully if it steps to a terminal configuration. -/
def EvalStmtSmall
    (ρ : Env P) (s : Stmt P CmdT)
    (ρ' : Env P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')

/-- A list of statements evaluates successfully if it steps to a terminal
    configuration. -/
def EvalStmtsSmall
    (ρ : Env P) (ss : List (Stmt P CmdT))
    (ρ' : Env P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.terminal ρ')

---------------------------------------------------------------------

/-! ## Basic Properties and Theorems -/

/-- Empty statement list evaluation. -/
theorem evalStmtsSmallNil
    (ρ : Env P) :
    EvalStmtsSmall P EvalCmd extendEval ρ [] ρ := by
  unfold EvalStmtsSmall
  exact .step _ _ _ StepStmt.step_stmts_nil (.refl _)

/-- Configuration is terminal if no further steps are possible. -/
def IsTerminal
    (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd extendEval c c'

/-- Terminal configurations are indeed terminal. -/
theorem terminalIsTerminal
    (ρ : Env P) :
    IsTerminal P EvalCmd extendEval (.terminal ρ) := by
  unfold IsTerminal
  intro c' h
  cases h

/-!
### Stepping through a statement list

When executing `.stmts (s :: ss) ρ`, the semantics first enters a
`.seq` context (via `step_stmts_cons`), executes `s` to terminal, then
resumes with `.stmts ss ρ'`.

The proof proceeds in two parts:
1. A helper lemma (`seq_inner_star`) showing that multi-step execution of
   the inner config lifts to multi-step execution of the enclosing `.seq`.
2. The main theorem (`stmts_cons_step`) composing the pieces.
-/

/-- Transitivity of `ReflTrans`: if `r* x y` and `r* y z` then `r* x z`.
    This is a local helper that avoids the opaque `Transitive` wrapper
    from `Relations.lean` (which becomes opaque across module boundaries). -/
private theorem reflTrans_trans {r : Relation A}
    {x y z : A} (h1 : ReflTrans r x y) (h2 : ReflTrans r y z) :
    ReflTrans r x z := by
  induction h1 with
  | refl => exact h2
  | step _ mid _ hstep _ ih => exact .step _ mid _ hstep (ih h2)

/-- Helper: if the inner config of a `.seq` takes multiple steps, the
    enclosing `.seq` takes the same number of steps.
    Proved by induction on the multi-step derivation. -/
theorem seq_inner_star
    (inner inner' : Config P CmdT)
    (ss : List (Stmt P CmdT))
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval
      (.seq inner ss)
      (.seq inner' ss) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih =>
    exact .step _ _ _ (.step_seq_inner hstep) ih

/-- When executing `.stmts (s :: ss) ρ`, if the head statement `s`
    multi-steps to `.terminal ρ'`, then the whole list multi-steps to
    `.stmts ss ρ'`.

    This captures the fundamental sequencing behaviour of statement lists
    in the small-step semantics. -/
theorem stmts_cons_step
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT))
    (ρ ρ' : Env P)
    (hstmt : StepStmtStar P EvalCmd extendEval
      (.stmt s ρ) (.terminal ρ')) :
    StepStmtStar P EvalCmd extendEval
      (.stmts (s :: ss) ρ)
      (.stmts ss ρ') := by
  -- Step 1: .stmts (s :: ss) ρ  →  .seq (.stmt s ρ) ss
  --         via step_stmts_cons
  apply ReflTrans.step _ (.seq (.stmt s ρ) ss)
  · exact .step_stmts_cons
  -- Step 2: .seq (.stmt s ρ) ss  →*  .seq (.terminal ρ') ss
  --         by lifting hstmt through the seq context
  have h2 := seq_inner_star P EvalCmd extendEval _ _ ss hstmt
  -- Step 3: .seq (.terminal ρ') ss  →  .stmts ss ρ'
  --         via step_seq_done, then chain with h2 by induction
  suffices h3 : StepStmtStar P EvalCmd extendEval
      (.seq (.terminal ρ') ss) (.stmts ss ρ') from
    reflTrans_trans h2 h3
  exact .step _ _ _ .step_seq_done (.refl _)

end -- section

end -- public section
end Imperative

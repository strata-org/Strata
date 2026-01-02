/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Imperative

/-! ## Small-Step Operational Semantics for Statements

This module defines small-step operational semantics for the Imperative
dialect's statement constructs.
-/

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of:
- The current statement (or list of statements) being executed
- The current store
-/
inductive Config (P : PureExpr) (CmdT : Type) : Type where
  /-- A single statement to execute next. -/
  | stmt : Stmt P CmdT → SemanticStore P → Config P CmdT
  /-- A list of statements to execute next, in order. -/
  | stmts : List (Stmt P CmdT) → SemanticStore P → Config P CmdT
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : SemanticStore P → Config P CmdT

/--
Small-step operational semantics for statements. The relation `StepStmt`
defines a single execution step from one configuration to another.
-/
inductive StepStmt
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Config P CmdT → Config P CmdT → Prop where

  /-- A command steps to terminal configuration if it evaluates successfully -/
  | step_cmd :
    EvalCmd δ σ c σ' →
    ----
    StepStmt P EvalCmd δ σ
      (.stmt (.cmd c) σ)
      (.terminal σ')

  /-- A labeled block steps to its statement list. -/
  | step_block :
    StepStmt P EvalCmd δ σ
      (.stmt (.block _ ss _) σ)
      (.stmts ss σ)

  /-- If the condition of an `ite` statement evaluates to true, step to the then
  branch. -/
  | step_ite_true :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ
      (.stmt (.ite c tss ess _) σ)
      (.stmts tss σ)

  /-- If the condition of an `ite` statement evaluates to false, step to the else
  branch. -/
  | step_ite_false :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ
      (.stmt (.ite c tss ess _) σ)
      (.stmts ess σ)

  /-- If a loop guard is true, execute the body and then loop again. -/
  | step_loop_enter :
    δ σ g = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ
      (.stmt (.loop g m inv body md) σ)
      (.stmts (body ++ [.loop g m inv body md]) σ)

  /-- If a loop guard is false, terminate the loop. -/
  | step_loop_exit :
    δ σ g = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ
      (.stmt (.loop g m inv body _) σ)
      (.terminal σ)

  /- Goto: not implemented, because we plan to remove it. -/

  /-- An empty list of statements steps to `.terminal` with no state changes. -/
  | step_stmts_nil :
    StepStmt P EvalCmd δ σ
      (.stmts [] σ)
      (.terminal σ)

  /-- To evaluate a sequence of statements, evaluate the first statement and
  then evaluate the remaining statements in the resulting state. -/
  | step_stmt_cons :
    StepStmt P EvalCmd δ σ (.stmt s σ) (.terminal σ') →
    ----
    StepStmt P EvalCmd δ σ
      (.stmts (s :: ss) σ)
      (.stmts ss σ')

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
def StepStmtStar
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Config P CmdT → Config P CmdT → Prop := fun δ σ => ReflTrans (StepStmt P EvalCmd δ σ)

/-- A statement evaluates successfully if it can step to a terminal
configuration.
-/
def EvalStmtSmall
  {CmdT : Type}
  (P : PureExpr)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (s : Stmt P CmdT)
  (σ' : SemanticStore P) : Prop :=
  StepStmtStar P EvalCmd δ σ (.stmt s σ) (.terminal σ')

/-- A list of statements evaluates successfully if it can step to a terminal
configuration.
-/
def EvalStmtsSmall
  (P : PureExpr)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (ss : List (Stmt P CmdT))
  (σ' : SemanticStore P) : Prop :=
  StepStmtStar P EvalCmd δ σ (.stmts ss σ) (.terminal σ')

---------------------------------------------------------------------

/-! ## Basic Properties and Theorems -/

/--
Empty statement list evaluation.
-/
theorem evalStmtsSmallNil
  (P : PureExpr)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (EvalCmd : EvalCmdParam P CmdT) :
  EvalStmtsSmall P EvalCmd δ σ [] σ := by
    unfold EvalStmtsSmall
    apply ReflTrans.step
    · exact StepStmt.step_stmts_nil
    · apply ReflTrans.refl

/--
Configuration is terminal if no further steps are possible.
-/
def IsTerminal
  {CmdT : Type}
  (P : PureExpr)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (EvalCmd : EvalCmdParam P CmdT)
  (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd δ σ c c'

/--
Terminal configurations are indeed terminal.
-/
theorem terminalIsTerminal
  {CmdT : Type}
  (P : PureExpr)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (σ : SemanticStore P)
  (δ : SemanticEval P)
  (EvalCmd : EvalCmdParam P CmdT) :
  IsTerminal P δ σ EvalCmd (.terminal σ) := by
  intro c' h
  cases h

end Imperative

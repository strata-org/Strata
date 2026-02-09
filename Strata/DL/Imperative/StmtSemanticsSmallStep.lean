/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
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
- The current expression evaluator (threaded to support funcDecl)
-/
inductive Config (P : PureExpr) (CmdT : Type) : Type where
  /-- A single statement to execute next. -/
  | stmt : Stmt P CmdT → SemanticStore P → SemanticEval P → Config P CmdT
  /-- A list of statements to execute next, in order. -/
  | stmts : List (Stmt P CmdT) → SemanticStore P → SemanticEval P → Config P CmdT
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : SemanticStore P → SemanticEval P → Config P CmdT

/--
Small-step operational semantics for statements. The relation `StepStmt`
defines a single execution step from one configuration to another.
The expression evaluator is part of the configuration and can be extended
by funcDecl statements.
-/
inductive StepStmt
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  Config P CmdT → Config P CmdT → Prop where

  /-- A command steps to terminal configuration if it evaluates successfully.
      Commands preserve the evaluator (δ' = δ). -/
  | step_cmd :
    EvalCmd δ σ c σ' →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.cmd c) σ δ)
      (.terminal σ' δ)

  /-- A labeled block steps to its statement list. -/
  | step_block :
    StepStmt P EvalCmd extendEval
      (.stmt (.block _ ss _) σ δ)
      (.stmts ss σ δ)

  /-- If the condition of an `ite` statement evaluates to true, step to the then
  branch. -/
  | step_ite_true :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.ite c tss ess _) σ δ)
      (.stmts tss σ δ)

  /-- If the condition of an `ite` statement evaluates to false, step to the else
  branch. -/
  | step_ite_false :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.ite c tss ess _) σ δ)
      (.stmts ess σ δ)

  /-- If a loop guard is true, execute the body and then loop again. -/
  | step_loop_enter :
    δ σ g = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.loop g m inv body md) σ δ)
      (.stmts (body ++ [.loop g m inv body md]) σ δ)

  /-- If a loop guard is false, terminate the loop. -/
  | step_loop_exit :
    δ σ g = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.loop g m inv body _) σ δ)
      (.terminal σ δ)

  /- Goto: not implemented, because we plan to remove it. -/

  /-- A function declaration extends the evaluator with the new function. -/
  | step_funcDecl [HasSubstFvar P] [HasVarsPure P P.Expr] :
    StepStmt P EvalCmd extendEval
      (.stmt (.funcDecl decl md) σ δ)
      (.terminal σ (extendEval δ σ decl))

  /-- An empty list of statements steps to `.terminal` with no state changes. -/
  | step_stmts_nil :
    StepStmt P EvalCmd extendEval
      (.stmts [] σ δ)
      (.terminal σ δ)

  /-- To evaluate a sequence of statements, evaluate the first statement and
  then evaluate the remaining statements in the resulting state. -/
  | step_stmt_cons :
    StepStmt P EvalCmd extendEval (.stmt s σ δ) (.terminal σ' δ') →
    ----
    StepStmt P EvalCmd extendEval
      (.stmts (s :: ss) σ δ)
      (.stmts ss σ' δ')

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
def StepStmtStar
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  Config P CmdT → Config P CmdT → Prop := ReflTrans (StepStmt P EvalCmd extendEval)

/-- A statement evaluates successfully if it can step to a terminal
configuration.
-/
def EvalStmtSmall
  {CmdT : Type}
  (P : PureExpr)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (s : Stmt P CmdT)
  (σ' : SemanticStore P)
  (δ' : SemanticEval P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmt s σ δ) (.terminal σ' δ')

/-- A list of statements evaluates successfully if it can step to a terminal
configuration.
-/
def EvalStmtsSmall
  (P : PureExpr)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (ss : List (Stmt P CmdT))
  (σ' : SemanticStore P)
  (δ' : SemanticEval P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmts ss σ δ) (.terminal σ' δ')

---------------------------------------------------------------------

/-! ## Basic Properties and Theorems -/

/--
Empty statement list evaluation.
-/
theorem evalStmtsSmallNil
  (P : PureExpr)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (δ : SemanticEval P)
  (σ : SemanticStore P)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P) :
  EvalStmtsSmall P EvalCmd extendEval δ σ [] σ δ := by
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
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd extendEval c c'

/--
Terminal configurations are indeed terminal.
-/
theorem terminalIsTerminal
  {CmdT : Type}
  (P : PureExpr)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (σ : SemanticStore P)
  (δ : SemanticEval P)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P) :
  IsTerminal P EvalCmd extendEval (.terminal σ δ) := by
  unfold IsTerminal
  intro c' h
  cases h

end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics

---------------------------------------------------------------------

namespace Imperative

/-! ## Small-Step Operational Semantics for Statements

This module defines small-step operational semantics for the Imperative
dialect's statement constructs.
-/

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of:
- The current statement being executed
- The current store
-/
inductive Config (P : PureExpr) (CmdT : Type) : Type where
  | stmt : Stmt P CmdT → SemanticStore P → Config P CmdT
  | stmts : List (Stmt P CmdT) → SemanticStore P → Config P CmdT
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

  /-- Command: a command steps to terminal configuration if it
  evaluates successfully -/
  | step_cmd :
    EvalCmd δ σ₀ σ c σ' →
    ----
    StepStmt P EvalCmd δ σ₀
      (.stmt (.cmd c) σ₀)
      (.terminal σ')

  /-- Block: a labeled block steps to its statement list -/
  | step_block :
    StepStmt P EvalCmd δ σ₀
      (.stmt (.block _ ⟨ss⟩ _) σ)
      (.stmts ss σ)

  /-- Conditional (true): if condition evaluates to true, step to then-branch -/
  | step_ite_true :
    δ σ₀ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ₀
      (.stmt (.ite c ⟨tss⟩ ⟨ess⟩ _) σ)
      (.stmts tss σ)

  /-- Conditional (false): if condition evaluates to false, step to else-branch -/
  | step_ite_false :
    δ σ₀ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ₀
      (.stmt (.ite c ⟨tss⟩ ⟨ess⟩ _) σ)
      (.stmts ess σ)

  /-- Loop (guard true): if guard is true, execute body then loop again -/
  | step_loop_enter :
    δ σ₀ σ g = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ₀
      (.stmt (.loop g m inv ⟨body⟩ md) σ)
      (.stmts (body ++ [.loop g m inv ⟨body⟩ md]) σ)

  /-- Loop (guard false): if guard is false, terminate the loop -/
  | step_loop_exit :
    δ σ₀ σ g = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd δ σ₀
      (.stmt (.loop g m inv ⟨body⟩ _) σ)
      (.terminal σ)

  /- Goto: not implemented, because we plan to remove it. -/

  /-- Empty statement list: no statements left to execute -/
  | step_stmts_nil :
    StepStmt P EvalCmd δ σ₀
      (.stmts [] σ)
      (.terminal σ)

  /-- Statement composition: after executing a statement, continue with
  remaining statements -/
  | step_stmt_cons :
    StepStmt P EvalCmd δ σ₀ (.stmt s σ) (.terminal σ') →
    ----
    StepStmt P EvalCmd δ σ₀
      (.stmts (s :: ss) σ)
      (.stmts ss σ')

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
inductive StepStmtStar
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Config P CmdT → Config P CmdT → Prop where
  | refl :
    StepStmtStar P EvalCmd δ σ₀ c c
  | step :
    StepStmt P EvalCmd δ σ₀ c₁ c₂ →
    StepStmtStar P EvalCmd δ σ₀ c₂ c₃ →
    StepStmtStar P EvalCmd δ σ₀ c₁ c₃

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
  (σ₀ σ : SemanticStore P)
  (s : Stmt P CmdT)
  (σ' : SemanticStore P) : Prop :=
  StepStmtStar P EvalCmd δ σ₀ (.stmt s σ) (.terminal σ')

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
  (σ₀ σ : SemanticStore P)
  (ss : List (Stmt P CmdT))
  (σ' : SemanticStore P) : Prop :=
  StepStmtStar P EvalCmd δ σ₀ (.stmts ss σ) (.terminal σ')

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
  (σ₀ σ : SemanticStore P)
  (EvalCmd : EvalCmdParam P CmdT) :
  EvalStmtsSmall P EvalCmd δ σ₀ σ [] σ := by
    unfold EvalStmtsSmall
    apply StepStmtStar.step
    · exact StepStmt.step_stmts_nil
    · exact StepStmtStar.refl

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
  (σ₀ : SemanticStore P)
  (EvalCmd : EvalCmdParam P CmdT)
  (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd δ σ₀ c c'

/--
Terminal configurations are indeed terminal.
-/
theorem terminalIsTerminal
  {CmdT : Type}
  (P : PureExpr)
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (σ σ₀ : SemanticStore P)
  (δ : SemanticEval P)
  (EvalCmd : EvalCmdParam P CmdT) :
  IsTerminal P δ σ₀ EvalCmd (.terminal σ) := by
  intro c' h
  cases h

end Imperative

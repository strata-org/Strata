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
- The current store (for current variable values)
- The initial store (for two-state expressions)
-/
inductive Config (P : PureExpr) : Type where
  | stmt : Stmt P (Cmd P) → SemanticStore P → SemanticStore P → Config P
  | stmts : List (Stmt P (Cmd P)) → SemanticStore P → SemanticStore P → Config P
  | terminal : SemanticStore P → SemanticStore P → Config P

/--
Small-step operational semantics for statements. The relation `StepStmt`
defines a single execution step from one configuration to another.
-/
inductive StepStmt (P : PureExpr)
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  SemanticEval P → Config P → Config P → Prop where

  /-- Command: a command steps to terminal configuration if it
  evaluates successfully -/
  | step_cmd :
    EvalCmd P δ σ₀ σ c σ' →
    isDefinedOver (HasVarsImp.modifiedVars) σ c → -- TODO: needed?
    ----
    StepStmt P δ
      (.stmt (.cmd c) σ σ₀)
      (.terminal σ' σ₀)

  /-- Block: a labeled block steps to its statement list -/
  | step_block :
    StepStmt P δ
      (.stmt (.block _ ⟨ss⟩ _) σ σ₀)
      (.stmts ss σ σ₀)

  /-- Conditional (true): if condition evaluates to true, step to then-branch -/
  | step_ite_true :
    δ σ₀ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P δ
      (.stmt (.ite c ⟨tss⟩ ⟨ess⟩ _) σ σ₀)
      (.stmts tss σ σ₀)

  /-- Conditional (false): if condition evaluates to false, step to else-branch -/
  | step_ite_false :
    δ σ₀ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P δ
      (.stmt (.ite c ⟨tss⟩ ⟨ess⟩ _) σ σ₀)
      (.stmts ess σ σ₀)

  /-- Loop (guard true): if guard is true, execute body then loop again -/
  | step_loop_enter :
    δ σ₀ σ g = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P δ
      (.stmt (.loop g m inv ⟨body⟩ md) σ σ₀)
      (.stmts (body ++ [.loop g m inv ⟨body⟩ md]) σ σ₀)

  /-- Loop (guard false): if guard is false, terminate the loop -/
  | step_loop_exit :
    δ σ₀ σ g = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P δ
      (.stmt (.loop g m inv ⟨body⟩ _) σ σ₀)
      (.terminal σ σ₀)

  /- Goto: not implemented, because we plan to remove it. -/

  /-- Empty statement list: no statements left to execute -/
  | step_stmts_nil :
    StepStmt P δ
      (.stmts [] σ σ₀)
      (.terminal σ σ₀)

  /-- Non-empty statement list: execute first statement -/
  | step_stmts_cons :
    StepStmt P δ
      (.stmts (s :: ss) σ σ₀)
      (.stmt s σ σ₀)

  /-- Statement composition: after executing a statement, continue with
  remaining statements -/
  | step_stmt_continue :
    StepStmt P δ (.stmt s σ σ₀) (.terminal σ' σ₀) →
    ----
    StepStmt P δ
      (.stmts (s :: ss) σ σ₀)
      (.stmts ss σ' σ₀)

/--
Multi-step execution: reflexive transitive closure of single steps.
-/
inductive StepStmtStar (P : PureExpr)
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  SemanticEval P → Config P → Config P → Prop where
  | refl :
    StepStmtStar P δ c c
  | step :
    StepStmt P δ c₁ c₂ →
    StepStmtStar P δ c₂ c₃ →
    StepStmtStar P δ c₁ c₃

/-- A statement evaluates successfully if it can step to a terminal
configuration.
-/
def EvalStmtSmall (P : PureExpr)
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (δ : SemanticEval P)
  (σ₀ σ : SemanticStore P)
  (s : Stmt P (Cmd P))
  (σ' : SemanticStore P) : Prop :=
  StepStmtStar P δ (.stmt s σ σ₀) (.terminal σ' σ₀)

/-- A list of statements evaluates successfully if it can step to a terminal
configuration.
-/
def EvalStmtsSmall (P : PureExpr)
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (δ : SemanticEval P)
  (σ₀ σ : SemanticStore P)
  (ss : List (Stmt P (Cmd P)))
  (σ' : SemanticStore P) : Prop :=
  StepStmtStar P δ (.stmts ss σ σ₀) (.terminal σ' σ₀)

---------------------------------------------------------------------

/-! ## Basic Properties and Theorems -/

/--
Empty statement list evaluation.
-/
theorem evalStmtsSmallNil
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  EvalStmtsSmall P δ σ₀ σ [] σ := by
    unfold EvalStmtsSmall
    apply StepStmtStar.step
    · exact StepStmt.step_stmts_nil
    · exact StepStmtStar.refl

/--
Configuration is terminal if no further steps are possible.
-/
def IsTerminal (P : PureExpr)
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (δ : SemanticEval P) (c : Config P) : Prop :=
  ∀ c', ¬ StepStmt P δ c c'

/--
Terminal configurations are indeed terminal.
-/
theorem terminalIsTerminal
  [HasVarsImp P (List (Stmt P (Cmd P)))]
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  IsTerminal P δ (.terminal σ σ₀) := by
  intro c' h
  cases h

end Imperative

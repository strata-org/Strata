/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics

namespace Imperative

public section

/-! ## Generic small-step evaluator

`RunConfig` mirrors `Config` but is parameterized by a generic state type `S`
instead of `Env P`, so that concrete interpreters (e.g. Core) can thread their
own rich environment through the stepper.
-/

/-- Configuration for the generic stepper, parameterized by state `S`. -/
inductive RunConfig (P : PureExpr) (CmdT : Type) (S : Type) where
  | stmt   : Stmt P CmdT → S → RunConfig P CmdT S
  | stmts  : List (Stmt P CmdT) → S → RunConfig P CmdT S
  | terminal : S → RunConfig P CmdT S
  | exiting  : Option String → S → RunConfig P CmdT S
  | block  : String → RunConfig P CmdT S → RunConfig P CmdT S
  | seq    : RunConfig P CmdT S → List (Stmt P CmdT) → RunConfig P CmdT S

/-- Operations the stepper needs from the state. -/
structure RunOps (P : PureExpr) (CmdT : Type) (S : Type) where
  /-- Evaluate a expression to a value. -/
  evalExpr : S → P.Expr → Option P.Expr
  /-- Execute a command, producing a new state. -/
  evalCmd : S → CmdT → S
  /-- Extend the evaluator with a function declaration. -/
  extendEval : S → PureFunc P → S
  /-- Push a new variable scope (for blocks). -/
  pushScope : S → S := id
  /-- Pop a variable scope (for blocks). -/
  popScope : S → S := id
  /-- Produce a new state with an error -/
  addError : S → String -> S
  /-- Check if the state has an error (to short-circuit execution). -/
  hasError : S → Bool := fun _ => false

def runStep [BEq P.Expr] [HasBool P]
    (ops : RunOps P CmdT S)
    (c : RunConfig P CmdT S) : RunConfig P CmdT S :=
  match c with
  | .terminal _ => c
  | .exiting _ _ => c

  | .stmt (.cmd cmd) ρ => .terminal (ops.evalCmd ρ cmd)

  | .stmt (.block label ss _) ρ => .block label (.stmts ss (ops.pushScope ρ))

  | .stmt (.ite cond tss ess _) ρ =>
    match cond with
    | .nondet => .stmts tss ρ
    | .det e =>
      match ops.evalExpr ρ e with
      | some v =>
        if HasBool.isTrue v then .stmts tss ρ
        else .stmts ess ρ
      | none => .terminal (ops.addError ρ "ITE condition did not reduce to bool")

  | .stmt s@(.loop guard _ _ body _) ρ =>
    match guard with
    | .nondet => .terminal ρ
    | .det g =>
      match ops.evalExpr ρ g with
      | some v =>
        if HasBool.isTrue v then .stmts (body ++ [s]) ρ
        else .terminal ρ
      | none => .terminal (ops.addError ρ "Loop guard did not reduce to bool")

  | .stmt (.exit label _) ρ => .exiting label ρ

  | .stmt (.funcDecl decl _) ρ => .terminal (ops.extendEval ρ decl)

  | .stmt (.typeDecl _ _) ρ => .terminal ρ

  | .stmts [] ρ => .terminal ρ

  | .stmts (s :: ss) ρ =>
    if ops.hasError ρ then .terminal ρ
    else .seq (.stmt s ρ) ss

  | .seq inner ss =>
    match inner with
    | .terminal ρ' => .stmts ss ρ'
    | .exiting label ρ' => .exiting label ρ'
    | _ => .seq (runStep ops inner) ss

  | .block label inner =>
    match inner with
    | .terminal ρ' => .terminal (ops.popScope ρ')
    | .exiting .none ρ' => .terminal (ops.popScope ρ')
    | .exiting (.some l) ρ' =>
      if l == label then .terminal (ops.popScope ρ')
      else .exiting (.some l) (ops.popScope ρ')
    | _ => .block label (runStep ops inner)

def runStmt [BEq P.Expr] [HasBool P]
    (ops : RunOps P CmdT S)
    (fuel : Nat)
    (c : RunConfig P CmdT S) : RunConfig P CmdT S :=
  match c with
  | .terminal _ => c
  | _ =>
    match fuel with
    | 0 => c
    | fuel + 1 => runStmt ops fuel (runStep ops c)

end -- public section
end Imperative

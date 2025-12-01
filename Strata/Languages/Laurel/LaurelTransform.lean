/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Laurel

---------------------------------------------------------------------
namespace Laurel

/- Translating concrete Laurel syntax into abstract Laurel syntax -/

open Laurel
open Std (ToFormat Format format)
open Strata (QualifiedIdent Arg)

---------------------------------------------------------------------

/- Translation Monad -/

structure TransState where
  errors : Array String

def TransM := StateM TransState
  deriving Monad

def TransM.run (m : TransM α) : (α × Array String) :=
  let (v, s) := StateT.run m { errors := #[] }
  (v, s.errors)

def TransM.error [Inhabited α] (msg : String) : TransM α := do
  modify fun s => { errors := s.errors.push msg }
  return panic msg

---------------------------------------------------------------------

def checkOp (op : Strata.Operation) (name : QualifiedIdent) (argc : Nat) :
  TransM Unit := do
  if op.name != name then
    TransM.error s!"Op name mismatch! \n\
                   Name: {repr name}\n\
                   Op: {repr op}"
  if op.args.size != argc then
    TransM.error s!"Op arg count mismatch! \n\
                   Expected: {argc}\n\
                   Got: {op.args.size}\n\
                   Op: {repr op}"
  return ()

def translateIdent (arg : Arg) : TransM Identifier := do
  let .ident _ id := arg
    | TransM.error s!"translateIdent expects ident"
  return id

def translateBool (arg : Arg) : TransM Bool := do
  match arg with
  | .op op =>
    if op.name == q`Laurel.boolTrue then
      return true
    else if op.name == q`Laurel.boolFalse then
      return false
    else
      TransM.error s!"translateBool expects boolTrue or boolFalse"
  | _ => TransM.error s!"translateBool expects operation"

---------------------------------------------------------------------

mutual

partial def translateStmtExpr (arg : Arg) : TransM StmtExpr := do
  match arg with
  | .op op =>
    if op.name == q`Laurel.assert then
      let cond ← translateStmtExpr op.args[0]!
      return .Assert cond
    else if op.name == q`Laurel.assume then
      let cond ← translateStmtExpr op.args[0]!
      return .Assume cond
    else if op.name == q`Laurel.block then
      let stmts ← translateSeqCommand op.args[0]!
      return .Block stmts none
    else if op.name == q`Laurel.boolTrue then
      return .LiteralBool true
    else if op.name == q`Laurel.boolFalse then
      return .LiteralBool false
    else
      TransM.error s!"Unknown operation: {op.name}"
  | _ => TransM.error s!"translateStmtExpr expects operation"

partial def translateSeqCommand (arg : Arg) : TransM (List StmtExpr) := do
  let .seq _ args := arg
    | TransM.error s!"translateSeqCommand expects seq"
  let mut stmts : List StmtExpr := []
  for arg in args do
    let stmt ← translateStmtExpr arg
    stmts := stmts ++ [stmt]
  return stmts

partial def translateCommand (arg : Arg) : TransM StmtExpr := do
  translateStmtExpr arg

end

def translateProcedure (arg : Arg) : TransM Procedure := do
  let .op op := arg
    | TransM.error s!"translateProcedure expects operation"
  checkOp op q`LaurelMinimal.procedure 2
  let name ← translateIdent op.args[0]!
  let body ← translateCommand op.args[1]!
  return {
    name := name
    inputs := []
    output := .TVoid
    precondition := .LiteralBool true
    decreases := .LiteralBool true
    deterministic := true
    reads := none
    modifies := .LiteralBool true
    body := .Transparent body
  }

def translateProgram (prog : Program) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  for decl in prog.commands do
    match decl with
    | .op op =>
      if op.name == q`Laurel.procedure then
        let proc ← translateProcedure decl
        procedures := procedures ++ [proc]
      else
        TransM.error s!"Unknown top-level declaration: {op.name}"
    | _ => TransM.error s!"translateProgram expects operations"
  return {
    staticProcedures := procedures
    staticFields := []
    types := []
  }

end Strata

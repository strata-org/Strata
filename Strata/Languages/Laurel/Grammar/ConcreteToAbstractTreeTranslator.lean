/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Laurel
import Strata.DL.Imperative.MetaData
import Strata.Languages.Boogie.Expressions

namespace Laurel

open Laurel
open Std (ToFormat Format format)
open Strata (QualifiedIdent Arg SourceRange)
open Lean.Parser (InputContext)
open Imperative (MetaData Uri FileRange)

structure TransState where
  inputCtx : InputContext
  errors : Array String

abbrev TransM := StateM TransState

def TransM.run (ictx : InputContext) (m : TransM α) : (α × Array String) :=
  let (v, s) := StateT.run m { inputCtx := ictx, errors := #[] }
  (v, s.errors)

def TransM.error [Inhabited α] (msg : String) : TransM α := do
  modify fun s => { s with errors := s.errors.push msg }
  return panic msg

def SourceRange.toMetaData (ictx : InputContext) (sr : SourceRange) : Imperative.MetaData Boogie.Expression :=
  let file := ictx.fileName
  let startPos := ictx.fileMap.toPosition sr.start
  let endPos := ictx.fileMap.toPosition sr.stop
  let uri : Uri := .file file
  let fileRangeElt := ⟨ Imperative.MetaDataElem.Field.label "fileRange", .fileRange ⟨ uri, startPos, endPos ⟩ ⟩
  #[fileRangeElt]

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Boogie.Expression) :=
  return SourceRange.toMetaData (← get).inputCtx arg.ann

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
  | .expr (.fn _ name) =>
    if name == q`Laurel.boolTrue then
      return true
    else if name == q`Laurel.boolFalse then
      return false
    else
      TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr name}"
  | .op op =>
    if op.name == q`Laurel.boolTrue then
      return true
    else if op.name == q`Laurel.boolFalse then
      return false
    else
      TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr op.name}"
  | x => TransM.error s!"translateBool expects expression or operation, got {repr x}"

instance : Inhabited Procedure where
  default := {
    name := ""
    inputs := []
    output := .TVoid
    precondition := .LiteralBool true
    decreases := none
    determinism := Determinism.deterministic none
    modifies := none
    body := .Transparent (.LiteralBool true)
  }

mutual

partial def translateStmtExpr (arg : Arg) : TransM StmtExpr := do
  match arg with
  | .op op =>
    if op.name == q`Laurel.assert then
      let cond ← translateStmtExpr op.args[0]!
      let md ← getArgMetaData (.op op)
      return .Assert cond md
    else if op.name == q`Laurel.assume then
      let cond ← translateStmtExpr op.args[0]!
      let md ← getArgMetaData (.op op)
      return .Assume cond md
    else if op.name == q`Laurel.block then
      let stmts ← translateSeqCommand op.args[0]!
      return .Block stmts none
    else if op.name == q`Laurel.literalBool then
      let boolVal ← translateBool op.args[0]!
      return .LiteralBool boolVal
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

def parseProcedure (arg : Arg) : TransM Procedure := do
  let .op op := arg
    | TransM.error s!"parseProcedure expects operation"
  let name ← translateIdent op.args[0]!
  let body ← translateCommand op.args[1]!
  return {
    name := name
    inputs := []
    output := .TVoid
    precondition := .LiteralBool true
    decreases := none
    determinism := Determinism.deterministic none
    modifies := none
    body := .Transparent body
  }

/- Translate concrete Laurel syntax into abstract Laurel syntax -/
def parseProgram (prog : Strata.Program) : TransM Laurel.Program := do
  -- Unwrap the program operation if present
  -- The parsed program may have a single `program` operation wrapping the procedures
  let commands : Array Strata.Operation :=
    -- support the program optionally being wrapped in a top level command
    if prog.commands.size == 1 && prog.commands[0]!.name == q`Laurel.program then
      -- Extract procedures from the program operation's first argument (Seq Procedure)
      match prog.commands[0]!.args[0]! with
      | .seq _ procs => procs.filterMap fun arg =>
          match arg with
          | .op op => some op
          | _ => none
      | _ => prog.commands
    else
      prog.commands

  let mut procedures : List Procedure := []
  for op in commands do
    if op.name == q`Laurel.procedure then
      let proc ← parseProcedure (.op op)
      procedures := procedures ++ [proc]
    else
      TransM.error s!"Unknown top-level declaration: {op.name}"
  return {
    staticProcedures := procedures
    staticFields := []
    types := []
  }

end Laurel

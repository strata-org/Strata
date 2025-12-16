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
  return arg.ann.toMetaData (← get).inputCtx

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

instance : Inhabited HighType where
  default := .TVoid

instance : Inhabited Parameter where
  default := { name := "", type := .TVoid }

def translateHighType (arg : Arg) : TransM HighType := do
  match arg with
  | .op op =>
    if op.name == q`Laurel.intType then
      return .TInt
    else if op.name == q`Laurel.boolType then
      return .TBool
    else
      TransM.error s!"translateHighType expects intType or boolType, got {repr op.name}"
  | _ => TransM.error s!"translateHighType expects operation"

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num literal"
  return n

def translateParameter (arg : Arg) : TransM Parameter := do
  let .op op := arg
    | TransM.error s!"translateParameter expects operation"
  if op.name != q`Laurel.parameter then
    TransM.error s!"translateParameter expects parameter operation, got {repr op.name}"
  let name ← translateIdent op.args[0]!
  let paramType ← translateHighType op.args[1]!
  return { name := name, type := paramType }

def translateParameters (arg : Arg) : TransM (List Parameter) := do
  match arg with
  | .commaSepList _ args =>
    args.toList.mapM translateParameter
  | _ => pure []

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
    else if op.name == q`Laurel.boolTrue then
      return .LiteralBool true
    else if op.name == q`Laurel.boolFalse then
      return .LiteralBool false
    else if op.name == q`Laurel.int then
      let n ← translateNat op.args[0]!
      return .LiteralInt n
    else if op.name == q`Laurel.varDecl then
      let name ← translateIdent op.args[0]!
      let typeArg := op.args[1]!
      let assignArg := op.args[2]!
      let varType ← match typeArg with
        | .option _ (some (.op typeOp)) =>
          if typeOp.name == q`Laurel.optionalType then
            translateHighType typeOp.args[0]!
          else
            pure .TInt
        | _ => pure .TInt
      let value ← match assignArg with
        | .option _ (some (.op assignOp)) =>
          if assignOp.name == q`Laurel.optionalAssignment then
            translateStmtExpr assignOp.args[0]! >>= (pure ∘ some)
          else
            pure none
        | _ => pure none
      return .LocalVariable name varType value
    else if op.name == q`Laurel.identifier then
      let name ← translateIdent op.args[0]!
      return .Identifier name
    else if op.name == q`Laurel.parenthesis then
      -- Parentheses don't affect the AST, just pass through
      translateStmtExpr op.args[0]!
    else if op.name == q`Laurel.assign then
      let target ← translateStmtExpr op.args[0]!
      let value ← translateStmtExpr op.args[1]!
      return .Assign target value
    else if op.name == q`Laurel.add then
      let lhs ← translateStmtExpr op.args[0]!
      let rhs ← translateStmtExpr op.args[1]!
      return .PrimitiveOp .Add [lhs, rhs]
    else if op.name == q`Laurel.eq then
      let lhs ← translateStmtExpr op.args[0]!
      let rhs ← translateStmtExpr op.args[1]!
      return .PrimitiveOp .Eq [lhs, rhs]
    else if op.name == q`Laurel.neq then
      let lhs ← translateStmtExpr op.args[0]!
      let rhs ← translateStmtExpr op.args[1]!
      return .PrimitiveOp .Neq [lhs, rhs]
    else if op.name == q`Laurel.gt then
      let lhs ← translateStmtExpr op.args[0]!
      let rhs ← translateStmtExpr op.args[1]!
      return .PrimitiveOp .Gt [lhs, rhs]
    else if op.name == q`Laurel.call then
      -- Handle function calls
      let callee ← translateStmtExpr op.args[0]!
      -- Extract the function name
      let calleeName := match callee with
        | .Identifier name => name
        | _ => ""
      -- Translate arguments from CommaSepBy
      let argsSeq := op.args[1]!
      let argsList ← match argsSeq with
        | .commaSepList _ args =>
          args.toList.mapM translateStmtExpr
        | _ => pure []
      return .StaticCall calleeName argsList
    else if op.name == q`Laurel.return then
      let value ← translateStmtExpr op.args[0]!
      return .Return value
    else if op.name == q`Laurel.ifThenElse then
      let cond ← translateStmtExpr op.args[0]!
      let thenBranch ← translateStmtExpr op.args[1]!
      let elseArg := op.args[2]!
      let elseBranch ← match elseArg with
        | .option _ (some (.op elseOp)) =>
          if elseOp.name == q`Laurel.optionalElse then
            translateStmtExpr elseOp.args[0]! >>= (pure ∘ some)
          else
            pure none
        | _ => pure none
      return .IfThenElse cond thenBranch elseBranch
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

  if op.name == q`Laurel.procedure then
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
  else if op.name == q`Laurel.procedureWithReturnType then
    let name ← translateIdent op.args[0]!
    let parameters ← translateParameters op.args[1]!
    let returnType ← translateHighType op.args[2]!
    let body ← translateCommand op.args[3]!
    return {
      name := name
      inputs := parameters
      output := returnType
      precondition := .LiteralBool true
      decreases := none
      determinism := Determinism.deterministic none
      modifies := none
      body := .Transparent body
    }
  else
    TransM.error s!"parseProcedure expects procedure or procedureWithReturnType, got {repr op.name}"

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
    if op.name == q`Laurel.procedure || op.name == q`Laurel.procedureWithReturnType then
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

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Laurel
import Strata.DL.Imperative.MetaData
import Strata.Languages.Core.Expressions

namespace Laurel

open Std (ToFormat Format format)
open Strata (QualifiedIdent Arg SourceRange)
open Lean.Parser (InputContext)
open Imperative (MetaData Uri FileRange)

structure TransState where
  inputCtx : InputContext

abbrev TransM := StateT TransState (Except String)

def TransM.run (ictx : InputContext) (m : TransM α) : Except String α :=
  match StateT.run m { inputCtx := ictx } with
  | .ok (v, _) => .ok v
  | .error e => .error e

def TransM.error (msg : String) : TransM α :=
  throw msg

def SourceRange.toMetaData (ictx : InputContext) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let file := ictx.fileName
  let startPos := ictx.fileMap.toPosition sr.start
  let endPos := ictx.fileMap.toPosition sr.stop
  let uri : Uri := .file file
  let fileRangeElt := ⟨ Imperative.MetaDataElem.Field.label "fileRange", .fileRange ⟨ uri, startPos, endPos ⟩ ⟩
  #[fileRangeElt]

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Core.Expression) :=
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
    match name with
    | q`Laurel.boolTrue => return true
    | q`Laurel.boolFalse => return false
    | _ => TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr name}"
  | .op op =>
    match op.name with
    | q`Laurel.boolTrue => return true
    | q`Laurel.boolFalse => return false
    | _ => TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr op.name}"
  | x => TransM.error s!"translateBool expects expression or operation, got {repr x}"

instance : Inhabited HighType where
  default := .TVoid

instance : Inhabited Parameter where
  default := { name := "", type := .TVoid }

def translateHighType (arg : Arg) : TransM HighType := do
  match arg with
  | .op op =>
    match op.name with
    | q`Laurel.intType => return .TInt
    | q`Laurel.boolType => return .TBool
    | _ => TransM.error s!"translateHighType expects intType or boolType, got {repr op.name}"
  | _ => TransM.error s!"translateHighType expects operation"

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num literal"
  return n

def translateParameter (arg : Arg) : TransM Parameter := do
  let .op op := arg
    | TransM.error s!"translateParameter expects operation"
  match op.name, op.args with
  | q`Laurel.parameter, #[arg0, arg1] =>
    let name ← translateIdent arg0
    let paramType ← translateHighType arg1
    return { name := name, type := paramType }
  | q`Laurel.parameter, args =>
    TransM.error s!"parameter needs two arguments, not {args.size}"
  | _, _ =>
    TransM.error s!"translateParameter expects parameter operation, got {repr op.name}"

def translateParameters (arg : Arg) : TransM (List Parameter) := do
  match arg with
  | .seq _ .comma args =>
    args.toList.mapM translateParameter
  | _ => pure []

instance : Inhabited Procedure where
  default := {
    name := ""
    inputs := []
    outputs := []
    precondition := .LiteralBool true
    decreases := none
    determinism := Determinism.deterministic none
    modifies := none
    body := .Transparent (.LiteralBool true)
  }

def getBinaryOp? (name : QualifiedIdent) : Option Operation :=
  match name with
  | q`Laurel.add => some Operation.Add
  | q`Laurel.eq => some Operation.Eq
  | q`Laurel.neq => some Operation.Neq
  | q`Laurel.gt => some Operation.Gt
  | q`Laurel.lt => some Operation.Lt
  | q`Laurel.le => some Operation.Leq
  | q`Laurel.ge => some Operation.Geq
  | _ => none

mutual

partial def translateStmtExpr (arg : Arg) : TransM StmtExpr := do
  match arg with
  | .op op => match op.name, op.args with
    | q`Laurel.assert, #[arg0] =>
      let cond ← translateStmtExpr arg0
      let md ← getArgMetaData (.op op)
      return .Assert cond md
    | q`Laurel.assume, #[arg0] =>
      let cond ← translateStmtExpr arg0
      let md ← getArgMetaData (.op op)
      return .Assume cond md
    | q`Laurel.block, #[arg0] =>
      let stmts ← translateSeqCommand arg0
      return .Block stmts none
    | q`Laurel.boolTrue, _ => return .LiteralBool true
    | q`Laurel.boolFalse, _ => return .LiteralBool false
    | q`Laurel.int, #[arg0] =>
      let n ← translateNat arg0
      return .LiteralInt n
    | q`Laurel.varDecl, #[arg0, typeArg, assignArg] =>
      let name ← translateIdent arg0
      let varType ← match typeArg with
        | .option _ (some (.op typeOp)) => match typeOp.name, typeOp.args with
          | q`Laurel.optionalType, #[typeArg0] => translateHighType typeArg0
          | _, _ => pure .TInt
        | _ => pure .TInt
      let value ← match assignArg with
        | .option _ (some (.op assignOp)) => match assignOp.args with
          | #[assignArg0] => translateStmtExpr assignArg0 >>= (pure ∘ some)
          | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
        | .option _ none => pure none
        | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
      return .LocalVariable name varType value
    | q`Laurel.identifier, #[arg0] =>
      let name ← translateIdent arg0
      return .Identifier name
    | q`Laurel.parenthesis, #[arg0] => translateStmtExpr arg0
    | q`Laurel.assign, #[arg0, arg1] =>
      let target ← translateStmtExpr arg0
      let value ← translateStmtExpr arg1
      return .Assign target value
    | q`Laurel.call, #[arg0, argsSeq] =>
      let callee ← translateStmtExpr arg0
      let calleeName := match callee with
        | .Identifier name => name
        | _ => ""
      let argsList ← match argsSeq with
        | .seq _ .comma args => args.toList.mapM translateStmtExpr
        | _ => pure []
      return .StaticCall calleeName argsList
    | q`Laurel.return, #[arg0] =>
      let value ← translateStmtExpr arg0
      return .Return (some value)
    | q`Laurel.ifThenElse, #[arg0, arg1, elseArg] =>
      let cond ← translateStmtExpr arg0
      let thenBranch ← translateStmtExpr arg1
      let elseBranch ← match elseArg with
        | .option _ (some (.op elseOp)) => match elseOp.name, elseOp.args with
          | q`Laurel.optionalElse, #[elseArg0] => translateStmtExpr elseArg0 >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      return .IfThenElse cond thenBranch elseBranch
    | _, #[arg0, arg1] => match getBinaryOp? op.name with
      | some primOp =>
        let lhs ← translateStmtExpr arg0
        let rhs ← translateStmtExpr arg1
        return .PrimitiveOp primOp [lhs, rhs]
      | none => TransM.error s!"Unknown operation: {op.name}"
    | _, _ => TransM.error s!"Unknown operation: {op.name}"
  | _ => TransM.error s!"translateStmtExpr expects operation"

partial def translateSeqCommand (arg : Arg) : TransM (List StmtExpr) := do
  let .seq _ .none args := arg
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

  match op.name, op.args with
  | q`Laurel.procedure, #[arg0, arg1, returnParamsArg, arg3] =>
    let name ← translateIdent arg0
    let parameters ← translateParameters arg1
    -- returnParamsArg is ReturnParameters category, need to unwrap returnParameters operation
    let returnParameters ← match returnParamsArg with
      | .option _ (some (.op returnOp)) => match returnOp.name, returnOp.args with
        | q`Laurel.returnParameters, #[returnArg0] => translateParameters returnArg0
        | _, _ => TransM.error s!"Expected returnParameters operation, got {repr returnOp.name}"
      | .option _ none => pure []
      | _ => TransM.error s!"Expected returnParameters operation, got {repr returnParamsArg}"
    let body ← translateCommand arg3
    return {
      name := name
      inputs := parameters
      outputs := returnParameters
      precondition := .LiteralBool true
      decreases := none
      determinism := Determinism.deterministic none
      modifies := none
      body := .Transparent body
    }
  | q`Laurel.procedure, args =>
    TransM.error s!"parseProcedure expects 4 arguments, got {args.size}"
  | _, _ =>
    TransM.error s!"parseProcedure expects procedure, got {repr op.name}"

/--
Translate concrete Laurel syntax into abstract Laurel syntax
-/
def parseProgram (prog : Strata.Program) : TransM Laurel.Program := do
  -- Unwrap the program operation if present
  -- The parsed program may have a single `program` operation wrapping the procedures
  let commands : Array Strata.Operation :=
    -- support the program optionally being wrapped in a top level command
    if prog.commands.size == 1 && prog.commands[0]!.name == q`Laurel.program then
      -- Extract procedures from the program operation's first argument (Seq Procedure)
      match prog.commands[0]!.args[0]! with
      | .seq _ .none procs => procs.filterMap fun arg =>
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

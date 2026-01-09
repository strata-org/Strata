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
  if op.name != q`Laurel.parameter then
    TransM.error s!"translateParameter expects parameter operation, got {repr op.name}"
  if op.args.size == 2 then
    let name ← translateIdent op.args[0]!
    let paramType ← translateHighType op.args[1]!
    return { name := name, type := paramType }
  else
    TransM.error s!"parameter needs two arguments, not {repr op.args.size}"

def translateParameters (arg : Arg) : TransM (List Parameter) := do
  match arg with
  | .commaSepList _ args =>
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

def binaryOpMap : List (QualifiedIdent × Operation) := [
  (q`Laurel.add, Operation.Add),
  (q`Laurel.eq, Operation.Eq),
  (q`Laurel.neq, Operation.Neq),
  (q`Laurel.gt, Operation.Gt),
  (q`Laurel.lt, Operation.Lt),
  (q`Laurel.le, Operation.Leq),
  (q`Laurel.ge, Operation.Geq)
]

def getBinaryOp? (name : QualifiedIdent) : Option Operation :=
  binaryOpMap.lookup name

mutual

partial def translateStmtExpr (arg : Arg) : TransM StmtExpr := do
  match arg with
  | .op op => match op.name with
    | q`Laurel.assert =>
      let cond ← translateStmtExpr op.args[0]!
      let md ← getArgMetaData (.op op)
      return .Assert cond md
    | q`Laurel.assume =>
      let cond ← translateStmtExpr op.args[0]!
      let md ← getArgMetaData (.op op)
      return .Assume cond md
    | q`Laurel.block =>
      let stmts ← translateSeqCommand op.args[0]!
      return .Block stmts none
    | q`Laurel.boolTrue => return .LiteralBool true
    | q`Laurel.boolFalse => return .LiteralBool false
    | q`Laurel.int =>
      let n ← translateNat op.args[0]!
      return .LiteralInt n
    | q`Laurel.varDecl =>
      let name ← translateIdent op.args[0]!
      let typeArg := op.args[1]!
      let assignArg := op.args[2]!
      let varType ← match typeArg with
        | .option _ (some (.op typeOp)) => match typeOp.name with
          | q`Laurel.optionalType => translateHighType typeOp.args[0]!
          | _ => pure .TInt
        | _ => pure .TInt
      let value ← match assignArg with
        | .option _ (some (.op assignOp)) =>
          translateStmtExpr assignOp.args[0]! >>= (pure ∘ some)
        | .option _ none => pure none
        | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
      return .LocalVariable name varType value
    | q`Laurel.identifier =>
      let name ← translateIdent op.args[0]!
      return .Identifier name
    | q`Laurel.parenthesis => translateStmtExpr op.args[0]!
    | q`Laurel.assign =>
      let target ← translateStmtExpr op.args[0]!
      let value ← translateStmtExpr op.args[1]!
      return .Assign target value
    | q`Laurel.call =>
      let callee ← translateStmtExpr op.args[0]!
      let calleeName := match callee with
        | .Identifier name => name
        | _ => ""
      let argsSeq := op.args[1]!
      let argsList ← match argsSeq with
        | .commaSepList _ args => args.toList.mapM translateStmtExpr
        | _ => pure []
      return .StaticCall calleeName argsList
    | q`Laurel.return =>
      let value ← translateStmtExpr op.args[0]!
      return .Return (some value)
    | q`Laurel.ifThenElse =>
      let cond ← translateStmtExpr op.args[0]!
      let thenBranch ← translateStmtExpr op.args[1]!
      let elseArg := op.args[2]!
      let elseBranch ← match elseArg with
        | .option _ (some (.op elseOp)) => match elseOp.name with
          | q`Laurel.optionalElse => translateStmtExpr elseOp.args[0]! >>= (pure ∘ some)
          | _ => pure none
        | _ => pure none
      return .IfThenElse cond thenBranch elseBranch
    | _ => match getBinaryOp? op.name with
      | some primOp =>
        let lhs ← translateStmtExpr op.args[0]!
        let rhs ← translateStmtExpr op.args[1]!
        return .PrimitiveOp primOp [lhs, rhs]
      | none => TransM.error s!"Unknown operation: {op.name}"
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
    let parameters ← translateParameters op.args[1]!
    -- args[2] is ReturnParameters category, need to unwrap returnParameters operation
    let returnParameters ← match op.args[2]! with
      | .option _ (some (.op returnOp)) => match returnOp.name with
        | q`Laurel.returnParameters => translateParameters returnOp.args[0]!
        | _ => TransM.error s!"Expected returnParameters operation, got {repr returnOp.name}"
      | .option _ none => pure []
      | _ => TransM.error s!"Expected returnParameters operation, got {repr op.args[2]!}"
    let body ← translateCommand op.args[3]!
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
  else TransM.error s!"parseProcedure expects procedure, got {repr op.name}"

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

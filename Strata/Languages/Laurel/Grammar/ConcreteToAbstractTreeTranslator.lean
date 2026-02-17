/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Laurel
import Strata.DL.Imperative.MetaData
import Strata.Languages.Core.Expressions

namespace Strata
namespace Laurel

open Std (ToFormat Format format)
open Strata (QualifiedIdent Arg SourceRange Uri FileRange)
open Lean.Parser (InputContext)
open Imperative (MetaData)

structure TransState where
  uri : Uri
  errors : Array String

abbrev TransM := StateT TransState (Except String)

def TransM.run (uri : Uri) (m : TransM α) : Except String α :=
  match StateT.run m { uri := uri, errors := #[] } with
  | .ok (v, _) => .ok v
  | .error e => .error e

def TransM.error (msg : String) : TransM α :=
  throw msg

def SourceRange.toMetaData (uri : Uri) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let fileRangeElt := ⟨ Imperative.MetaDataElem.Field.label "fileRange", .fileRange ⟨ uri, sr.start, sr.stop ⟩ ⟩
  #[fileRangeElt]

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Core.Expression) :=
  return SourceRange.toMetaData (← get).uri arg.ann

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
    | q`Init.boolTrue => return true
    | q`Init.boolFalse => return false
    | _ => TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr name}"
  | .op op =>
    match op.name with
    | q`Init.boolTrue => return true
    | q`Init.boolFalse => return false
    | _ => TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr op.name}"
  | x => TransM.error s!"translateBool expects expression or operation, got {repr x}"

instance : Inhabited HighType where
  default := .TVoid

instance : Inhabited Parameter where
  default := { name := "", type := ⟨.TVoid, #[]⟩ }

/-- Create a HighTypeMd with the given metadata -/
def mkHighTypeMd (t : HighType) (md : MetaData Core.Expression) : HighTypeMd := ⟨t, md⟩

/-- Create a StmtExprMd with the given metadata -/
def mkStmtExprMd (e : StmtExpr) (md : MetaData Core.Expression) : StmtExprMd := ⟨e, md⟩

partial def translateHighType (arg : Arg) : TransM HighTypeMd := do
  let md ← getArgMetaData arg
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`Laurel.intType, _ => return mkHighTypeMd .TInt md
    | q`Laurel.boolType, _ => return mkHighTypeMd .TBool md
    | q`Laurel.stringType, _ => return mkHighTypeMd .TString md
    | q`Laurel.arrayType, #[elemArg] =>
      let elemType ← translateHighType elemArg
      return mkHighTypeMd (.Applied (mkHighTypeMd (.UserDefined "Array") md) [elemType]) md
    | q`Laurel.compositeType, #[nameArg] =>
      let name ← translateIdent nameArg
      return mkHighTypeMd (.UserDefined name) md
    | _, _ => TransM.error s!"translateHighType expects intType, boolType, stringType, arrayType or compositeType, got {repr op.name}"
  | _ => TransM.error s!"translateHighType expects operation"

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num literal"
  return n

def translateString (arg : Arg) : TransM String := do
  let .strlit _ s := arg
    | TransM.error s!"translateString expects string literal"
  return s

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
    preconditions := []
    decreases := none
    body := .Transparent ⟨.LiteralBool true, #[]⟩
  }

def getBinaryOp? (name : QualifiedIdent) : Option Operation :=
  match name with
  | q`Laurel.add => some Operation.Add
  | q`Laurel.sub => some Operation.Sub
  | q`Laurel.mul => some Operation.Mul
  | q`Laurel.div => some Operation.Div
  | q`Laurel.mod => some Operation.Mod
  | q`Laurel.divT => some Operation.DivT
  | q`Laurel.modT => some Operation.ModT
  | q`Laurel.eq => some Operation.Eq
  | q`Laurel.neq => some Operation.Neq
  | q`Laurel.gt => some Operation.Gt
  | q`Laurel.lt => some Operation.Lt
  | q`Laurel.le => some Operation.Leq
  | q`Laurel.ge => some Operation.Geq
  | q`Laurel.and => some Operation.And
  | q`Laurel.or => some Operation.Or
  | q`Laurel.implies => some Operation.Implies
  | q`Laurel.strConcat => some Operation.StrConcat
  | _ => none

def getUnaryOp? (name : QualifiedIdent) : Option Operation :=
  match name with
  | q`Laurel.not => some Operation.Not
  | q`Laurel.neg => some Operation.Neg
  | _ => none

mutual

partial def translateStmtExpr (arg : Arg) : TransM StmtExprMd := do
  let md ← getArgMetaData arg
  match arg with
  | .op op => match op.name, op.args with
    | q`Laurel.assert, #[arg0] =>
      let cond ← translateStmtExpr arg0
      return mkStmtExprMd (.Assert cond none) md
    | q`Laurel.assume, #[arg0] =>
      let cond ← translateStmtExpr arg0
      return mkStmtExprMd (.Assume cond) md
    | q`Laurel.block, #[arg0] =>
      let stmts ← translateSeqCommand arg0
      return mkStmtExprMd (.Block stmts none) md
    | q`Laurel.literalBool, #[arg0] => return mkStmtExprMd (.LiteralBool (← translateBool arg0)) md
    | q`Laurel.int, #[arg0] =>
      let n ← translateNat arg0
      return mkStmtExprMd (.LiteralInt n) md
    | q`Laurel.string, #[arg0] =>
      let s ← translateString arg0
      return mkStmtExprMd (.LiteralString s) md
    | q`Laurel.varDecl, #[arg0, typeArg, assignArg] =>
      let name ← translateIdent arg0
      let varType ← match typeArg with
        | .option _ (some (.op typeOp)) => match typeOp.name, typeOp.args with
          | q`Laurel.optionalType, #[typeArg0] => translateHighType typeArg0
          | _, _ => TransM.error s!"Variable {name} requires explicit type"
        | _ => TransM.error s!"Variable {name} requires explicit type"
      let value ← match assignArg with
        | .option _ (some (.op assignOp)) => match assignOp.args with
          | #[assignArg0] => translateStmtExpr assignArg0 >>= (pure ∘ some)
          | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
        | .option _ none => pure none
        | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
      return mkStmtExprMd (.LocalVariable name varType value) md
    | q`Laurel.identifier, #[arg0] =>
      let name ← translateIdent arg0
      return mkStmtExprMd (.Identifier name) md
    | q`Laurel.parenthesis, #[arg0] => translateStmtExpr arg0
    | q`Laurel.assign, #[arg0, arg1] =>
      let target ← translateStmtExpr arg0
      let value ← translateStmtExpr arg1
      return mkStmtExprMd (.Assign [target] value) md
    | q`Laurel.call, #[arg0, argsSeq] =>
      let callee ← translateStmtExpr arg0
      let calleeName := match callee.val with
        | .Identifier name => name
        | _ => ""
      let argsList ← match argsSeq with
        | .seq _ .comma args => args.toList.mapM translateStmtExpr
        | _ => pure []
      return mkStmtExprMd (.StaticCall calleeName argsList) md
    | q`Laurel.return, #[arg0] =>
      let value ← translateStmtExpr arg0
      return mkStmtExprMd (.Return (some value)) md
    | q`Laurel.ifThenElse, #[arg0, arg1, elseArg] =>
      let cond ← translateStmtExpr arg0
      let thenBranch ← translateStmtExpr arg1
      let elseBranch ← match elseArg with
        | .option _ (some (.op elseOp)) => match elseOp.name, elseOp.args with
          | q`Laurel.optionalElse, #[elseArg0] => translateStmtExpr elseArg0 >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.IfThenElse cond thenBranch elseBranch) md
    | q`Laurel.fieldAccess, #[objArg, fieldArg] =>
      let obj ← translateStmtExpr objArg
      let field ← translateIdent fieldArg
      return mkStmtExprMd (.FieldSelect obj field) md
    | q`Laurel.arrayIndex, #[arrArg, idxArg] =>
      let arr ← translateStmtExpr arrArg
      let idx ← translateStmtExpr idxArg
      return mkStmtExprMd (.StaticCall "Array.Get" [arr, idx]) md
    | q`Laurel.while, #[condArg, invSeqArg, bodyArg] =>
      let cond ← translateStmtExpr condArg
      let invariants ← match invSeqArg with
        | .seq _ _ clauses => clauses.toList.mapM fun arg => match arg with
            | .op invOp => match invOp.name, invOp.args with
              | q`Laurel.invariantClause, #[exprArg] => translateStmtExpr exprArg
              | _, _ => TransM.error "Expected invariantClause"
            | _ => TransM.error "Expected operation"
        | _ => pure []
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.While cond invariants none body) md
    | _, #[arg0] => match getUnaryOp? op.name with
      | some primOp =>
        let inner ← translateStmtExpr arg0
        return mkStmtExprMd (.PrimitiveOp primOp [inner]) md
      | none => TransM.error s!"Unknown unary operation: {op.name}"
    | q`Laurel.forallExpr, #[nameArg, tyArg, bodyArg] =>
      let name ← translateIdent nameArg
      let ty ← translateHighType tyArg
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.Forall name ty body) md
    | q`Laurel.existsExpr, #[nameArg, tyArg, bodyArg] =>
      let name ← translateIdent nameArg
      let ty ← translateHighType tyArg
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.Exists name ty body) md
    | _, #[arg0, arg1] => match getBinaryOp? op.name with
      | some primOp =>
        let lhs ← translateStmtExpr arg0
        let rhs ← translateStmtExpr arg1
        return mkStmtExprMd (.PrimitiveOp primOp [lhs, rhs]) md
      | none => TransM.error s!"Unknown operation: {op.name}"
    | _, _ => TransM.error s!"Unknown operation: {op.name}"
  | _ => TransM.error s!"translateStmtExpr expects operation"

partial def translateSeqCommand (arg : Arg) : TransM (List StmtExprMd) := do
  let args ← match arg with
    | .seq _ .none args => pure args
    | .seq _ .newline args => pure args  -- NewlineSepBy for block statements
    | _ => TransM.error s!"translateSeqCommand expects seq or newlineSepBy"
  let mut stmts : List StmtExprMd := []
  for arg in args do
    let stmt ← translateStmtExpr arg
    stmts := stmts ++ [stmt]
  return stmts

partial def translateCommand (arg : Arg) : TransM StmtExprMd := do
  translateStmtExpr arg

end

def parseProcedure (arg : Arg) : TransM Procedure := do
  let .op op := arg
    | TransM.error s!"parseProcedure expects operation"

  match op.name, op.args with
  | q`Laurel.procedure, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
      requiresArg, ensuresArg, bodyArg] =>
    let name ← translateIdent nameArg
    let parameters ← translateParameters paramArg
    -- Either returnTypeArg or returnParamsArg may have a value, not both
    -- If returnTypeArg is set, create a single "result" parameter
    let returnParameters ← match returnTypeArg with
      | .option _ (some (.op returnTypeOp)) => match returnTypeOp.name, returnTypeOp.args with
        | q`Laurel.optionalReturnType, #[typeArg] =>
          let retType ← translateHighType typeArg
          pure [{ name := "result", type := retType : Parameter }]
        | _, _ => TransM.error s!"Expected optionalReturnType operation, got {repr returnTypeOp.name}"
      | .option _ none =>
        -- No return type, check returnParamsArg instead
        match returnParamsArg with
        | .option _ (some (.op returnOp)) => match returnOp.name, returnOp.args with
          | q`Laurel.returnParameters, #[returnArg0] => translateParameters returnArg0
          | _, _ => TransM.error s!"Expected returnParameters operation, got {repr returnOp.name}"
        | .option _ none => pure []
        | _ => TransM.error s!"Expected returnParameters operation, got {repr returnParamsArg}"
      | _ => TransM.error s!"Expected optionalReturnType operation, got {repr returnTypeArg}"
    -- Parse preconditions (requires clauses)
    let preconditions ← match requiresArg with
      | .seq _ _ clauses => clauses.toList.mapM fun arg => match arg with
          | .op reqOp => match reqOp.name, reqOp.args with
            | q`Laurel.requiresClause, #[exprArg] => translateStmtExpr exprArg
            | _, _ => TransM.error "Expected requiresClause"
          | _ => TransM.error "Expected operation"
      | _ => pure []
    -- Parse postconditions (ensures clauses)
    let postconditions ← match ensuresArg with
      | .seq _ _ clauses => clauses.toList.mapM fun arg => match arg with
          | .op ensOp => match ensOp.name, ensOp.args with
            | q`Laurel.ensuresClause, #[exprArg] => translateStmtExpr exprArg
            | _, _ => TransM.error "Expected ensuresClause"
          | _ => TransM.error "Expected operation"
      | _ => pure []
    let body ← translateCommand bodyArg
    -- If there are postconditions, use Opaque body; otherwise use Transparent
    let procBody := match postconditions with
      | [] => Body.Transparent body
      | posts => Body.Opaque posts (some body) none
    return {
      name := name
      inputs := parameters
      outputs := returnParameters
      preconditions := preconditions
      decreases := none
      body := procBody
    }
  | q`Laurel.procedure, args =>
    TransM.error s!"parseProcedure expects 7 arguments, got {args.size}"
  | _, _ =>
    TransM.error s!"parseProcedure expects procedure, got {repr op.name}"

def parseConstrainedType (arg : Arg) : TransM ConstrainedType := do
  let .op op := arg
    | TransM.error s!"parseConstrainedType expects operation"
  match op.name, op.args with
  | q`Laurel.constrainedType, #[nameArg, valueNameArg, baseArg, constraintArg, witnessArg] =>
    let name ← translateIdent nameArg
    let valueName ← translateIdent valueNameArg
    let base ← translateHighType baseArg
    let constraint ← translateStmtExpr constraintArg
    let witness ← translateStmtExpr witnessArg
    return { name, base, valueName, constraint, witness }
  | _, _ =>
    TransM.error s!"parseConstrainedType expects constrainedType, got {repr op.name}"

def parseField (arg : Arg) : TransM Field := do
  let .op op := arg
    | TransM.error s!"parseField expects operation"
  match op.name, op.args with
  | q`Laurel.mutableField, #[nameArg, typeArg] =>
    let name ← translateIdent nameArg
    let fieldType ← translateHighType typeArg
    return { name := name, isMutable := true, type := fieldType }
  | q`Laurel.immutableField, #[nameArg, typeArg] =>
    let name ← translateIdent nameArg
    let fieldType ← translateHighType typeArg
    return { name := name, isMutable := false, type := fieldType }
  | _, _ =>
    TransM.error s!"parseField expects mutableField or immutableField, got {repr op.name}"

def parseComposite (arg : Arg) : TransM TypeDefinition := do
  let .op op := arg
    | TransM.error s!"parseComposite expects operation"
  match op.name, op.args with
  | q`Laurel.composite, #[nameArg, fieldsArg] =>
    let name ← translateIdent nameArg
    let fields ← match fieldsArg with
      | .seq _ _ args => args.toList.mapM parseField
      | _ => pure []
    return .Composite { name := name, extending := [], fields := fields, instanceProcedures := [] }
  | _, _ =>
    TransM.error s!"parseComposite expects composite, got {repr op.name}"

inductive TopLevelItem where
  | proc (p : Procedure)
  | typeDef (t : TypeDefinition)

def parseTopLevel (arg : Arg) : TransM (Option TopLevelItem) := do
  let .op op := arg
    | TransM.error s!"parseTopLevel expects operation"

  match op.name, op.args with
  | q`Laurel.topLevelProcedure, #[procArg] =>
    let proc ← parseProcedure procArg
    return some (.proc proc)
  | q`Laurel.topLevelComposite, #[compositeArg] =>
    let typeDef ← parseComposite compositeArg
    return some (.typeDef typeDef)
  | q`Laurel.topLevelConstrainedType, #[ctArg] =>
    let ct ← parseConstrainedType ctArg
    return some (.typeDef (.Constrained ct))
  | _, _ =>
    TransM.error s!"parseTopLevel expects topLevelProcedure, topLevelComposite, or topLevelConstrainedType, got {repr op.name}"

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
  let mut types : List TypeDefinition := []
  for op in commands do
    let result ← parseTopLevel (.op op)
    match result with
    | some (.proc proc) => procedures := procedures ++ [proc]
    | some (.typeDef td) => types := types ++ [td]
    | none => pure () -- composite types are skipped for now
  return {
    staticProcedures := procedures
    staticFields := []
    types := types
  }

end Laurel

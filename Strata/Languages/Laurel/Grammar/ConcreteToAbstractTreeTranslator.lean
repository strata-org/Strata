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

instance : Inhabited Parameter where
  default := { name := "", type := ⟨.TVoid, #[]⟩ }

def mkHighTypeMd (t : HighType) (md : MetaData Core.Expression) : HighTypeMd := ⟨t, md⟩
def mkStmtExprMd (e : StmtExpr) (md : MetaData Core.Expression) : StmtExprMd := ⟨e, md⟩
def mkStmtExprMdEmpty (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

partial def translateHighType (arg : Arg) : TransM HighTypeMd := do
  let md ← getArgMetaData arg
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`Laurel.intType, _ => return mkHighTypeMd .TInt md
    | q`Laurel.boolType, _ => return mkHighTypeMd .TBool md
    | q`Laurel.stringType, _ => return mkHighTypeMd .TString md
    | q`Laurel.compositeType, #[nameArg] =>
      let name ← translateIdent nameArg
      return mkHighTypeMd (.UserDefined name) md
    | _, _ => TransM.error s!"translateHighType expects intType, boolType, arrayType or compositeType, got {repr op.name}"
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
    precondition := mkStmtExprMdEmpty <| .LiteralBool true
    determinism := .deterministic none
    decreases := none
    body := .Transparent ⟨.LiteralBool true, #[]⟩
    md := .empty
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
      return mkStmtExprMd (.Assert cond) md
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
    | q`Laurel.new, #[nameArg] =>
      let name ← translateIdent nameArg
      return mkStmtExprMd (.New name) md
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
    | _, #[arg0] => match getUnaryOp? op.name with
      | some primOp =>
        let inner ← translateStmtExpr arg0
        return mkStmtExprMd (.PrimitiveOp primOp [inner]) md
      | none => TransM.error s!"Unknown unary operation: {op.name}"
    | _, #[arg0, arg1] => match getBinaryOp? op.name with
      | some primOp =>
        let lhs ← translateStmtExpr arg0
        let rhs ← translateStmtExpr arg1
        return mkStmtExprMd (.PrimitiveOp primOp [lhs, rhs]) md
      | none => TransM.error s!"Unknown operation: {op.name}"
    | _, _ => TransM.error s!"Unknown operation: {op.name}"
  | _ => TransM.error s!"translateStmtExpr expects operation"

partial def translateSeqCommand (arg : Arg) : TransM (List StmtExprMd) := do
  let .seq _ .none args := arg
    | TransM.error s!"translateSeqCommand expects seq"
  let mut stmts : List StmtExprMd := []
  for arg in args do
    let stmt ← translateStmtExpr arg
    stmts := stmts ++ [stmt]
  return stmts

partial def translateCommand (arg : Arg) : TransM StmtExprMd := do
  translateStmtExpr arg

end

def translateModifiesExprs (arg : Arg) : TransM (List StmtExprMd) := do
  match arg with
  | .seq _ .comma args =>
    args.toList.mapM translateStmtExpr
  | _ => pure []

def translateModifiesClauses (arg : Arg) : TransM (List StmtExprMd) := do
  match arg with
  | .seq _ _ args => do
    let mut allModifies : List StmtExprMd := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp => match clauseOp.name, clauseOp.args with
        | q`Laurel.modifiesClause, #[refsArg] =>
          let refs ← translateModifiesExprs refsArg
          allModifies := allModifies ++ refs
        | _, _ => TransM.error s!"Expected modifiesClause operation, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected modifiesClause operation in modifies sequence"
    pure allModifies
  | _ => pure []

def translateEnsuresClauses (arg : Arg) : TransM (List StmtExprMd) := do
  match arg with
  | .seq _ _ args => do
    let mut allEnsures : List StmtExprMd := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp => match clauseOp.name, clauseOp.args with
        | q`Laurel.ensuresClause, #[exprArg] =>
          let expr ← translateStmtExpr exprArg
          allEnsures := allEnsures ++ [expr]
        | _, _ => TransM.error s!"Expected ensuresClause operation, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected ensuresClause operation in ensures sequence"
    pure allEnsures
  | _ => pure []

def parseProcedure (arg : Arg) : TransM Procedure := do
  let .op op := arg
    | TransM.error s!"parseProcedure expects operation"

  match op.name, op.args with
  | q`Laurel.procedure, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
      requiresArg, ensuresArg, modifiesArg, bodyArg] =>
    let name ← translateIdent nameArg
    let nameMd ← getArgMetaData nameArg
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
    -- Parse precondition (requires clause)
    let precondition ← match requiresArg with
      | .option _ (some (.op requiresOp)) => match requiresOp.name, requiresOp.args with
        | q`Laurel.optionalRequires, #[exprArg] => translateStmtExpr exprArg
        | _, _ => TransM.error s!"Expected optionalRequires operation, got {repr requiresOp.name}"
      | .option _ none => pure (mkStmtExprMdEmpty <| .LiteralBool true)
      | _ => TransM.error s!"Expected optionalRequires operation, got {repr requiresArg}"
    -- Parse postconditions (ensures clauses - zero or more)
    let postconditions ← translateEnsuresClauses ensuresArg
    -- Parse modifies clauses (zero or more)
    let modifies ← translateModifiesClauses modifiesArg
    -- Parse optional body
    let body ← match bodyArg with
      | .option _ (some (.op bodyOp)) => match bodyOp.name, bodyOp.args with
        | q`Laurel.optionalBody, #[exprArg] => translateCommand exprArg >>= (pure ∘ some)
        | _, _ => TransM.error s!"Expected optionalBody operation, got {repr bodyOp.name}"
      | .option _ none => pure none
      | _ => TransM.error s!"Expected optionalBody, got {repr bodyArg}"
    -- Determine procedure body kind
    let procBody := match postconditions, body with
      | _ :: _, bodyOpt => Body.Opaque postconditions bodyOpt modifies
      | [], some b => Body.Transparent b
      | [], none => Body.Opaque [] none modifies
    return {
      name := name
      inputs := parameters
      outputs := returnParameters
      precondition := precondition
      determinism := .deterministic none
      decreases := none
      body := procBody
      md := nameMd
    }
  | q`Laurel.procedure, args =>
    TransM.error s!"parseProcedure expects 8 arguments, got {args.size}"
  | _, _ =>
    TransM.error s!"parseProcedure expects procedure, got {repr op.name}"

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

def parseTopLevel (arg : Arg) : TransM (Option Procedure × Option TypeDefinition) := do
  let .op op := arg
    | TransM.error s!"parseTopLevel expects operation"

  match op.name, op.args with
  | q`Laurel.topLevelProcedure, #[procArg] =>
    let proc ← parseProcedure procArg
    return (some proc, none)
  | q`Laurel.topLevelComposite, #[compositeArg] =>
    let typeDef ← parseComposite compositeArg
    return (none, some typeDef)
  | _, _ =>
    TransM.error s!"parseTopLevel expects topLevelProcedure or topLevelComposite, got {repr op.name}"

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
    let (procOpt, typeOpt) ← parseTopLevel (.op op)
    match procOpt with
    | some proc => procedures := procedures ++ [proc]
    | none => pure ()
    match typeOpt with
    | some typeDef => types := types ++ [typeDef]
    | none => pure ()
  return {
    staticProcedures := procedures
    staticFields := []
    types := types
  }

end Laurel

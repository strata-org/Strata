/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Strata.Languages.Laurel.Grammar.LaurelGrammar
public import Strata.Languages.Laurel.Laurel
public import Strata.DL.Imperative.MetaData
public import Strata.Languages.Core.Expressions

namespace Strata
namespace Laurel

public section

open Std (ToFormat Format format)
open Strata (QualifiedIdent Arg SourceRange Uri FileRange)
open Lean.Parser (InputContext)
open Imperative (MetaData)

structure TransState where
  uri : Option Uri
  errors : Array String

@[expose] abbrev TransM := StateT TransState (Except String)

def TransM.run (uri : Option Uri) (m : TransM α) : Except String α :=
  match StateT.run m { uri := uri, errors := #[] } with
  | .ok (v, _) => .ok v
  | .error e => .error e

def TransM.error (msg : String) : TransM α :=
  throw msg

private def SourceRange.toFileRange (uri : Uri) (sr : SourceRange) : FileRange :=
  ⟨ uri, sr ⟩

private def getArgFileRange (arg : Arg) : TransM (Option FileRange) := do
  return match (← get).uri with
  | some uri => some (SourceRange.toFileRange uri arg.ann)
  | none => none

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Core.Expression) := do
  return match (← get).uri with
  | some uri => #[⟨Imperative.MetaData.fileRange, .fileRange (SourceRange.toFileRange uri arg.ann)⟩]
  | none => #[⟨Imperative.MetaData.fileRange, .fileRange FileRange.unknown⟩]

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
  let source ← getArgFileRange arg
  return { text := id, source := source }

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
  default := { name := "" , type := { val := .Unknown, source := none } }

def mkHighTypeMd (t : HighType) (source : Option FileRange) : HighTypeMd := { val := t, source := source }
def mkStmtExprMd (e : StmtExpr) (source : Option FileRange) : StmtExprMd := { val := e, source := source }

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num literal"
  return n

partial def translateHighType (arg : Arg) : TransM HighTypeMd := do
  let src ← getArgFileRange arg
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`Laurel.intType, _ => return mkHighTypeMd .TInt src
    | q`Laurel.boolType, _ => return mkHighTypeMd .TBool src
    | q`Laurel.float64Type, _ => return mkHighTypeMd .TFloat64 src
    | q`Laurel.realType, _ => return mkHighTypeMd .TReal src
    | q`Laurel.stringType, _ => return mkHighTypeMd .TString src
    | q`Laurel.bvType, #[widthArg] =>
      let width ← translateNat widthArg
      return mkHighTypeMd (.TBv width) src
    | q`Laurel.coreType, #[.ident _ name] => return mkHighTypeMd (.TCore name) src
    | q`Laurel.mapType, #[keyArg, valArg] =>
      let keyType ← translateHighType keyArg
      let valType ← translateHighType valArg
      return mkHighTypeMd (.TMap keyType valType) src
    | q`Laurel.seqType, #[elemArg] =>
      let elemType ← translateHighType elemArg
      return mkHighTypeMd (.TSeq elemType) src
    | q`Laurel.arrayType, #[elemArg] =>
      let elemType ← translateHighType elemArg
      return mkHighTypeMd (.TArray elemType) src
    | q`Laurel.compositeType, #[nameArg] =>
      let name ← translateIdent nameArg
      return mkHighTypeMd (.UserDefined name) src
    | _, _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
  | _ => TransM.error s!"translateHighType expects operation"

def translateString (arg : Arg) : TransM String := do
  let .strlit _ s := arg
    | TransM.error s!"translateString expects string literal"
  return s

def translateDecimal (arg : Arg) : TransM Decimal := do
  let .decimal _ d := arg
    | TransM.error s!"translateDecimal expects decimal literal"
  return d

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
    isFunctional := false
    invokeOn := none
    body := .Transparent { val := .LiteralBool true, source := none }
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
  | q`Laurel.andThen => some Operation.AndThen
  | q`Laurel.orElse => some Operation.OrElse
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
  let src ← getArgFileRange arg
  match arg with
  | .op op => match op.name, op.args with
    | q`Laurel.assert, #[arg0, errMsgArg] =>
      let cond ← translateStmtExpr arg0
      let summary ← match errMsgArg with
        | .option _ (some (.op errOp)) => match errOp.name, errOp.args with
          | q`Laurel.errorSummary, #[strArg] => do
            let msg ← translateString strArg
            pure (some msg)
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.Assert { condition := cond, summary }) src
    | q`Laurel.assume, #[arg0] =>
      let cond ← translateStmtExpr arg0
      return mkStmtExprMd (.Assume cond) src
    | q`Laurel.block, #[arg0] =>
      let stmts ← translateSeqCommand arg0
      return mkStmtExprMd (.Block stmts none) src
    | q`Laurel.labelledBlock, #[arg0, arg1] =>
      let stmts ← translateSeqCommand arg0
      let label ← translateIdent arg1
      return mkStmtExprMd (.Block stmts (some label.text)) src
    | q`Laurel.exit, #[arg0] =>
      let label ← translateIdent arg0
      return mkStmtExprMd (.Exit label.text) src
    | q`Laurel.literalBool, #[arg0] => return mkStmtExprMd (.LiteralBool (← translateBool arg0)) src
    | q`Laurel.int, #[arg0] =>
      let n ← translateNat arg0
      return mkStmtExprMd (.LiteralInt n) src
    | q`Laurel.real, #[arg0] =>
      let d ← translateDecimal arg0
      return mkStmtExprMd (.LiteralDecimal d) src
    | q`Laurel.string, #[arg0] =>
      let s ← translateString arg0
      return mkStmtExprMd (.LiteralString s) src
    | q`Laurel.hole, #[] => return mkStmtExprMd (.Hole true none) src
    | q`Laurel.nondetHole, #[] => return mkStmtExprMd (.Hole false none) src
    | q`Laurel.varDecl, #[arg0, typeArg, assignArg] =>
      let name ← translateIdent arg0
      let varType ← match typeArg with
        | .option _ (some (.op typeOp)) => match typeOp.name, typeOp.args with
          | q`Laurel.typeAnnotation, #[typeArg0] => translateHighType typeArg0
          | _, _ => TransM.error s!"Variable {name} requires explicit type"
        | _ => TransM.error s!"Variable {name} requires explicit type"
      let value ← match assignArg with
        | .option _ (some (.op assignOp)) => match assignOp.args with
          | #[assignArg0] => translateStmtExpr assignArg0 >>= (pure ∘ some)
          | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
        | .option _ none => pure none
        | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
      return mkStmtExprMd (.LocalVariable name varType value) src
    | q`Laurel.identifier, #[arg0] =>
      let name ← translateIdent arg0
      return mkStmtExprMd (.Identifier name) src
    | q`Laurel.parenthesis, #[arg0] => translateStmtExpr arg0
    | q`Laurel.assign, #[arg0, arg1] =>
      let target ← translateStmtExpr arg0
      let value ← translateStmtExpr arg1
      return mkStmtExprMd (.Assign [target] value) src
    | q`Laurel.new, #[nameArg] =>
      let name ← translateIdent nameArg
      return mkStmtExprMd (.New name) src
    | q`Laurel.isType, #[targetArg, typeNameArg] =>
      let target ← translateStmtExpr targetArg
      let typeName ← translateIdent typeNameArg
      return mkStmtExprMd (.IsType target (mkHighTypeMd (.UserDefined typeName) src)) src
    | q`Laurel.asType, #[targetArg, typeNameArg] =>
      let target ← translateStmtExpr targetArg
      let typeName ← translateIdent typeNameArg
      return mkStmtExprMd (.AsType target (mkHighTypeMd (.UserDefined typeName) src)) src
    | q`Laurel.call, #[arg0, argsSeq] =>
      let callee ← translateStmtExpr arg0
      let calleeName := match callee.val with
        | .Identifier name => name
        | _ => ""
      let argsList ← match argsSeq with
        | .seq _ .comma args => args.toList.mapM translateStmtExpr
        | _ => pure []
      return mkStmtExprMd (.StaticCall calleeName argsList) src
    | q`Laurel.return, #[arg0] =>
      let value ← translateStmtExpr arg0
      return mkStmtExprMd (.Return (some value)) src
    | q`Laurel.ifThenElse, #[arg0, arg1, elseArg] =>
      let cond ← translateStmtExpr arg0
      let thenBranch ← translateStmtExpr arg1
      let elseBranch ← match elseArg with
        | .option _ (some (.op elseOp)) => match elseOp.name, elseOp.args with
          | q`Laurel.elseBranch, #[elseArg0] => translateStmtExpr elseArg0 >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.IfThenElse cond thenBranch elseBranch) src
    | q`Laurel.fieldAccess, #[objArg, fieldArg] =>
      let obj ← translateStmtExpr objArg
      let field ← translateIdent fieldArg
      let fieldSrc ← getArgFileRange fieldArg
      return mkStmtExprMd (.FieldSelect obj field) fieldSrc
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
      return mkStmtExprMd (.While cond invariants none body) src
    | q`Laurel.forLoop, #[initArg, condArg, stepArg, invSeqArg, bodyArg] =>
      let init ← translateStmtExpr initArg
      let cond ← translateStmtExpr condArg
      let step ← translateStmtExpr stepArg
      let invariants ← match invSeqArg with
        | .seq _ _ clauses => clauses.toList.mapM fun arg => match arg with
            | .op invOp => match invOp.name, invOp.args with
              | q`Laurel.invariantClause, #[exprArg] => translateStmtExpr exprArg
              | _, _ => TransM.error "Expected invariantClause"
            | _ => TransM.error "Expected operation"
        | _ => pure []
      let body ← translateStmtExpr bodyArg
      let whileBody := mkStmtExprMd (.Block [body, step] none) src
      let whileStmt := mkStmtExprMd (.While cond invariants none whileBody) src
      return mkStmtExprMd (.Block [init, whileStmt] none) src
    | q`Laurel.forallExpr, #[nameArg, tyArg, triggerArg, bodyArg] =>
      let name ← translateIdent nameArg
      let ty ← translateHighType tyArg
      let trigger ← match triggerArg with
        | .option _ (some (.op triggerOp)) => match triggerOp.name, triggerOp.args with
          | q`Laurel.trigger, #[triggerExprArg] =>
            translateStmtExpr triggerExprArg >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.Quantifier .Forall { name := name, type := ty } trigger body) src
    | q`Laurel.existsExpr, #[nameArg, tyArg, triggerArg, bodyArg] =>
      let name ← translateIdent nameArg
      let ty ← translateHighType tyArg
      let trigger ← match triggerArg with
        | .option _ (some (.op triggerOp)) => match triggerOp.name, triggerOp.args with
          | q`Laurel.trigger, #[triggerExprArg] =>
            translateStmtExpr triggerExprArg >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.Quantifier .Exists { name := name, type := ty } trigger body) src
    | q`Laurel.seqLiteral, #[elementsSeq] =>
      let elements ← match elementsSeq with
        | .seq _ .comma args => args.toList.mapM translateStmtExpr
        | _ => pure []
      let empty := mkStmtExprMd (.StaticCall (mkId SeqOp.empty) []) src
      return elements.foldl (fun acc e => mkStmtExprMd (.StaticCall (mkId SeqOp.build) [acc, e]) src) empty
    | q`Laurel.subscript, #[targetArg, indexArg, updateArg] =>
      let target ← translateStmtExpr targetArg
      let index ← translateStmtExpr indexArg
      let update ← match updateArg with
        | .option _ (some (.op updateOp)) => match updateOp.name, updateOp.args with
          | q`Laurel.seqUpdateValue, #[valArg] => some <$> translateStmtExpr valArg
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.Subscript target index update) src
    | _, #[arg0] => match getUnaryOp? op.name with
      | some primOp =>
        let inner ← translateStmtExpr arg0
        return mkStmtExprMd (.PrimitiveOp primOp [inner]) src
      | none => TransM.error s!"Unknown unary operation: {op.name}"
    | _, #[arg0, arg1] => match getBinaryOp? op.name with
      | some primOp =>
        let lhs ← translateStmtExpr arg0
        let rhs ← translateStmtExpr arg1
        return mkStmtExprMd (.PrimitiveOp primOp [lhs, rhs]) src
      | none => TransM.error s!"Unknown operation: {op.name}"
    | _, _ => TransM.error s!"Unknown operation: {op.name}"
  | _ => TransM.error s!"translateStmtExpr expects operation"

partial def translateSeqCommand (arg : Arg) : TransM (List StmtExprMd) := do
  let .seq _ _ args := arg
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
        | q`Laurel.modifiesWildcard, #[] =>
          let src ← match (← get).uri with
            | some uri => pure (some (SourceRange.toFileRange uri clauseOp.ann))
            | none => pure none
          allModifies := allModifies ++ [mkStmtExprMd .All src]
        | _, _ => TransM.error s!"Expected modifiesClause operation, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected modifiesClause operation in modifies sequence"
    pure allModifies
  | _ => pure []

def translateRequiresClauses (arg : Arg) : TransM (List Condition) := do
  match arg with
  | .seq _ _ args => do
    let mut allRequires : List Condition := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp => match clauseOp.name, clauseOp.args with
        | q`Laurel.requiresClause, #[exprArg, errMsgArg] =>
          let expr ← translateStmtExpr exprArg
          let summary ← match errMsgArg with
            | .option _ (some (.op errOp)) => match errOp.name, errOp.args with
              | q`Laurel.errorSummary, #[strArg] => do
                let msg ← translateString strArg
                pure (some msg)
              | _, _ => pure none
            | _ => pure none
          allRequires := allRequires ++ [{ condition := expr, summary }]
        | _, _ => TransM.error s!"Expected requiresClause operation, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected requiresClause operation in requires sequence"
    pure allRequires
  | _ => pure []

def translateEnsuresClauses (arg : Arg) : TransM (List Condition) := do
  match arg with
  | .seq _ _ args => do
    let mut allEnsures : List Condition := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp => match clauseOp.name, clauseOp.args with
        | q`Laurel.ensuresClause, #[exprArg, errMsgArg] =>
          let expr ← translateStmtExpr exprArg
          let summary ← match errMsgArg with
            | .option _ (some (.op errOp)) => match errOp.name, errOp.args with
              | q`Laurel.errorSummary, #[strArg] => do
                let msg ← translateString strArg
                pure (some msg)
              | _, _ => pure none
            | _ => pure none
          allEnsures := allEnsures ++ [{ condition := expr, summary }]
        | _, _ => TransM.error s!"Expected ensuresClause operation, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected ensuresClause operation in ensures sequence"
    pure allEnsures
  | _ => pure []

def parseProcedure (arg : Arg) : TransM Procedure := do
  let .op op := arg
    | TransM.error s!"parseProcedure expects operation"

  match op.name, op.args with
  | q`Laurel.procedure, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
      requiresArg, invokeOnArg, opaqueSpecArg, bodyArg]
  | q`Laurel.function, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
      requiresArg, invokeOnArg, opaqueSpecArg, bodyArg] =>
    let name ← translateIdent nameArg
    let parameters ← translateParameters paramArg
    -- Either returnTypeArg or returnParamsArg may have a value, not both
    -- If returnTypeArg is set, create a single "result" parameter
    let returnParameters ← match returnTypeArg with
      | .option _ (some (.op returnTypeOp)) => match returnTypeOp.name, returnTypeOp.args with
        | q`Laurel.returnType, #[typeArg] =>
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
    -- Parse preconditions (requires clauses - zero or more)
    let preconditions ← translateRequiresClauses requiresArg
    -- Parse optional invokeOn clause
    let invokeOn ← match invokeOnArg with
      | .option _ (some (.op invokeOnOp)) => match invokeOnOp.name, invokeOnOp.args with
        | q`Laurel.invokeOnClause, #[triggerExprArg] =>
          translateStmtExpr triggerExprArg >>= (pure ∘ some)
        | _, _ => TransM.error s!"Expected invokeOnClause operation, got {repr invokeOnOp.name}"
      | .option _ none => pure none
      | _ => pure none
    -- Parse optional opaqueSpec (contains ensures and modifies)
    let (isOpaque, postconditions, modifies) ← match opaqueSpecArg with
      | .option _ (some (.op opaqueSpecOp)) => match opaqueSpecOp.name, opaqueSpecOp.args with
        | q`Laurel.opaqueSpec, #[ensuresArg, modifiesArg] =>
          let postconditions ← translateEnsuresClauses ensuresArg
          let modifies ← translateModifiesClauses modifiesArg
          pure (true, postconditions, modifies)
        | _, _ => TransM.error s!"Expected opaqueSpec operation, got {repr opaqueSpecOp.name}"
      | .option _ none => pure (false, [], [])
      | _ => pure (false, [], [])
    -- Parse optional body
    let isExternal ← match bodyArg with
      | .option _ (some (.op bodyOp)) => match bodyOp.name, bodyOp.args with
        | q`Laurel.externalBody, #[] => pure true
        | _, _ => pure false
      | _ => pure false
    let body ← match bodyArg with
      | .option _ (some (.op bodyOp)) => match bodyOp.name, bodyOp.args with
        | q`Laurel.body, #[exprArg] => translateCommand exprArg >>= (pure ∘ some)
        | q`Laurel.externalBody, #[] => pure none
        | _, _ => TransM.error s!"Expected body or externalBody operation, got {repr bodyOp.name}"
      | .option _ none => pure none
      | _ => TransM.error s!"Expected body, got {repr bodyArg}"
    -- Determine procedure body kind
    let procBody :=
      if isExternal then Body.External
      else if isOpaque then Body.Opaque postconditions body modifies
      else match body with
      | some b => Body.Transparent b
      | none => Body.Opaque [] none modifies
    return {
      name := name
      inputs := parameters
      outputs := returnParameters
      preconditions := preconditions
      decreases := none
      isFunctional := op.name == q`Laurel.function
      invokeOn := invokeOn
      body := procBody
    }
  | q`Laurel.procedure, args
  | q`Laurel.function, args =>
    TransM.error s!"parseProcedure expects 8 arguments, got {args.size}"
  | _, _ =>
    TransM.error s!"parseProcedure expects procedure or function, got {repr op.name}"

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
  | q`Laurel.composite, #[nameArg, extendsArg, fieldsArg, procsArg] =>
    let name ← translateIdent nameArg
    let extending ← match extendsArg with
      | .option _ (some (.op extendsOp)) => match extendsOp.name, extendsOp.args with
        | q`Laurel.extends, #[parentsArg] =>
          match parentsArg with
          | .seq _ .comma args => args.toList.mapM translateIdent
          | singleArg => do let parent ← translateIdent singleArg; pure [parent]
        | _, _ => TransM.error s!"Expected optionalExtends operation, got {repr extendsOp.name}"
      | .option _ none => pure []
      | _ => TransM.error s!"Expected optionalExtends, got {repr extendsArg}"
    let fields ← match fieldsArg with
      | .seq _ _ args => args.toList.mapM parseField
      | _ => pure []
    let instanceProcedures ← match procsArg with
      | .seq _ _ args => args.toList.mapM parseProcedure
      | _ => pure []
    return .Composite { name := name, extending := extending, fields := fields, instanceProcedures := instanceProcedures }
  | _, _ =>
    TransM.error s!"parseComposite expects composite, got {repr op.name}"

def parseDatatypeConstructorArg (arg : Arg) : TransM Parameter := do
  let .op op := arg
    | TransM.error s!"parseDatatypeConstructorArg expects operation"
  match op.name, op.args with
  | q`Laurel.datatypeConstructorArg, #[nameArg, typeArg] =>
    let name ← translateIdent nameArg
    let argType ← translateHighType typeArg
    return { name := name, type := argType }
  | _, _ =>
    TransM.error s!"parseDatatypeConstructorArg expects datatypeConstructorArg, got {repr op.name}"

def parseDatatypeConstructor (arg : Arg) : TransM DatatypeConstructor := do
  let .op op := arg
    | TransM.error s!"parseDatatypeConstructor expects operation"
  match op.name, op.args with
  | q`Laurel.datatypeConstructor, #[nameArg, argsSeq] =>
    let name ← translateIdent nameArg
    let args ← match argsSeq with
      | .seq _ .comma args => args.toList.mapM parseDatatypeConstructorArg
      | _ => pure []
    return { name := name, args := args }
  | q`Laurel.datatypeConstructorNoArgs, #[nameArg] =>
    let name ← translateIdent nameArg
    return { name := name, args := [] }
  | _, _ =>
    TransM.error s!"parseDatatypeConstructor expects datatypeConstructor, got {repr op.name}"

def parseDatatype (arg : Arg) : TransM TypeDefinition := do
  let .op op := arg
    | TransM.error s!"parseDatatype expects operation"
  match op.name, op.args with
  | q`Laurel.datatype, #[nameArg, constructorsArg] =>
    let name ← translateIdent nameArg
    let constructors ← match constructorsArg with
      | .op listOp => match listOp.name, listOp.args with
        | q`Laurel.datatypeConstructorList, #[csArg] =>
          match csArg with
          | .seq _ .comma args => args.toList.mapM parseDatatypeConstructor
          | singleArg => do let c ← parseDatatypeConstructor singleArg; pure [c]
        | _, _ => TransM.error s!"Expected datatypeConstructorList, got {repr listOp.name}"
      | _ => TransM.error s!"Expected datatypeConstructorList operation"
    return .Datatype { name := name, typeArgs := [], constructors := constructors }
  | _, _ =>
    TransM.error s!"parseDatatype expects datatype, got {repr op.name}"

def parseOpaqueType (arg : Arg) : TransM TypeDefinition := do
  let .op op := arg
    | TransM.error s!"parseOpaqueType expects operation"
  match op.name, op.args with
  | q`Laurel.opaqueType, #[nameArg] =>
    let name ← translateIdent nameArg
    return .Datatype { name := name, typeArgs := [], constructors := [] }
  | _, _ =>
    TransM.error s!"parseOpaqueType expects opaqueType, got {repr op.name}"

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

def parseTopLevel (arg : Arg) : TransM (Option Procedure × Option TypeDefinition) := do
  let .op op := arg
    | TransM.error s!"parseTopLevel expects operation"

  match op.name, op.args with
  | q`Laurel.procedureCommand, #[procArg] =>
    let proc ← parseProcedure procArg
    return (some proc, none)
  | q`Laurel.compositeCommand, #[compositeArg] =>
    let typeDef ← parseComposite compositeArg
    return (none, some typeDef)
  | q`Laurel.datatypeCommand, #[datatypeArg] =>
    let typeDef ← parseDatatype datatypeArg
    return (none, some typeDef)
  | q`Laurel.constrainedTypeCommand, #[ctArg] =>
    let ct ← parseConstrainedType ctArg
    return (none, some (.Constrained ct))
  | _, _ =>
    TransM.error s!"parseTopLevel expects procedureCommand, compositeCommand, or datatypeCommand, got {repr op.name}"

/--
Translate concrete Laurel syntax into abstract Laurel syntax
-/
def parseProgram (prog : Strata.Program) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []
  for op in prog.commands do
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

end

end Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelCheck
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Core.Verifier
import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.CorePrelude
import Strata.Languages.Core.Program

/-!
# Python to Laurel Translation

This module translates Python AST to Laurel intermediate representation.

## Design Goals
- Support fully type-annotated Python functions
- Start with heap-free programs (no classes/objects initially)
- Incremental feature addition

## Current Limitations
- No heap operations (classes, objects, fields)
- No collections (lists, dicts, sets)
- No exceptions
- No imports
- No function calls (initially)
- Basic control flow only (if/while/return)
-/

namespace Strata.Python

open Laurel

/-! ## Translation Context

The translation context tracks information needed during translation:
- Variable types (from type annotations)
- Function signatures (for call resolution)
- Current scope information
-/

structure CoreProcedureSignature where
  inputs : List String
  outputs : List String
deriving Inhabited

inductive UnmodeledFunctionBehavior where
  | havocOutputs
  | havocInputsAndOutputs
deriving Inhabited

structure TranslationContext where
  /-- Map from variable names to their Laurel types -/
  variableTypes : List (String × HighTypeMd) := []
  /-- Map from function names to their signatures -/
  functionSignatures : List (String × Procedure) := []
  /-- Map from prelude procedure names to their full signatures -/
  preludeProcedures : List (String × CoreProcedureSignature) := []
  /-- Names of user-defined functions -/
  userFunctions : List String := []
  /-- Names of prelude types -/
  preludeTypes : List String := []
  /-- Behavior for unmodeled functions -/
  unmodeledBehavior : UnmodeledFunctionBehavior := .havocOutputs
  /-- List of defined composite types -/
  compositeTypes : List CompositeType := []
  /-- Track current class during method translation -/
  currentClassName : Option String := none   -- Track current class during method translation
deriving Inhabited

/-! ## Error Handling -/

/-- Translation errors with context -/
inductive TranslationError where
  | unsupportedConstruct (msg : String) (pyAst : String)
  | typeError (msg : String)
  | nameError (name : String)
  | internalError (msg : String)
deriving Repr

def TranslationError.toString : TranslationError → String
  | .unsupportedConstruct msg ast => s!"Unsupported construct: {msg}\nAST: {ast}"
  | .typeError msg => s!"Type error: {msg}"
  | .nameError name => s!"Name not found: {name}"
  | .internalError msg => s!"Internal error: {msg}"

instance : ToString TranslationError where
  toString := TranslationError.toString

/-! ## Helper Functions -/

/-- Create default metadata for Laurel AST nodes -/
def defaultMetadata : Imperative.MetaData Core.Expression :=
  let fileRangeElt := ⟨ Imperative.MetaDataElem.Field.label "fileRange", .fileRange ⟨ ⟨"foo"⟩ , 0, 0 ⟩ ⟩
  #[fileRangeElt]

/-- Create a HighTypeMd with default metadata -/
def mkHighTypeMd (ty : HighType) : HighTypeMd :=
  { val := ty, md := defaultMetadata }

def mkCoreType (s: String): HighTypeMd :=
  {val := .TCore s , md := defaultMetadata}

/-- Create a StmtExprMd with default metadata -/
def mkStmtExprMd (expr : StmtExpr) : StmtExprMd :=
  { val := expr, md := defaultMetadata }

/-- Extract string representation from Python expression (for type annotations) -/
partial def pyExprToString (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Constant _ (.ConString _ s) _ => s.val
  | .Subscript _ val slice _ =>
    let base := pyExprToString val
    let arg := pyExprToString slice
    s!"{base}[{arg}]"
  | .Attribute _ val attr _ =>
    let base := pyExprToString val
    s!"{base}_{attr.val}"
  | .Tuple _ elts _ =>
    let args := elts.val.toList.map pyExprToString
    String.intercalate ", " args
  | _ => "<unknown>"

/-- Map Python type strings to Core type names -/
def pythonTypeToCoreType (typeStr : String) : Option String :=
  match typeStr with
  | "Dict[str, Any]" => some "DictStrAny"
  | "List[str]" => some "ListStr"
  | _ => none

/-- Translate Python type annotation to Laurel HighType -/
def translateType (ctx : TranslationContext) (typeStr : String) : Except TranslationError HighTypeMd :=
  match typeStr with
  | "int" => .ok (mkHighTypeMd HighType.TInt)
  | "bool" => .ok (mkHighTypeMd HighType.TBool)
  | "str" => .ok (mkHighTypeMd HighType.TString)
  | _ =>
    -- Check if it's a Python type that maps to Core
    match pythonTypeToCoreType typeStr with
    | some coreType => .ok (mkCoreType coreType)
    | none =>
      -- Check if it's a prelude type
      if ctx.preludeTypes.contains typeStr then
        .ok (mkCoreType typeStr)
      else
      -- check here
        .ok (mkHighTypeMd (HighType.UserDefined typeStr))

/-- Create a None value for a given OrNone type -/
def mkNoneForType (typeName : String) : StmtExprMd :=
  -- First construct None_none(), then wrap it in the appropriate OrNone constructor
  let noneVal := mkStmtExprMd (StmtExpr.StaticCall "None_none" [])
  mkStmtExprMd (StmtExpr.StaticCall s!"{typeName}_mk_none" [noneVal])

/-! ## Expression Translation -/

/-- Check if a function has a model (is in prelude or user-defined) -/
def hasModel (ctx : TranslationContext) (funcName : String) : Bool :=
  ctx.preludeProcedures.any (·.1 == funcName) || ctx.userFunctions.contains funcName

mutual

/-- Translate Python expression to Laurel StmtExpr -/
partial def translateExpr (ctx : TranslationContext) (e : Python.expr SourceRange)
    : Except TranslationError StmtExprMd := do
  match e with
  -- Integer literals
  | .Constant _ (.ConPos _ n) _ =>
    return mkStmtExprMd (StmtExpr.LiteralInt n.val)

  | .Constant _ (.ConNeg _ n) _ =>
    return mkStmtExprMd (StmtExpr.LiteralInt (-n.val))

  -- String literals
  | .Constant _ (.ConString _ s) _ =>
    return mkStmtExprMd (StmtExpr.LiteralString s.val)

  -- Boolean literals
  | .Constant _ (.ConTrue _) _ =>
    return mkStmtExprMd (StmtExpr.LiteralBool true)

  | .Constant _ (.ConFalse _) _ =>
    return mkStmtExprMd (StmtExpr.LiteralBool false)

  -- Variable references
  | .Name _ name _ =>
    return mkStmtExprMd (StmtExpr.Identifier name.val)

  -- Binary operations
  | .BinOp _ left op right => do
    let leftExpr ← translateExpr ctx left
    let rightExpr ← translateExpr ctx right
    let laurelOp ← match op with
      -- Arithmetic
      | .Add _ =>
        let typeEnv : Laurel.TypeEnv := ctx.variableTypes
        let tString : Laurel.HighTypeMd := { val := .TString, md := default }
        if Laurel.check typeEnv leftExpr tString && Laurel.check typeEnv rightExpr tString then .ok Operation.StrConcat else .ok Operation.Add
      | .Sub _ => .ok Operation.Sub
      | .Mult _ => .ok Operation.Mul
      | .FloorDiv _ => .ok Operation.Div  -- Python // maps to Laurel Div
      | .Mod _ => .ok Operation.Mod
      -- Unsupported for now
      | _ => throw (.unsupportedConstruct s!"Binary operator not yet supported: {repr op}" (toString (repr e)))
    return mkStmtExprMd (StmtExpr.PrimitiveOp laurelOp [leftExpr, rightExpr])

  -- Comparison operations
  | .Compare _ left ops comparators => do
    -- Python allows chained comparisons: a < b < c
    -- For now, only support single comparison
    if ops.val.size != 1 || comparators.val.size != 1 then
      throw (.unsupportedConstruct "Chained comparisons not yet supported" (toString (repr e)))
    let leftExpr ← translateExpr ctx left
    let rightExpr ← translateExpr ctx comparators.val[0]!
    let laurelOp ← match ops.val[0]! with
      | .Eq _ => .ok Operation.Eq
      | .NotEq _ => .ok Operation.Neq
      | .Lt _ => .ok Operation.Lt
      | .LtE _ => .ok Operation.Leq
      | .Gt _ => .ok Operation.Gt
      | .GtE _ => .ok Operation.Geq
      | _ => throw (.unsupportedConstruct s!"Comparison operator not yet supported: {repr ops.val[0]!}" (toString (repr e)))
    return mkStmtExprMd (StmtExpr.PrimitiveOp laurelOp [leftExpr, rightExpr])

  -- Boolean operations
  | .BoolOp _ op values => do
    if values.val.size < 2 then
      throw (.internalError "BoolOp must have at least 2 operands")
    let laurelOp ← match op with
      | .And _ => .ok Operation.And
      | .Or _ => .ok Operation.Or
    -- Translate all operands
    let mut exprs : List StmtExprMd := []
    for val in values.val do
      let expr ← translateExpr ctx val
      exprs := exprs ++ [expr]
    -- Chain binary operations: a && b && c becomes (a && b) && c
    let mut result := exprs[0]!
    for i in [1:exprs.length] do
      result := mkStmtExprMd (StmtExpr.PrimitiveOp laurelOp [result, exprs[i]!])
    return result

  -- Unary operations
  | .UnaryOp _ op operand => do
    let operandExpr ← translateExpr ctx operand
    let laurelOp ← match op with
      | .Not _ => .ok Operation.Not
      | .USub _ => .ok Operation.Neg
      | _ => throw (.unsupportedConstruct s!"Unary operator not yet supported: {repr op}" (toString (repr e)))
    return mkStmtExprMd (StmtExpr.PrimitiveOp laurelOp [operandExpr])

  -- JoinedStr (f-strings) - return first part until we have string concat
  | .JoinedStr _ values =>
    if values.val.isEmpty then
      return mkStmtExprMd (StmtExpr.LiteralString "")
    else
      let first ← translateExpr ctx values.val[0]!
      return first

  | .Call _ f args _kwargs => translateCall ctx (pyExprToString f) args.val.toList

  -- Field access: self.x or obj.field
  | .Attribute _ obj attr _ => do
    -- Check if this is self.field access
    match obj with
    | .Name _ name _ =>
      if name.val == "self" && ctx.currentClassName.isSome then
        -- self.field in a method - translate to field access
        return mkStmtExprMd (StmtExpr.FieldSelect
          (mkStmtExprMd (StmtExpr.Identifier "self"))
          attr.val)
      else
        -- Regular object.field access
        let objExpr ← translateExpr ctx obj
        return mkStmtExprMd (StmtExpr.FieldSelect objExpr attr.val)
    | _ =>
      let objExpr ← translateExpr ctx obj
      return mkStmtExprMd (StmtExpr.FieldSelect objExpr attr.val)

  | _ => throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr e)))

/-- Translate function call, filling in optional arguments with None if needed -/
partial def translateCall (ctx : TranslationContext) (funcName : String) (args : List (Python.expr SourceRange))
    : Except TranslationError StmtExprMd := do
  let mut translatedArgs ← args.mapM (translateExpr ctx)

  -- Check if function has a model
  if !hasModel ctx funcName then
    -- Unmodeled function - use Hole
    return mkStmtExprMd .Hole

  -- Check if this is a prelude procedure and fill in optional args
  if let some sig := ctx.preludeProcedures.lookup funcName then
    let numProvided := translatedArgs.length
    let numExpected := sig.inputs.length

    if numProvided < numExpected then
      -- Fill remaining args with None of the appropriate type
      for i in [numProvided:numExpected] do
        let paramType := sig.inputs[i]!
        translatedArgs := translatedArgs ++ [mkNoneForType paramType]

    if sig.outputs.length > 0 then
      let call := mkStmtExprMd (StmtExpr.StaticCall funcName translatedArgs)
      return mkStmtExprMd (.Assign [mkStmtExprMd (.Identifier "maybe_except")] call)
  -- Check if this is a user function and fill in optional args
  else if let some proc := ctx.functionSignatures.lookup funcName then
    let numProvided := translatedArgs.length
    let numExpected := proc.inputs.length

    if numProvided < numExpected then
      -- Fill remaining args with None - extract type name from HighTypeMd
      for i in [numProvided:numExpected] do
        if h : i < proc.inputs.length then
          let paramType := proc.inputs[i].type
          -- Extract the base type name for mkNoneForType
          let typeName := match paramType.val with
            | HighType.TCore name => name
            | HighType.UserDefined name => name
            | _ => "Unknown"  -- Fallback, shouldn't happen for optional params
          translatedArgs := translatedArgs ++ [mkNoneForType typeName]

  return mkStmtExprMd (StmtExpr.StaticCall funcName translatedArgs)

end

/-! ## Statement Translation

Translate Python statements to Laurel StmtExpr nodes.
These functions are mutually recursive.
-/

mutual

partial def translateStmt (ctx : TranslationContext) (s : Python.stmt SourceRange)
    : Except TranslationError (TranslationContext × StmtExprMd) := do
  match s with
  -- Assignment: x = expr
  | .Assign _ targets value _ => do
    -- For now, only support single target
    if targets.val.size != 1 then
      throw (.unsupportedConstruct "Multiple assignment targets not yet supported" (toString (repr s)))
    let target ← match targets.val[0]! with
      | .Name _ name _ => .ok name.val
      | _ => throw (.unsupportedConstruct "Only simple variable assignment supported" (toString (repr s)))
    let valueExpr ← translateExpr ctx value
    let targetExpr := mkStmtExprMd (StmtExpr.Identifier target)
    let assignStmt := mkStmtExprMd (StmtExpr.Assign [targetExpr] valueExpr)
    return (ctx, assignStmt)

  -- Annotated assignment: x: int = expr or x: ClassName = ClassName(args) or self.field: int = expr
  | .AnnAssign _ target annotation value _ => do
    -- Check if this is a field assignment (self.field)
    match target with
    | .Attribute _ obj attr _ =>
      match obj with
      | .Name _ name _ =>
        if name.val == "self" && ctx.currentClassName.isSome then
          -- This is self.field = value in a method
          match value.val with
          | some initExpr => do
            let initVal ← translateExpr ctx initExpr
            let fieldAccess := mkStmtExprMd (StmtExpr.FieldSelect
              (mkStmtExprMd StmtExpr.This)
              attr.val)
            let assignStmt := mkStmtExprMd (StmtExpr.Assign [fieldAccess] initVal)
            return (ctx, assignStmt)
          | none =>
            throw (.unsupportedConstruct "Field declaration without initializer not supported" (toString (repr s)))
        else
          throw (.unsupportedConstruct "Only self.field assignments supported in methods" (toString (repr s)))
      | _ => throw (.unsupportedConstruct "Only simple field access supported" (toString (repr s)))
    | .Name _ name _ =>
      -- Regular variable assignment
      let varName := name.val
      let typeStr := pyExprToString annotation
      let varType ← translateType ctx typeStr
      let newCtx := { ctx with variableTypes := ctx.variableTypes ++ [(varName, varType)] }

      -- Check if this is a class constructor call
      match value.val with
      | some (.Call _ f args _) =>
        let funcName := pyExprToString f
        if ctx.compositeTypes.any (fun ct => ct.name == funcName) then
          -- This is: var x: ClassName = ClassName(args)
          -- Translate constructor arguments
          let translatedArgs ← args.val.toList.mapM (translateExpr ctx)

          -- Generate: var a: C; call a.__init__(args);
          let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType none)

          let initCall := mkStmtExprMd (StmtExpr.InstanceCall
            (mkStmtExprMd (StmtExpr.Identifier varName))
            "__init__"
            translatedArgs)

          let blockStmt := mkStmtExprMd (StmtExpr.Block [declStmt, initCall] none)

          return (newCtx, blockStmt)
        else
          -- Regular annotated assignment with call initializer
          let initVal ← translateCall ctx funcName args.val.toList
          let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType (some initVal))
          return (newCtx, declStmt)
      | some initExpr => do
        -- Regular annotated assignment with initializer
        let initVal ← translateExpr newCtx initExpr
        let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType (some initVal))
        return (newCtx, declStmt)
      | none =>
        -- Declaration without initializer
        let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType none)
        return (newCtx, declStmt)
    | _ => throw (.unsupportedConstruct "Only simple variable or field annotation supported" (toString (repr s)))

  -- If statement
  | .If _ test body orelse => do
    let condExpr ← translateExpr ctx test
    -- Translate body (list of statements)
    let (bodyCtx, bodyStmts) ← translateStmtList ctx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    -- Translate else branch if present
    let elseBlock ← if orelse.val.isEmpty then
      .ok none
    else do
      let (_, elseStmts) ← translateStmtList bodyCtx orelse.val.toList
      .ok (some (mkStmtExprMd (StmtExpr.Block elseStmts none)))
    let ifStmt := mkStmtExprMd (StmtExpr.IfThenElse condExpr bodyBlock elseBlock)
    return (bodyCtx, ifStmt)

  -- While loop
  | .While _ test body _orelse => do
    -- Note: Python while-else not supported yet
    let condExpr ← translateExpr ctx test
    let (loopCtx, bodyStmts) ← translateStmtList ctx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    let whileStmt := mkStmtExprMd (StmtExpr.While condExpr [] none bodyBlock)
    return (loopCtx, whileStmt)

  -- Return statement
  | .Return _ value => do
    let retVal ← match value.val with
      | some expr => do
        let e ← translateExpr ctx expr
        .ok (some e)
      | none => .ok none
    let retStmt := mkStmtExprMd (StmtExpr.Return retVal)
    return (ctx, retStmt)

  -- Assert statement
  | .Assert _ test msg => do
    let condExpr ← translateExpr ctx test
    let label := msg.val.bind fun expr =>
    match expr with
    | .Constant _ (.ConString _ s) _ => some s.val
    | _ => none
    let assertStmt := mkStmtExprMd (StmtExpr.Assert condExpr label)
    return (ctx, assertStmt)

  -- Expression statement (e.g., function call)
  | .Expr _ value => do
    let expr ← translateExpr ctx value
    return (ctx, expr)

  | .Import _ _ | .ImportFrom _ _ _ _ => return (ctx, mkStmtExprMd .Hole)

  -- Try/except - wrap body with exception checks and handlers
  | .Try _ body handlers _ _ => do
    let tryLabel := "try_end"
    let handlerLabel := "exception_handlers"

    -- Translate try body
    let (bodyCtx, bodyStmts) ← translateStmtList ctx body.val.toList

    -- Insert exception checks after each statement in try body
    let bodyStmtsWithChecks := bodyStmts.flatMap fun stmt =>
      -- Check if maybe_except is an exception and exit to handlers if so
      let isException := mkStmtExprMd (StmtExpr.StaticCall "ExceptOrNone..isExceptOrNone_mk_code"
        [mkStmtExprMd (StmtExpr.Identifier "maybe_except")])
      let exitToHandler := mkStmtExprMd (StmtExpr.IfThenElse isException
        (mkStmtExprMd (StmtExpr.Exit handlerLabel)) none)
      [stmt, exitToHandler]

    -- Translate exception handlers
    let mut handlerStmts : List StmtExprMd := []
    for handler in handlers.val do
      match handler with
      | .ExceptHandler _ _ _ handlerBody =>
        let (_, hStmts) ← translateStmtList bodyCtx handlerBody.val.toList
        handlerStmts := handlerStmts ++ hStmts

    -- Create handler block
    let handlerBlock := mkStmtExprMd (StmtExpr.Block handlerStmts (some handlerLabel))

    -- Wrap in try block
    let tryBlock := mkStmtExprMd (StmtExpr.Block (bodyStmtsWithChecks ++ [handlerBlock]) (some tryLabel))
    return (bodyCtx, tryBlock)

  | .Raise _ _ _ => return (ctx, mkStmtExprMd .Hole)

  | _ => throw (.unsupportedConstruct "Statement type not yet supported" (toString (repr s)))

partial def translateStmtList (ctx : TranslationContext) (stmts : List (Python.stmt SourceRange))
    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let mut currentCtx := ctx
  let mut result : List StmtExprMd := []
  for stmt in stmts do
    let (newCtx, laurelStmt) ← translateStmt currentCtx stmt
    currentCtx := newCtx
    result := result ++ [laurelStmt]
  return (currentCtx, result)

end

def prependExceptHandlingHelper (l: List StmtExprMd) : List StmtExprMd :=
  mkStmtExprMd (.LocalVariable "maybe_except" (mkCoreType "ExceptOrNone") none) :: l

/-- Translate Python function to Laurel Procedure -/
def translateFunction (ctx : TranslationContext) (f : Python.stmt SourceRange)
    : Except TranslationError Laurel.Procedure := do
  match f with
  | .FunctionDef _ name args body _decorator_list returns _type_comment _ => do
    -- Extract function name
    let funcName := name.val

    -- Translate parameters
    let mut inputs : List Parameter := []
    let mut localCtx := ctx

    -- Process regular arguments - args is a constructor, need to extract the args field
    match args with
    | .mk_arguments _ _ argsList _ _ _ _ _ =>
      for arg in argsList.val do
        match arg with
        | .mk_arg _ paramName paramAnnotation _ =>
          let paramTypeStr ← match paramAnnotation.val with
            | some typeExpr => .ok (pyExprToString typeExpr)
            | none => throw (.typeError s!"Parameter {paramName.val} must have type annotation")
          let paramType ← translateType ctx paramTypeStr
          inputs := inputs ++ [{ name := paramName.val, type := paramType }]
          localCtx := { localCtx with variableTypes := localCtx.variableTypes ++ [(paramName.val, paramType)] }

    -- Translate return type
    let returnType ← match returns.val with
      | some retExpr => translateType ctx (pyExprToString retExpr)
      | none => .ok (mkHighTypeMd HighType.TVoid)

    -- Determine outputs based on return type
    let outputs : List Parameter :=
      match returnType.val with
      | HighType.TVoid => []
      | _ => [{ name := "result", type := returnType }]

    -- Translate function body
    let (_, bodyStmts) ← translateStmtList localCtx body.val.toList
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    -- Create procedure with transparent body (no contracts for now)
    let proc : Procedure := {
      name := funcName
      inputs := inputs
      outputs := outputs
      preconditions := []
      decreases := none
      body := Body.Transparent bodyBlock
    }

    return proc

  | _ => throw (.internalError "Expected FunctionDef")

/-- Extract type name from LMonoTy -/
def getTypeName (ty : Lambda.LMonoTy) : String :=
  match ty with
  | .tcons name _ => name
  | .ftvar name => name
  | .bitvec n => s!"bv{n}"

/-- Extract type names from a Core program -/
def extractPreludeTypes (prelude : Core.Program) : List String :=
  prelude.decls.flatMap fun decl =>
    match decl with
    | .type (.con tc) _ => [tc.name]
    | .type (.syn ts) _ => [ts.name]
    | .type (.data dts) _ => dts.map (·.name)
    | _ => []

/-- Extract procedure signatures from a Core program -/
def extractPreludeProcedures (prelude : Core.Program) : List (String × CoreProcedureSignature) :=
  prelude.decls.filterMap fun decl =>
    match Core.Program.Procedure.find? prelude decl.name with
    | some proc =>
      let inputs := proc.header.inputs.values.map getTypeName
      let outputs := proc.header.outputs.values.map getTypeName
      some (proc.header.name.name, { inputs := inputs, outputs := outputs })
    | none => none

/-- Extract field declarations from class body (annotated assignments at class level) -/
def extractClassFields (ctx : TranslationContext) (classBody : Array (Python.stmt SourceRange))
    : Except TranslationError (List Field) := do
  let mut fields : List Field := []

  for stmt in classBody do
    match stmt with
    | .AnnAssign _ target annotation _ _ =>
      -- Class-level annotated assignment: x: int
      let fieldName ← match target with
        | .Name _ name _ => .ok name.val
        | _ => throw (.unsupportedConstruct "Only simple field names supported" (toString (repr stmt)))

      let fieldType ← translateType ctx (pyExprToString annotation)

      fields := fields ++ [{
        name := fieldName
        type := fieldType
        isMutable := true  -- Python fields are mutable by default
      }]
    | _ => pure ()  -- Ignore non-field statements

  return fields

/-- Translate a Python method to a Laurel instance procedure -/
def translateMethod (ctx : TranslationContext) (className : String)
    (methodStmt : Python.stmt SourceRange)
    : Except TranslationError Procedure := do
  match methodStmt with
  | .FunctionDef _ name args body _ ret _ _ => do
    let methodName := name.val

    -- First parameter is self - type it as the class
    let selfParam : Parameter := {
      name := "self"
      type := mkHighTypeMd (.UserDefined className)
    }

    -- Translate remaining parameters
    let mut inputs : List Parameter := [selfParam]
    match args with
    | .mk_arguments _ _ argsList _ _ _ _ _ =>
      -- Skip first arg (self), process rest
      for arg in argsList.val.toList.tail! do
        match arg with
        | .mk_arg _ paramName paramAnnotation _ =>
          let paramType ← match paramAnnotation.val with
            | some annot => translateType ctx (pyExprToString annot)
            | none => throw (TranslationError.typeError s!"Parameter {paramName.val} must have type annotation")
          inputs := inputs ++ [{name := paramName.val, type := paramType}]

    -- Translate return type
    let outputs ← match ret.val with
      | some retExpr => do
        let retType ← translateType ctx (pyExprToString retExpr)
        pure (match retType.val with
          | HighType.TVoid => []
          | _ => [{name := "result", type := retType}])
      | none => pure []

    -- Translate method body with class context
    let ctxWithClass := {ctx with currentClassName := some className}
    let (_, bodyStmts) ← translateStmtList ctxWithClass body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    return {
      name := methodName
      inputs := inputs
      outputs := outputs
      preconditions := []
      decreases := none
      body := .Transparent bodyBlock
    }
  | _ => throw (.internalError "Expected FunctionDef for method")

/-- Translate a Python class to a Laurel CompositeType -/
def translateClass (ctx : TranslationContext) (classStmt : Python.stmt SourceRange)
    : Except TranslationError CompositeType := do
  match classStmt with
  | .ClassDef _ className bases _ body _ _ =>
    let className := className.val

    -- Extract fields from class body
    let fields ← extractClassFields ctx body.val

    -- Extract methods from class body
    let methodStmts := body.val.toList.filter fun stmt =>
      match stmt with
      | .FunctionDef _ _ _ _ _ _ _ _ => true
      | _ => false

    -- Translate each method
    let mut instanceProcedures : List Procedure := []
    for methodStmt in methodStmts do
      let proc ← translateMethod ctx className methodStmt
      instanceProcedures := instanceProcedures ++ [proc]

    -- Handle inheritance (bases)
    let extending : List Identifier := bases.val.toList.filterMap fun base =>
      match base with
      | .Name _ name _ => some name.val
      | _ => none  -- Ignore complex base expressions for now

    return {
      name := className
      extending := extending
      fields := fields
      instanceProcedures := instanceProcedures
    }
  | _ => throw (.internalError "Expected ClassDef")


/-- Translate Python module to Laurel Program -/
def pythonToLaurel (prelude: Core.Program) (pyModule : Python.Command SourceRange) : Except TranslationError Laurel.Program := do
  match pyModule with
  | .Module _ body _ => do
    let preludeProcedures := extractPreludeProcedures prelude
    let preludeTypes := extractPreludeTypes prelude

    -- Collect user function names
    let userFunctions := body.val.toList.filterMap fun stmt =>
      match stmt with
      | .FunctionDef _ name _ _ _ _ _ _ => some name.val
      | _ => none


    -- FIRST PASS: Collect all class definitions
    let mut compositeTypes : List CompositeType := []
    for stmt in body.val do
      match stmt with
      | .ClassDef _ _ _ _ _ _ _ =>
        let composite ← translateClass {preludeProcedures := preludeProcedures, compositeTypes := compositeTypes} stmt
        compositeTypes := compositeTypes ++ [composite]
      | _ => pure ()

    -- SECOND PASS: Collect user function signatures
    let mut functionSignatures : List (String × Procedure) := []
    for stmt in body.val do
      match stmt with
      | .FunctionDef _ _ _ _ _ _ _ _ =>
        let proc ← translateFunction {preludeProcedures := preludeProcedures, preludeTypes := preludeTypes, userFunctions := userFunctions, compositeTypes := compositeTypes} stmt
        functionSignatures := functionSignatures ++ [(proc.name, proc)]
      | _ => pure ()

    -- Create context with composite types and function signatures
    let ctx : TranslationContext := {
      preludeProcedures := preludeProcedures,
      preludeTypes := preludeTypes,
      userFunctions := userFunctions,
      compositeTypes := compositeTypes,
      functionSignatures := functionSignatures
    }

    -- THIRD PASS: Translate functions and other statements
    let mut procedures : List Procedure := []
    let mut otherStmts : List (Python.stmt SourceRange) := []

    for stmt in body.val do
      match stmt with
      | .FunctionDef _ _ _ _ _ _ _ _ =>
        let proc ← translateFunction ctx stmt
        procedures := procedures ++ [proc]
      | .ClassDef _ _ _ _ _ _ _ =>
        pure ()  -- Already processed in first pass
      | .Import _ _ | .ImportFrom _ _ _ _ =>
        pure ()  -- Ignore imports
      | .If _ _ _ _ =>
        pure ()  -- Ignore top-level if statements
      | _ =>
        otherStmts := otherStmts ++ [stmt]

    let (_, bodyStmts) ← translateStmtList ctx otherStmts
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyStmts := mkStmtExprMd (.LocalVariable "__name__" (mkHighTypeMd .TString) (some <| mkStmtExprMd (.LiteralString "__main__"))) :: bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    let mainProc : Procedure := {name := "__main__", inputs := [], outputs := [], preconditions := [], decreases := none, body := .Transparent bodyBlock}

    let typeDefinitions := compositeTypes.map TypeDefinition.Composite

    let program : Laurel.Program := {
      staticProcedures := mainProc :: procedures
      staticFields := []
      types := typeDefinitions
      constants := []
    }

    return program

  | _ => throw (TranslationError.internalError "Expected Module")

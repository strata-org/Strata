/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Core.Verifier
import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.CorePrelude
import Strata.Languages.Python.Specs.ToLaurel
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
  /-- Overload dispatch table from PySpec: function name → overloads -/
  overloadTable : Specs.ToLaurel.OverloadTable := {}
  /-- Behavior for unmodeled functions -/
  unmodeledBehavior : UnmodeledFunctionBehavior := .havocOutputs
  /-- File path for source location metadata -/
  filePath : String := ""
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

/-- Create metadata from a SourceRange for attaching to Laurel statements. -/
def sourceRangeToMetaData (filePath : String) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let uri : Uri := .file filePath
  let fileRangeElt := ⟨ Imperative.MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩
  #[fileRangeElt]

/-- Create default metadata for Laurel AST nodes -/
def defaultMetadata : Imperative.MetaData Core.Expression :=
  #[]

/-- Create a HighTypeMd with default metadata -/
def mkHighTypeMd (ty : HighType) : HighTypeMd :=
  { val := ty, md := defaultMetadata }

/-- Create a HighTypeMd with source location metadata -/
def mkHighTypeMdWithLoc (ty : HighType) (md : Imperative.MetaData Core.Expression) : HighTypeMd :=
  { val := ty, md := md }

def mkCoreType (s: String): HighTypeMd :=
  {val := .TCore s , md := defaultMetadata}

/-- Create a StmtExprMd with default metadata -/
def mkStmtExprMd (expr : StmtExpr) : StmtExprMd :=
  { val := expr, md := defaultMetadata }

/-- Create a StmtExprMd with source location metadata -/
def mkStmtExprMdWithLoc (expr : StmtExpr) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  { val := expr, md := md }

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
        -- Map it to a core PyAnyType
        .ok (mkCoreType "PyAnyType")

/-- Create a None value for a given OrNone type -/
def mkNoneForType (typeName : String) : StmtExprMd :=
  -- First construct None_none(), then wrap it in the appropriate OrNone constructor
  let noneVal := mkStmtExprMd (StmtExpr.StaticCall "None_none" [])
  mkStmtExprMd (StmtExpr.StaticCall s!"{typeName}_mk_none" [noneVal])

/-- Look up a function call in the overload dispatch table.
    Extracts the bare function name from the call target, then
    returns the class name if the first arg is a string literal
    matching an overload entry. -/
def resolveDispatch (ctx : TranslationContext)
    (f : Python.expr SourceRange)
    (args : Array (Python.expr SourceRange))
    : Except TranslationError (Option String) := do
  let funcName := match f with
    | .Attribute _ _ attr _ => attr.val
    | .Name _ n _ => n.val
    | _ => ""
  match ctx.overloadTable.get? funcName with
  | none => return none
  | some fnOverloads =>
    let .isTrue _ := decideProp (args.size > 0)
      | throw (.typeError
          s!"Dispatched function '{funcName}' called with no \
            arguments (expected a string literal first argument)")
    match args[0] with
    | .Constant _ (.ConString _ s) _ =>
      return (fnOverloads.get? s.val).map (·.name)
    | _ => return none

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
        let leftType := Laurel.computeExprType typeEnv [] leftExpr
        -- Dispatch on left operand
        if highEq leftType { val := .TString, md := leftExpr.md } then
          .ok Operation.StrConcat
        else
          .ok Operation.Add
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

  | .Call _ f args _kwargs =>
    translateCall ctx f args.val.toList

  | _ => throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr e)))

/-- Translate a Python call expression to Laurel.
    Tries factory dispatch, then method dispatch on typed variables,
    then falls back to a static call by flattened name. -/
partial def translateCall (ctx : TranslationContext) (f : Python.expr SourceRange) (args : List (Python.expr SourceRange))
    : Except TranslationError StmtExprMd := do
  -- Step 1: factory dispatch (e.g., boto3.client('iam'))
  if let some className ← resolveDispatch ctx f args.toArray then
    return mkStmtExprMd (.New className)
  -- Step 2: method call on typed variable (e.g., iam.get_role())
  --   Resolve to ClassName_method(obj, args)
  let (funcName, finalArgs) := match f with
    | .Attribute _ obj methodAttr _ =>
      match obj with
      | .Name _ objName _ =>
        match ctx.variableTypes.lookup objName.val with
        | some ⟨.UserDefined className, _⟩ =>
          (s!"{className}_{methodAttr.val}", obj :: args)
        | _ => (pyExprToString f, args)
      | _ => (pyExprToString f, args)
    | _ => (pyExprToString f, args)
  -- Step 3: translate the resolved call
  let mut translatedArgs ← finalArgs.mapM (translateExpr ctx)

  -- Check if function has a model
  if !hasModel ctx funcName then
    return mkStmtExprMd .Hole

  -- Check if this is a prelude procedure and fill in optional args
  if let some sig := ctx.preludeProcedures.lookup funcName then
    let numProvided := translatedArgs.length
    let numExpected := sig.inputs.length

    if numProvided < numExpected then
      for i in [numProvided:numExpected] do
        let paramType := sig.inputs[i]!
        translatedArgs := translatedArgs ++ [mkNoneForType paramType]

    -- Check if function returns maybe_except (by convention, last output if present)
    if sig.outputs.length > 0 && sig.outputs.getLast! == "ExceptOrNone" then
      let call := mkStmtExprMd (StmtExpr.StaticCall funcName translatedArgs)
      let mut targets := []
      for i in [:sig.outputs.length - 1] do
        targets := targets ++ [mkStmtExprMd (.Identifier s!"result{i}")]
      targets := targets ++ [mkStmtExprMd (.Identifier "maybe_except")]
      return mkStmtExprMd (.Assign targets call)

  return mkStmtExprMd (StmtExpr.StaticCall funcName translatedArgs)

end

/-! ## Statement Translation

Translate Python statements to Laurel StmtExpr nodes.
These functions are mutually recursive.
-/

mutual

partial def translateStmt (ctx : TranslationContext) (s : Python.stmt SourceRange)
    : Except TranslationError (TranslationContext × StmtExprMd) := do
  let md := sourceRangeToMetaData ctx.filePath s.toAst.ann
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

  -- Annotated assignment: x: int = expr
  | .AnnAssign _ target annotation value _ => do
    let varName ← match target with
      | .Name _ name _ => .ok name.val
      | _ => throw (.unsupportedConstruct "Only simple variable annotation supported" (toString (repr s)))
    let typeStr := pyExprToString annotation
    -- Try the annotation first; if it resolves to PyAnyType and there's
    -- an initializer call, fall back to the dispatch table.  This handles
    -- the mismatch between Python type-stub names and PySpec service names.
    let annotationType ← translateType ctx typeStr
    let varType ← match annotationType.val, value.val with
      | .TCore "PyAnyType", some (.Call _ f args _) =>
        match ← resolveDispatch ctx f args.val with
        | some name => .ok (mkHighTypeMd (.UserDefined name))
        | none => .ok annotationType
      | _, _ => .ok annotationType
    -- Add to context
    let newCtx := { ctx with variableTypes := ctx.variableTypes ++ [(varName, varType)] }
    -- If there's an initializer, create declaration with init
    match value.val with
    | some initExpr => do
      let initVal ← translateExpr newCtx initExpr
      let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType (some initVal))
      return (newCtx, declStmt)
    | none =>
      -- Declaration without initializer (not allowed in pure context, but OK in procedures)
      let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType none)
      return (newCtx, declStmt)

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
  | .Assert _ test _msg => do
    let condExpr ← translateExpr ctx test
    let assertStmt := mkStmtExprMdWithLoc (StmtExpr.Assert condExpr) md
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
      precondition := mkStmtExprMd (StmtExpr.LiteralBool true)
      determinism := .deterministic none -- TODO: need to set reads
      decreases := none
      body := Body.Transparent bodyBlock
      md := default
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

/-- Translate Python module to Laurel Program -/
def pythonToLaurel (prelude: Core.Program)
    (pyModule : Python.Command SourceRange)
    (filePath : String := "")
    (overloadTable : Specs.ToLaurel.OverloadTable := {})
    : Except TranslationError Laurel.Program := do
  match pyModule with
  | .Module _ body _ => do
    let preludeProcedures := extractPreludeProcedures prelude
    let preludeTypes := extractPreludeTypes prelude

    -- Collect user function names
    let userFunctions := body.val.toList.filterMap fun stmt =>
      match stmt with
      | .FunctionDef _ name _ _ _ _ _ _ => some name.val
      | _ => none

    let ctx : TranslationContext := {
      preludeProcedures := preludeProcedures,
      preludeTypes := preludeTypes,
      userFunctions := userFunctions,
      overloadTable := overloadTable,
      filePath := filePath
    }

    -- Separate functions from other statements
    let mut procedures : List Procedure := []
    let mut otherStmts : List (Python.stmt SourceRange) := []

    for stmt in body.val do
      match stmt with
      | .FunctionDef _ _ _ _ _ _ _ _ =>
        let proc ← translateFunction ctx stmt
        procedures := procedures ++ [proc]
      | _ =>
        otherStmts := otherStmts ++ [stmt]

    let (_, bodyStmts) ← translateStmtList ctx otherStmts
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyStmts := mkStmtExprMd (.LocalVariable "__name__" (mkHighTypeMd .TString) (some <| mkStmtExprMd (.LiteralString "__main__"))) :: bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    let mainProc : Procedure := {
      name := "__main__",
      inputs := [],
      outputs := [],
      precondition := mkStmtExprMd (StmtExpr.LiteralBool true),
      decreases := none,
      determinism := .deterministic none --TODO: need to set reads
      body := .Transparent bodyBlock
      md := default
      }

    let program : Laurel.Program := {
      staticProcedures := mainProc :: procedures
      staticFields := []
      types := []
      constants := []
    }

    return program

  | _ => throw (.internalError "Expected Module")

end Strata.Python

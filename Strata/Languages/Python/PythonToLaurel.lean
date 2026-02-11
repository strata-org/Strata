/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Core.Verifier
import Strata.Languages.Python.PythonDialect

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

structure TranslationContext where
  /-- Map from variable names to their Laurel types -/
  variableTypes : List (String × HighTypeMd) := []
  /-- Map from function names to their signatures -/
  functionSignatures : List (String × Procedure) := []
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
    s!"{base}.{attr.val}"
  | _ => "<unknown>"

/-! ## Translation Functions -/

/-- Translate Python type annotation to Laurel HighType -/
def translateType (typeStr : String) : Except TranslationError HighTypeMd :=
  match typeStr with
  | "int" => .ok (mkHighTypeMd HighType.TInt)
  | "bool" => .ok (mkHighTypeMd HighType.TBool)
  | "str" => .ok (mkHighTypeMd HighType.TString)
  | _ => throw (.typeError s!"Unsupported type: {typeStr}")

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
      | .Add _ => .ok Operation.Add
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

  | .Call _ f args _kwargs => return mkStmtExprMd (StmtExpr.StaticCall (pyExprToString f) (← args.val.toList.mapM (translateExpr ctx)))

  | _ => throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr e)))

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

  -- Annotated assignment: x: int = expr
  | .AnnAssign _ target annotation value _ => do
    let varName ← match target with
      | .Name _ name _ => .ok name.val
      | _ => throw (.unsupportedConstruct "Only simple variable annotation supported" (toString (repr s)))
    let typeStr := pyExprToString annotation
    let varType ← translateType typeStr
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
    let assertStmt := mkStmtExprMd (StmtExpr.Assert condExpr)
    return (ctx, assertStmt)

  -- Expression statement (e.g., function call)
  | .Expr _ value => do
    let expr ← translateExpr ctx value
    return (ctx, expr)

  | .Import _ _ | .ImportFrom _ _ _ _ => return (ctx, mkStmtExprMd .Hole)

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
          let paramType ← translateType paramTypeStr
          inputs := inputs ++ [{ name := paramName.val, type := paramType }]
          localCtx := { localCtx with variableTypes := localCtx.variableTypes ++ [(paramName.val, paramType)] }

    -- Translate return type
    let returnType ← match returns.val with
      | some retExpr => translateType (pyExprToString retExpr)
      | none => .ok (mkHighTypeMd HighType.TVoid)

    -- Determine outputs based on return type
    let outputs : List Parameter :=
      match returnType.val with
      | HighType.TVoid => []
      | _ => [{ name := "result", type := returnType }]

    -- Translate function body
    let (_, bodyStmts) ← translateStmtList localCtx body.val.toList
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

/-- Translate Python module to Laurel Program -/
def pythonToLaurel (pyModule : Python.Command SourceRange) : Except TranslationError Laurel.Program := do
  match pyModule with
  | .Module _ body _ => do
    let ctx : TranslationContext := default

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

    let ctx : TranslationContext := {variableTypes := [], functionSignatures := procedures.map (λ p => (p.name, p))}
    let (_, bodyStmts) ← translateStmtList ctx otherStmts
    let bodyStmts := mkStmtExprMd (.LocalVariable "__name__" (mkHighTypeMd .TString) (some <| mkStmtExprMd (.LiteralString "__main__"))) :: bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    let mainProc : Procedure := {name := "__main__", inputs := [], outputs := [], preconditions := [], decreases := none, body := .Transparent bodyBlock}

    -- Create Laurel program - use fully qualified name to avoid ambiguity
    let program : Laurel.Program := {
      staticProcedures := mainProc :: procedures
      staticFields := []
      types := []
      constants := []
    }

    return program

  | _ => throw (.internalError "Expected Module")

/-! ## Verification Entry Point

This will be the main entry point for verifying Python programs through Laurel.
-/

def verifyPythonThroughLaurel (pyModule : Python.Command SourceRange)
    (smtsolver : String := "cvc5")
    : IO (Except TranslationError Core.VCResults) := do
  -- Step 1: Translate Python to Laurel
  let laurelProgram := pythonToLaurel pyModule
  match laurelProgram with
  | .error e => return .error e
  | .ok laurelProg =>
    -- Step 2: Translate Laurel to Core (using existing translator)
    let coreProgram := Laurel.translate laurelProg
    match coreProgram with
    | .error diagnostics =>
      return .error (.internalError s!"Laurel to Core translation failed: {diagnostics}")
    | .ok coreProg =>
      -- Step 3: Verify using Core verifier
      try
        let results ← IO.FS.withTempDir fun tempDir => do
          EIO.toIO (fun e => IO.Error.userError (toString e))
            (Core.verify smtsolver coreProg tempDir none default)
        return .ok results
      catch e =>
        return .error (.internalError s!"Verification failed: {e}")

end Strata.Python

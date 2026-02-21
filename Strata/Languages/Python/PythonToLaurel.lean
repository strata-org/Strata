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

structure PythonFunctionDecl where
  name : String
  --args include name, type, default value
  args : List (String × String × Option (Python.expr SourceRange))
  has_kwargs: Bool
  ret : Option String
deriving Repr, Inhabited

structure TranslationContext where
  /-- Map from variable names to their Laurel types -/
  variableTypes : List (String × HighTypeMd) := []
  /-- Map from function names to their signatures -/
  functionSignatures : List PythonFunctionDecl := []
  /-- Map from prelude procedure names to their full signatures -/
  preludeProcedures : List (String × CoreProcedureSignature) := []
  /-- Names of user-defined functions -/
  userFunctions : List String := []
  /-- Names of user-defined classes -/
  userClasses : List String := []
  /-- Map (Classname, Attribute) to its type -/
  ClassAttribute_type: Std.HashMap (String × String) HighTypeMd := {}
  /-- Names of prelude types -/
  preludeTypes : List String := []
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
  | "Any" => some "Any"
  | "datetime" => some "Datetime"
  | "timedelta" => some "int"
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
        .ok (mkCoreType "Any")

def AnyTy := mkCoreType "Any"
def PackageTy := mkCoreType "Package"
def intTy := mkHighTypeMd HighType.TInt
def boolTy := mkHighTypeMd HighType.TBool
def strTy := mkHighTypeMd HighType.TString
def strToAny (s: String) := mkStmtExprMd (.StaticCall "from_string" [mkStmtExprMd (StmtExpr.LiteralString s)])
def intToAny (i: Int) := mkStmtExprMd (.StaticCall "from_int" [mkStmtExprMd (StmtExpr.LiteralInt i)])
def boolToAny (b: Bool) := mkStmtExprMd (.StaticCall "from_bool" [mkStmtExprMd (StmtExpr.LiteralBool b)])
def AnyNone := mkStmtExprMd (.StaticCall "from_none" [])
def Any_to_bool (b: StmtExprMd) := mkStmtExprMd (.StaticCall "Any_to_bool" [b])


def HighTypeToString (ty: HighType) : String :=
  match ty with
  | .TVoid => "none"
  | .TBool => "bool"
  | .TInt => "int"
  | .TFloat64 => "float"
  | .TString => "string"
  | .THeap => "heap"
  | .UserDefined name => name
  | .TCore s => s
  | _ => "UnknownType"

/-- Create a None value for a given OrNone type -/
def mkNoneForType (typeName : String) : StmtExprMd :=
  -- First construct None_none(), then wrap it in the appropriate OrNone constructor
  let noneVal := mkStmtExprMd (StmtExpr.StaticCall "None_none" [])
  mkStmtExprMd (StmtExpr.StaticCall s!"{typeName}_mk_none" [noneVal])

def OptionNone : StmtExprMd := mkStmtExprMd (StmtExpr.StaticCall "None" [])

def DictStrAny_mk_aux
    (kv: List (String × StmtExprMd)) (acc: StmtExprMd): StmtExprMd :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let dict_insert := StmtExpr.StaticCall "DictStrAny_insert" [acc, mkStmtExprMd (StmtExpr.LiteralString k), v]
      DictStrAny_mk_aux t (mkStmtExprMd dict_insert)

def DictStrAny_empty:= mkStmtExprMd (StmtExpr.StaticCall "DictStrAny_empty" [])

def DictStrAny_mk (kv: List (String × StmtExprMd)) := DictStrAny_mk_aux kv DictStrAny_empty


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
  | .Constant _ (.ConPos _ n) _ => return intToAny n.val
  | .Constant _ (.ConNeg _ n) _ => return intToAny (-n.val)
  -- String literals
  | .Constant _ (.ConString _ s) _ => return strToAny s.val
  -- Boolean literals
  | .Constant _ (.ConTrue _) _ => return boolToAny true
  | .Constant _ (.ConFalse _) _ => return boolToAny false
  | .Constant _ (.ConNone _) _ =>
    return OptionNone

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

  -- JoinedStr (f-strings) - return first part until we have string concat
  | .JoinedStr _ values =>
    if values.val.isEmpty then
      return mkStmtExprMd (StmtExpr.LiteralString "")
    else
      let first ← translateExpr ctx values.val[0]!
      return first

  | .Call _ f args kwargs => translateCall ctx f args.val.toList kwargs.val.toList

  | _ => throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr e)))


partial def breakdown_Attribute (expr: Python.expr SourceRange): (Python.expr SourceRange) × List String :=
  match expr with
  | .Attribute _ v attr _ =>
      let ret := (breakdown_Attribute v)
      (ret.fst , ret.snd ++ [attr.val])
  | _ => (expr, [])

partial def remap_funcname (ctx: TranslationContext) (fname: String) : String :=
  if fname ∈ ctx.userClasses then
    fname ++ "___init__"
  else
    match fname with
    | "str" => "to_string_any"
    | "int" => "to_int_any"
    | "len" => "Any_len_to_Any"
    | _ => fname

partial def isPackage (ctx : TranslationContext) (expr: Python.expr SourceRange) : Bool :=
  let (root, _):= breakdown_Attribute expr
  match root with
  | .Name _ n _ => n.val ∉ ctx.variableTypes.unzip.fst
  | _ => false

partial def get_unresolved_Attribute_type (attributes: List String) : String :=
  match attributes with
  | [] => ""
  | [h] => h
  | h::t => h ++ "_" ++ (get_unresolved_Attribute_type t)

partial def inferExprtype (ctx : TranslationContext) (e: Python.expr SourceRange) : String :=
  match e with
  -- Integer literals
  | .Constant _ (.ConPos _ _) _
  | .Constant _ (.ConNeg _ _) _ => "int"
  -- String literals
  | .Constant _ (.ConString _ _) _ => "string"
  -- Boolean literals
  | .Constant _ (.ConTrue _) _
  | .Constant _ (.ConFalse _) _
  | .BoolOp _ _ _
  | .Compare _ _ _ _=> "bool"
  -- Variable references
  | .Name _ n _ =>
      match ctx.variableTypes.find? (λ v => v.fst == n.val) with
      | some (_, ty) => HighTypeToString ty.val
      | _ => "Package"
  | .Attribute _ v attr _ =>
    let vty := inferExprtype ctx v
    match ctx.ClassAttribute_type.get? (vty, attr.val) with
      | some ty => HighTypeToString ty.val
      | _ => "Any"
  -- Binary operations
  | .BinOp _ _ _ _ => "Any"

  -- Unary operations
  | .UnaryOp _ _ _ => "Any"

  -- JoinedStr (f-strings) - return first part until we have string concat
  | .JoinedStr _ _ => "Any"

  | .Call _ f _ _ => getFunctionReturnType ctx f

  | _ => "Any"

partial def getFunctionReturnType (ctx : TranslationContext) (func: Python.expr SourceRange) : String :=
  let (fname, _) :=refineFunctionCallExpr ctx func
  match ctx.functionSignatures.find? (λ f => f.name == fname) with
    | some funcdecl => match funcdecl.ret with | some ty => ty | _=> "Any"
    | _ => "Any"


/-
Python function call can be caller.function_name(arg1, arg2, ...)
If a is a variable, and type of a can be inferred, then the call should be translated to TypeOfcaller_function_name (caller, arg1, arg2)
If a is a variable, and type of a can NOT be inferred, then the call should be translated to AnyType_function_name (TypeOf(caller), caller, arg1, arg2)
If a is a package, this should be translated to a_function_name (arg1, arg2)
If the function_name is a class, add __init__ into it
The following function return a tuple (translated function name, first argument, is the first argument of unknown type)
-/

partial def refineFunctionCallExpr (ctx : TranslationContext) (func: Python.expr SourceRange) :
        String × Option (Python.expr SourceRange) × Bool:=
  match func with
    | .Name _ n _ => (remap_funcname ctx n.val, none , false)
    | .Attribute _ v attr _ =>
        let callerty := inferExprtype ctx v
        let callname := attr.val
        if isPackage ctx v then
          (pyExprToString func, none, false)
        else
        if callerty == "Any" then
          ("AnyTyInstance" ++ "_" ++ callname, some v, true)
        else
          (callerty ++ "_" ++ callname, some v, false)
    | _ => panic! s!"{repr func} is not a function"

--Kwargs can be a single Dict variable: func_call (**var) or a normal Kwargs (key1 = val1, key2 =val2 ...)
partial def translateDictKWords (ctx : TranslationContext) (kw : Python.keyword SourceRange)
    : Except TranslationError (String × StmtExprMd) := do
  match kw with
  | .mk_keyword _ name expr =>
    let expr ← translateExpr ctx expr
    match name.val with
    | some n => return (n.val, expr)
    | none => throw (.internalError "Expected keyname for Dict Kwargs")

partial def PyKWordsToHashMap (kwords : List (Python.keyword SourceRange)) : Std.HashMap String (Python.expr SourceRange) :=
  kwords.foldl (λ hashmap kw =>
    match kw with
      | .mk_keyword _ name expr =>
        match name.val with
        | some n => hashmap.insert n.val expr
        | none => hashmap)
    {}

partial def isVarKwargs (kwords : List (Python.keyword SourceRange)) : Bool :=
  if kwords.length == 0 then false else
  match kwords[0]! with
  | .mk_keyword _ name _ =>
    match name.val with
    | some _ => false
    | none => true

partial def translateVarKwargs (ctx : TranslationContext) (kwords : List (Python.keyword SourceRange)) : Except TranslationError StmtExprMd := do
  match kwords[0]! with
  | .mk_keyword _ name expr =>
    match name.val with
    | some _ => panic! s!"Keyword arg should be a Dict"
    | none =>
        let expr ← translateExpr ctx expr
        return expr

partial def translateKwargs (ctx : TranslationContext) (kwords : List (Python.keyword SourceRange)): Except TranslationError StmtExprMd := do
  if isVarKwargs kwords then
    translateVarKwargs ctx kwords
  else
    let kws_and_exprs ← kwords.mapM (translateDictKWords ctx)
    let ret := DictStrAny_mk kws_and_exprs
    return ret

partial def remove_Posargs_from_Kwargs (kwords : List (Python.keyword SourceRange)) (funcdecl: PythonFunctionDecl) : List (Python.keyword SourceRange) :=
  kwords.filter (λ kw => match kw with
    | .mk_keyword _ name _ =>
      match name.val with
        | some n => n.val ∉ funcdecl.args.unzip.fst
        | none => True)

partial def CombinePositionalAndKeywordArgs
    (posargs: List (Python.expr SourceRange))
    (kwords : List (Python.keyword SourceRange))
    (funcdecl: PythonFunctionDecl) : (List (Python.expr SourceRange)) × (List (Python.keyword SourceRange)):=
  let kwordargs := remove_Posargs_from_Kwargs kwords funcdecl
  let kwords := PyKWordsToHashMap kwords
  let unprovided_posargs := funcdecl.args.drop posargs.length
  --every unprovided positional args must have a default value in the function signature or be provided in the kwargs
  let check_args := (unprovided_posargs.map (λ (name, _, default) => (name ∈ kwords.keys) || default.isSome)).all (fun a => a)
  let filled_posargs :=
    if check_args then
      unprovided_posargs.map (λ (name, _, default) =>
        match kwords.get? name with
          | some expr => expr
          | none => match default with
                  | some default => default
                  | _ => panic! "Must have a default")
    else
      panic! s!"{funcdecl.name} call miss default input"
  let posargs := posargs ++ filled_posargs
  (posargs, kwordargs)

partial def translateCall  (ctx : TranslationContext)
                            (func: Python.expr SourceRange)
                            (args: List (Python.expr SourceRange))
                            (kwords : List (Python.keyword SourceRange)): Except TranslationError StmtExprMd:= do
  let (fname, opt_firstarg, unknowtype) := refineFunctionCallExpr ctx func
  let args :=
    match opt_firstarg with
        | some firstarg => firstarg::args
        | _ => args
  let (args, kwords, funcdecl_has_kwargs) := match ctx.functionSignatures.find? (λ x => x.name == fname) with
    | .some funcdecl =>
        let (args, kwords) := CombinePositionalAndKeywordArgs args kwords funcdecl
        (args, kwords, funcdecl.has_kwargs)
    | _ => (args, kwords, false)
  let trans_args ← (args.mapM (λ a => translateExpr ctx a))
  let trans_kwords ← translateKwargs ctx kwords
  let trans_kwords_exprs :=
    if kwords.length == 0 then
      if funcdecl_has_kwargs then [DictStrAny_empty] else []
    else [trans_kwords]
  let typeof_expr := if unknowtype then [mkStmtExprMd (.StaticCall "TypeOf" [trans_args[0]!])] else []
  return mkStmtExprMd (StmtExpr.StaticCall fname (typeof_expr ++ trans_args ++ trans_kwords_exprs))


end

/-! ## Statement Translation

Translate Python statements to Laurel StmtExpr nodes.
These functions are mutually recursive.
-/

def withException (ctx : TranslationContext) (funcname: String) : Bool :=
  match ctx.preludeProcedures.lookup funcname with
  | some sig => sig.outputs.length > 0 && sig.outputs.getLast! == "ExceptOrNone"
  | _ => true

def maybe_except_var := mkStmtExprMd (.Identifier "maybe_except")

partial def translateAssign  (ctx : TranslationContext)
                             (lhs: Python.expr SourceRange)
                             (annotation: Option (Python.expr SourceRange) )
                             (rhs: Python.expr SourceRange)
                    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let rhs_trans ←  translateExpr ctx rhs
  match lhs with
    | .Name _ n _ =>
        let targetExpr := mkStmtExprMd (StmtExpr.Identifier n.val)
        let targets := match rhs_trans.val with
        | .StaticCall fnname _ =>
            if withException ctx fnname then [targetExpr, maybe_except_var] else [targetExpr]
        | _ => [targetExpr]
        let assignStmt := mkStmtExprMd (StmtExpr.Assign targets rhs_trans)
        if n.val ∈ ctx.variableTypes.unzip.1 then
          return (ctx, [assignStmt])
        else
          let infertype ←  translateType ctx (inferExprtype ctx rhs)
          let type ←  match annotation with
          | none => .ok infertype
          | some annotation =>
               translateType ctx (pyExprToString annotation)
          let initStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val AnyTy none)
          let newctx := {ctx with variableTypes:=(n.val, type)::ctx.variableTypes}
          return (newctx, [initStmt, assignStmt])
    | .Subscript _ _ _ _ =>
          throw (.unsupportedConstruct "Subscript assignment targets not yet supported" (toString (repr lhs)))
    | .Attribute _ _ _ _ =>
          throw (.unsupportedConstruct "Attribute assignment targets not yet supported" (toString (repr lhs)))
    | _ => throw (.unsupportedConstruct "Assignment targets not yet supported" (toString (repr lhs)))


mutual

partial def translateStmt (ctx : TranslationContext) (s : Python.stmt SourceRange)
    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let md := sourceRangeToMetaData ctx.filePath s.toAst.ann
  match s with
  -- Assignment: x = expr
  | .Assign _ targets value _ => do
    -- For now, only support single target
    if targets.val.size != 1 then
      throw (.unsupportedConstruct "Multiple assignment targets not yet supported" (toString (repr s)))
    translateAssign ctx targets.val[0]! none value

  -- Annotated assignment: x: int = expr
  | .AnnAssign _ target annotation value _ => do
    match value.val with
    | some value => translateAssign ctx target annotation value
    | none =>
      -- Declaration without initializer (not allowed in pure context, but OK in procedures)
      let varType ← translateType ctx (pyExprToString annotation)
      let varName := pyExprToString target
      let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType none)
      let newctx := {ctx with variableTypes:=(varName, varType)::ctx.variableTypes}
      return (newctx, [declStmt])

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
    let ifStmt := mkStmtExprMd (StmtExpr.IfThenElse (condExpr) bodyBlock elseBlock)
    return (bodyCtx, [ifStmt])

  -- While loop
  | .While _ test body _orelse => do
    -- Note: Python while-else not supported yet
    let condExpr ← translateExpr ctx test
    let (loopCtx, bodyStmts) ← translateStmtList ctx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    let whileStmt := mkStmtExprMd (StmtExpr.While condExpr [] none bodyBlock)
    return (loopCtx, [whileStmt])

  -- Return statement
  | .Return _ value => do
    let retVal ← match value.val with
      | some expr => do
        let e ← translateExpr ctx expr
        .ok (some e)
      | none => .ok none
    let retStmt := mkStmtExprMd (StmtExpr.Return retVal)
    return (ctx, [retStmt])

  -- Assert statement
  | .Assert _ test _msg => do
    let condExpr ← translateExpr ctx test
    let assertStmt := mkStmtExprMdWithLoc (StmtExpr.Assert (condExpr)) md
    return (ctx, [assertStmt])

  -- Expression statement (e.g., function call)
  | .Expr _ value => do
    let expr ← translateExpr ctx value
    return (ctx, [expr])

  | .Import _ _ | .ImportFrom _ _ _ _ |.Pass _ => return (ctx, [mkStmtExprMd .Hole])

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
    return (bodyCtx, [tryBlock])

  | .Raise _ _ _ => return (ctx, [mkStmtExprMd .Hole])

  | _ => throw (.unsupportedConstruct "Statement type not yet supported" (toString (repr s)))

partial def translateStmtList (ctx : TranslationContext) (stmts : List (Python.stmt SourceRange))
    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let mut currentCtx := ctx
  let mut result : List StmtExprMd := []
  for stmt in stmts do
    let (newCtx, laurelStmt) ← translateStmt currentCtx stmt
    currentCtx := newCtx
    result := result ++ laurelStmt
  return (currentCtx, result)

end

def prependExceptHandlingHelper (l: List StmtExprMd) : List StmtExprMd :=
  mkStmtExprMd (.LocalVariable "maybe_except" (mkCoreType "ExceptOrNone") (some OptionNone)) :: l

partial def breakdown_nested_Subscript (expr:  Python.expr SourceRange) : List ( Python.expr SourceRange) :=
  match expr with
  | .Subscript _ val slice _ => [val] ++ (breakdown_nested_Subscript slice)
  | _ => [expr]

partial def ArgumentTypeToString (arg: Python.expr SourceRange) : String :=
  match arg with
  | .Name _ n _ => n.val
  | .Subscript _ _ _ _ =>
    let subscript_list:= breakdown_nested_Subscript arg
    let subscript_head := subscript_list[0]!
    let slice_head := subscript_list[1]!
    let v_name := pyExprToString subscript_head
    match v_name with
    | "Optional" => "NoneOr" ++ pyExprToString slice_head
    | _ => v_name
  | .Constant _ _ _ => "None"
  | .Attribute _ _ _ _ => pyExprToString arg
  | _ => panic! s!"Unhandled Expr: {repr arg}"

--The return is a List (inputname, type, default value) and a bool indicating if the function has Kwargs input
def unpackPyArguments (args: Python.arguments SourceRange) : (List (String × String × Option (Python.expr SourceRange))) × Bool  :=
  match args with
    | .mk_arguments _ _ args _ _ _ kwargs defaults =>
      let argscount := args.val.size
      let defaultscount := defaults.val.size;
      let listdefaults := (List.range (argscount - defaultscount)).map (λ _ => none)
                        ++ defaults.val.toList.map (λ x => some x)
      let argsinfo := args.val.toList.zip listdefaults
      let argtypes :=
        argsinfo.map (λ a: Python.arg SourceRange × Option (Python.expr SourceRange) =>
        match a.fst with
          | .mk_arg _ name oty _ =>
            match oty.val with
              | .some ty => (name.val, ArgumentTypeToString ty, a.snd)
              | _ => (name.val, "Any", a.snd))
      (argtypes, kwargs.val.isSome)


def pyFuncDef_to_PythonFunctionDecl (f : Python.stmt SourceRange) : Except TranslationError PythonFunctionDecl :=
  match f with
  | .FunctionDef _ name args _body _decorator_list returns _type_comment _ =>
    let name := name.val
    let args_trans := unpackPyArguments args
    let args := if name.endsWith "___init__" then args_trans.fst.tail else args_trans.fst
    let ret := if name.endsWith "___init__" then some (name.dropEnd "___init__".length).toString
        else
        match returns.val with
          | some retExpr => some (pyExprToString retExpr)
          | none => none
    let has_kwargs := args_trans.snd
    return {
      name
      args
      has_kwargs
      ret
    }
  | _ => throw (.internalError "Expected FunctionDef")


/-- Translate Python function to Laurel Procedure -/
def translateFunction (ctx : TranslationContext) (f : Python.stmt SourceRange)
    : Except TranslationError Laurel.Procedure := do
  match f with
  | .FunctionDef _ name _args body _decorator_list returns _type_comment _ => do
    -- Extract function name
    let funcName := name.val

    -- Translate parameters
    let mut inputs : List Parameter := []
    let mut localCtx := ctx

    let funcdecl ←  pyFuncDef_to_PythonFunctionDecl f

    inputs ← funcdecl.args.mapM (fun (name, _, _) => do
        --let paramType ← translateType ctx type
        return { name := name, type := AnyTy })
    if funcdecl.has_kwargs then
      let paramType ← translateType ctx "DictStrAny"
      inputs:= inputs ++ [{ name := "kwargs", type := paramType }]


    -- Translate return type
    let returnType ← match returns.val with
      | some retExpr => translateType ctx (pyExprToString retExpr)
      | none => .ok (mkHighTypeMd HighType.TVoid)

    -- Determine outputs based on return type
    let outputs : List Parameter :=
      match returnType.val with
      | HighType.TVoid => []
      | _ => [{ name := "result", type := AnyTy },
      { name := "error", type := (mkCoreType "ExceptOrNone") }]

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

def preludeSignature_to_PythonFunctionDecl (prelude : Core.Program) : List PythonFunctionDecl :=
  prelude.decls.filterMap fun decl =>
    match Core.Program.Procedure.find? prelude decl.name with
    | some proc =>
      let inputtypes := proc.header.inputs.values.map getTypeName
      let inputnames := proc.header.inputs.keys.map (λ n => n.name)
      let outputtypes := proc.header.outputs.values.map getTypeName
      let noneexpr : Python.expr SourceRange := .Constant default (.ConNone default) default
      --let outputnames := proc.header.outputs.keys
      some {
        name:= proc.header.name.name
        args:= (inputnames.zip inputtypes).map (λ(n,t) => if t.endsWith "OrNone" then (n,t,noneexpr) else (n,t,none))
        has_kwargs := false
        ret := if outputtypes.length == 0 then none else outputtypes[0]!
      }


    | none => none


/-- Translate Python module to Laurel Program -/
def pythonToLaurel (prelude: Core.Program) (pyModule : Python.Command SourceRange) (prev_ctx: Option TranslationContext:= none) (filePath : String := "")
    : Except TranslationError (Laurel.Program × TranslationContext) := do
  match pyModule with
  | .Module _ body _ => do
    let preludeProcedures := extractPreludeProcedures prelude
    let preludeTypes := extractPreludeTypes prelude

    -- Collect user function names
    let userFunctions := body.val.toList.filterMap fun stmt =>
      match stmt with
      | .FunctionDef _ name _ _ _ _ _ _ => some name.val
      | _ => none

    let mut ctx : TranslationContext := match prev_ctx with
    | some prev_ctx => prev_ctx
    | _ =>
    {
      preludeProcedures := preludeProcedures,
      functionSignatures := preludeSignature_to_PythonFunctionDecl prelude
      preludeTypes := preludeTypes,
      userFunctions := userFunctions,
      filePath := filePath
    }

    -- Separate functions from other statements
    let mut procedures : List Procedure := []
    let mut otherStmts : List (Python.stmt SourceRange) := []

    for stmt in body.val do
      match stmt with
      | .FunctionDef _ _ _ _ _ _ _ _ =>
        let proc ← translateFunction ctx stmt
        let funcdecl ←  pyFuncDef_to_PythonFunctionDecl stmt
        ctx := {ctx with functionSignatures:= ctx.functionSignatures ++ [funcdecl]}
        procedures := procedures ++ [proc]
      | _ =>
        otherStmts := otherStmts ++ [stmt]

    let (_, bodyStmts) ← translateStmtList ctx otherStmts
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyStmts := mkStmtExprMd (.LocalVariable "__name__" AnyTy (some <| strToAny "__main__")) :: bodyStmts
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

    return (program, ctx)

  | _ => throw (.internalError "Expected Module")

def pythonToLaurel_withFuncSigature (prelude: Core.Program) (funsig : Python.Command SourceRange) (pyModule : Python.Command SourceRange)
            (filePath : String := "") : Except TranslationError Laurel.Program := do
  let funsig_trans ← pythonToLaurel prelude funsig
  let program ← pythonToLaurel prelude pyModule funsig_trans.snd filePath
  return program.fst


end Strata.Python

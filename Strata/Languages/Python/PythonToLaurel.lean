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
import Strata.Languages.Python.PythonLaurelCorePrelude
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

structure PythonFunctionDecl where
  name : String
  --args include name, type, default value
  args : List (String × String × Option (Python.expr SourceRange))
  hasKwargs: Bool
  ret : Option String
deriving Repr, Inhabited

structure TranslationContext where
  variableTypes : List (String × String) := []
  /-- List of function signatures -/
  functionSignatures : List PythonFunctionDecl := []
  /-- Map from prelude procedure names to their full signatures -/
  preludeProcedures : List (String × CoreProcedureSignature) := []
  /-- Names of prelude functions (non-procedure callables) -/
  preludeFunctions : List String := []
  /-- Names of user-defined functions -/
  userFunctions : List String := []
  /-- Names of user-defined classes -/
  userClasses : List String := []
  /-- Map (Classname, Attribute) to its type -/
  classAttributeType: Std.HashMap (String × String) String := {}
  /-- Names of prelude types -/
  preludeTypes : List String := []
  /-- Overload dispatch table from PySpec: function name → overloads -/
  overloadTable : Specs.ToLaurel.OverloadTable := {}
  /-- Behavior for unmodeled functions -/
  unmodeledBehavior : UnmodeledFunctionBehavior := .havocOutputs
  /-- File path for source location metadata -/
  filePath : String := ""
  /-- List of defined composite types (classes) -/
  compositeTypes : List CompositeType := []
  /-- Track current class during method translation -/
  currentClassName : Option String := none
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

/-- Walk through nested subscripts to find the root variable name.
    e.g. `a[b][c]` → `a`, `params["key"]` → `params` -/
partial def getSubscriptBaseName (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Subscript _ val _ _ => getSubscriptBaseName val
  | _ => pyExprToString e

def PyLauType.Int := "int"
def PyLauType.Bool := "bool"
def PyLauType.Str := "str"
def PyLauType.Datetime := "Datetime"
def PyLauType.DictStrAny := "DictStrAny"
def PyLauType.ListStr := "ListStr"
def PyLauType.Package := "Package"
def PyLauType.Any := "Any"

/-- Map Python type strings to Core type names -/
def pythonTypeToCoreType (typeStr : String) : Option String :=
  match typeStr with
  | "Dict[str, Any]" => some PyLauType.DictStrAny
  | "List[str]" => some PyLauType.ListStr
  | "Any" => some PyLauType.Any
  | "datetime" => some PyLauType.Datetime
  | "timedelta" => some PyLauType.Int
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
        .ok (mkCoreType PyLauType.Any)

def AnyTy := mkCoreType PyLauType.Any
def strToAny (s: String) := mkStmtExprMd (.StaticCall "from_string" [mkStmtExprMd (StmtExpr.LiteralString s)])
def intToAny (i: Int) := mkStmtExprMd (.StaticCall "from_int" [mkStmtExprMd (StmtExpr.LiteralInt i)])
def boolToAny (b: Bool) := mkStmtExprMd (.StaticCall "from_bool" [mkStmtExprMd (StmtExpr.LiteralBool b)])
def AnyNone := mkStmtExprMd (.StaticCall "from_none" [])
def Any_to_bool (b: StmtExprMd) := mkStmtExprMd (.StaticCall "Any_to_bool" [b])
def NoError : StmtExprMd := mkStmtExprMd (StmtExpr.StaticCall "NoError" [])

def getSubscriptList (expr:  Python.expr SourceRange) : List ( Python.expr SourceRange) :=
  match expr with
  | .Subscript _ val slice _ => (getSubscriptList val) ++ [slice]
  | _ => [expr]

def pyOptExprToString (e : Python.opt_expr SourceRange) : Except TranslationError String := do
  match e with
  | .some_expr _ (.Constant _ (.ConString _ s) _) => return s.val
  | _ => throw (.internalError s!"Expected some constant string: {repr e}")

def DictStrAny_mk_aux
    (kv: List (String × StmtExprMd)) (acc: StmtExprMd): StmtExprMd :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let dict_insert := StmtExpr.StaticCall "DictStrAny_insert" [acc, mkStmtExprMd (StmtExpr.LiteralString k), v]
      DictStrAny_mk_aux t (mkStmtExprMd dict_insert)

def DictStrAny_empty:= mkStmtExprMd (StmtExpr.StaticCall "DictStrAny_empty" [])

def DictStrAny_mk (kv: List (String × StmtExprMd)) := DictStrAny_mk_aux kv DictStrAny_empty

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
  ctx.preludeProcedures.any (·.1 == funcName) || ctx.userFunctions.contains funcName || ctx.preludeFunctions.contains funcName ||
  ctx.compositeTypes.any (fun ct => ct.name == funcName)

def ListAny_mk (es: List StmtExprMd) : StmtExprMd := match es with
  | [] => mkStmtExprMd (.StaticCall "ListAny_nil" [])
  | e::t => mkStmtExprMd (.StaticCall "ListAny_cons" [e, ListAny_mk t])

mutual

partial def translateList (ctx : TranslationContext) (elmts: List (Python.expr SourceRange))
    : Except TranslationError StmtExprMd := do
  let trans_elmts ←  elmts.mapM (translateExpr ctx)
  return  mkStmtExprMd (.StaticCall "from_ListAny" [ListAny_mk trans_elmts])

partial def translateDictStrAny (ctx : TranslationContext)
    (keys: List (Python.opt_expr SourceRange)) (values: List (Python.expr SourceRange))
      : Except TranslationError StmtExprMd := do
  if keys.length != values.length then
    throw (.internalError s!"Invalid Dict: number of keys not match number of values" )
  let kv := keys.zip values
  let val_trans ←  kv.unzip.snd.mapM (translateExpr ctx)
  let keys ← keys.mapM pyOptExprToString
  return  mkStmtExprMd (.StaticCall "from_Dict" [DictStrAny_mk (keys.zip val_trans)])

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
  | .Constant _ (.ConNone _) _ => return AnyNone

  -- Bytes literal
  | .Constant _ (.ConBytes _ _) _ =>
    return mkStmtExprMd .Hole

  -- Float literal
  | .Constant _ (.ConFloat _ _) _ =>
    return mkStmtExprMd .Hole

  -- Complex literal
  | .Constant _ (.ConComplex _ _ _) _ =>
    return mkStmtExprMd .Hole

  -- Ellipsis literal
  | .Constant _ (.ConEllipsis _) _ =>
    return mkStmtExprMd .Hole

  -- Variable references
  | .Name _ name _ =>
    return mkStmtExprMd (StmtExpr.Identifier name.val)

  -- Binary operations
  | .BinOp _ left op right => do
    let leftExpr ← translateExpr ctx left
    let rightExpr ← translateExpr ctx right
    let preludeOpnames ← match op with
      -- Arithmetic
      | .Add _ => .ok "PAdd"
      | .Sub _ => .ok "PSub"
      | .Mult _ => .ok "PMul"
      | .Div _ => return mkStmtExprMd .Hole -- Floating-point are not supported yet
      | .FloorDiv _ => .ok "PFloorDiv"  -- Python // maps to Laurel Div
      | .Mod _ => .ok "PMod"
      | .BitAnd _ => return mkStmtExprMd .Hole --TODO: Adding BitVector subtype in Any type, then the related operations
      | .BitOr _ => return mkStmtExprMd .Hole
      | .BitXor _ => return mkStmtExprMd .Hole
      -- Unsupported for now
      | _ => throw (.unsupportedConstruct s!"Binary operator not yet supported: {repr op}" (toString (repr e)))
    return mkStmtExprMd (StmtExpr.StaticCall preludeOpnames [leftExpr, rightExpr])

  -- Comparison operations
  | .Compare _ left ops comparators => do
    -- Python allows chained comparisons: a < b < c
    -- For now, only support single comparison
    if ops.val.size != 1 || comparators.val.size != 1 then
      throw (.unsupportedConstruct "Chained comparisons not yet supported" (toString (repr e)))
    let leftExpr ← translateExpr ctx left
    let rightExpr ← translateExpr ctx comparators.val[0]!
    let preludeOpnames ← match ops.val[0]! with
      | .Eq _ => .ok "PEq"
      | .NotEq _ => .ok "PNEq"
      | .Lt _ => .ok "PLt"
      | .LtE _ => .ok "PLe"
      | .Gt _ => .ok "PGt"
      | .GtE _ => .ok "PGe"
      | .In _ => .ok "PIn"
      | .NotIn _ => .ok "PNotIn"
      | _ => throw (.unsupportedConstruct s!"Comparison operator not yet supported: {repr ops.val[0]!}" (toString (repr e)))
    return mkStmtExprMd (StmtExpr.StaticCall preludeOpnames [leftExpr, rightExpr])

  -- Boolean operations
  | .BoolOp _ op values => do
    if values.val.size < 2 then
      throw (.internalError "BoolOp must have at least 2 operands")
    let preludeOpnames ← match op with
      | .And _ => .ok "PAnd"
      | .Or _ => .ok "POr"
    -- Translate all operands
    let mut exprs : List StmtExprMd := []
    for val in values.val do
      let expr ← translateExpr ctx val
      exprs := exprs ++ [expr]
    -- Chain binary operations: a && b && c becomes (a && b) && c
    let mut result := exprs[0]!
    for i in [1:exprs.length] do
      result := mkStmtExprMd (StmtExpr.StaticCall preludeOpnames [result, exprs[i]!])
    return result

  -- Unary operations
  | .UnaryOp _ op operand => do
    let operandExpr ← translateExpr ctx operand
    let preludeOpnames ← match op with
      | .Not _ => .ok "PNot"
      | .USub _ => .ok "PNeg"
      | _ => throw (.unsupportedConstruct s!"Unary operator not yet supported: {repr op}" (toString (repr e)))
    return mkStmtExprMd (StmtExpr.StaticCall preludeOpnames [operandExpr])

  -- JoinedStr (f-strings) - return first part until we have string concat
  | .JoinedStr _ values =>
    if values.val.isEmpty then
      return mkStmtExprMd (StmtExpr.LiteralString "")
    else
      let first ← translateExpr ctx values.val[0]!
      return first

  | .Call _ f args kwargs => translateCall ctx f args.val.toList kwargs.val.toList

  -- Subscript access: dict['key'] or list[0]
  -- Abstract: return havoc'd value (sound for any dict/list operation)
  -- Note: Creates free variables which cause type errors in some contexts (if conditions)
  -- TODO: Handle by creating explicit variable declarations
  | .Subscript _ val slice _ =>
    let dictOrList ← translateExpr ctx val
    let index ← translateExpr ctx slice
    return mkStmtExprMd (.StaticCall "Any_get" [dictOrList, index])

  -- Attribute access: obj.attr or obj.method
  | .Attribute _ obj attr _ => do
    -- Check if this is self.field access in a method
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
      -- Complex object expression - translate and access field
      let objExpr ← translateExpr ctx obj
      return mkStmtExprMd (StmtExpr.FieldSelect objExpr attr.val)

  -- List literal: [1, 2, 3]
  -- Abstract: return havoc'd list (sound abstraction)
  | .List _ elems _ => translateList ctx elems.val.toList

  -- Dict literal: {'a': 1}
  -- Abstract: return havoc'd dict (sound abstraction)
  | .Dict _ keys vals => translateDictStrAny ctx keys.val.toList vals.val.toList

  -- Set literal: {1, 2, 3}
  -- Abstract: return havoc'd set (sound abstraction)
  | .Set .. => return mkStmtExprMd .Hole

  -- Tuple literal: (1, 2)
  -- Abstract: return havoc'd tuple (sound abstraction)
  | .Tuple .. => return mkStmtExprMd .Hole

  -- List comprehension: [x for x in items]
  -- Abstract: return havoc'd list (sound abstraction)
  | .ListComp .. => return mkStmtExprMd .Hole

  -- Set comprehension: {x for x in items}
  -- Abstract: return havoc'd set (sound abstraction)
  | .SetComp .. => return mkStmtExprMd .Hole

  -- Dict comprehension: {k: v for k, v in items}
  | .DictComp .. => return mkStmtExprMd .Hole

  -- Generator expression: (x for x in items)
  | .GeneratorExp .. => return mkStmtExprMd .Hole

  | _ => throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr e)))


partial def getListAttributes (expr: Python.expr SourceRange): (Python.expr SourceRange) × List String :=
  match expr with
  | .Attribute _ v attr _ =>
      let ret := (getListAttributes v)
      (ret.fst , ret.snd ++ [attr.val])
  | _ => (expr, [])

partial def reMapFunctionName (ctx: TranslationContext) (fname: String) : String :=
  if fname ∈ ctx.userClasses then
    fname ++ "@__init__"
  else
    match fname with
    | "str" => "to_string_any"
    | "int" => "to_int_any"
    | "len" => "Any_len_to_Any"
    | _ => fname

partial def isPackage (ctx : TranslationContext) (expr: Python.expr SourceRange) : Bool :=
  let (root, _):= getListAttributes expr
  match root with
  | .Name _ n _ => n.val ∉ ctx.variableTypes.unzip.fst
  | _ => false

partial def inferExprType (ctx : TranslationContext) (e: Python.expr SourceRange) : Except TranslationError String := do
  match e with
  -- Integer literals
  | .Constant _ (.ConPos _ _) _
  | .Constant _ (.ConNeg _ _) _ => return PyLauType.Int
  -- String literals
  | .Constant _ (.ConString _ _) _ => return PyLauType.Str
  -- Boolean literals
  | .Constant _ (.ConTrue _) _
  | .Constant _ (.ConFalse _) _
  | .BoolOp _ _ _
  | .Compare _ _ _ _=> return PyLauType.Bool
  -- Variable references
  | .Name _ n _ =>
      match ctx.variableTypes.find? (λ v => v.fst == n.val) with
      | some (_, ty) => return ty
      | _ => return PyLauType.Package
  | .Attribute _ v attr _ =>
    let vty ←  inferExprType ctx v
    match ctx.classAttributeType.get? (vty, attr.val) with
      | some ty => return ty
      | _ => return PyLauType.Any
  -- Binary operations
  | .BinOp _ _ _ _ => return PyLauType.Any

  -- Unary operations
  | .UnaryOp _ _ _ => return PyLauType.Any

  -- JoinedStr (f-strings) - return first part until we have string concat
  | .JoinedStr _ _ => return PyLauType.Any

  | .Call _ f args _ => getFunctionReturnType ctx f args.val

  | _ => return PyLauType.Any

partial def getFunctionReturnType (ctx : TranslationContext) (func: Python.expr SourceRange) (args : Array (Python.expr SourceRange))
    : Except TranslationError String := do
  match resolveDispatch ctx func args with
  |.ok (some classname) => return classname
  | _=>
    let (fname, _) ← refineFunctionCallExpr ctx func
    match ctx.functionSignatures.find? (λ f => f.name == fname) with
      | some funcDecl => match funcDecl.ret with | some ty => return ty | _ => return PyLauType.Any
      | _ => return PyLauType.Any


/-
Python function call can be caller.function_name(arg1, arg2, ...)
If a is a variable, and type of a can be inferred, then the call should be translated to TypeOfcaller_function_name (caller, arg1, arg2)
If a is a variable, and type of a can NOT be inferred, then the call should be translated to AnyType_function_name (TypeOf(caller), caller, arg1, arg2)
If a is a package, this should be translated to a_function_name (arg1, arg2)
If the function_name is a class, add __init__ into it
The following function return a tuple (translated function name, first argument, is the first argument of unknown type)
-/

partial def refineFunctionCallExpr (ctx : TranslationContext) (func: Python.expr SourceRange) :
      Except TranslationError (String × Option (Python.expr SourceRange) × Bool) := do
  match func with
    | .Name _ n _ => return (reMapFunctionName ctx n.val, none , false)
    | .Attribute _ v attr _ =>
        let callerTy ←  inferExprType ctx v
        let callname := attr.val
        if isPackage ctx v then
          return (pyExprToString func, none, false)
        else
        if callerTy == PyLauType.Any then
          return ("AnyTyInstance" ++ "@" ++ callname, some v, true)
        else
          return (callerTy ++ "_" ++ callname, some v, false)
    | _ => throw (.internalError s!"{repr func} is not a function")

--Kwargs can be a single Dict variable: func_call (**var) or a normal Kwargs (key1 = val1, key2 =val2 ...)
partial def translateDictKWords (ctx : TranslationContext) (kw : Python.keyword SourceRange)
    : Except TranslationError (String × StmtExprMd) := do
  match kw with
  | .mk_keyword _ name expr =>
    let expr ← translateExpr ctx expr
    match name.val with
    | some n => return (n.val, expr)
    | none => throw (.internalError "Expected keyname for Dict Kwargs")

partial def pyKwordsToHashMap (kwords : List (Python.keyword SourceRange)) : Std.HashMap String (Python.expr SourceRange) :=
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
    | some _ => throw (.internalError s!"Keyword arg should be a Dict")
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

partial def removePosargsFromKwargs (kwords : List (Python.keyword SourceRange)) (funcDecl: PythonFunctionDecl) : List (Python.keyword SourceRange) :=
  kwords.filter (λ kw => match kw with
    | .mk_keyword _ name _ =>
      match name.val with
        | some n => n.val ∉ funcDecl.args.unzip.fst
        | none => true)

partial def combinePositionalAndKeywordArgs
    (posArgs: List (Python.expr SourceRange))
    (kwords : List (Python.keyword SourceRange))
    (funcDecl: Option PythonFunctionDecl)
      : Except TranslationError ((List (Python.expr SourceRange)) × (List (Python.keyword SourceRange)) × Bool):= do
  match funcDecl with
  | some funcDecl =>
    let kwordArgs := removePosargsFromKwargs kwords funcDecl
    let kwords := pyKwordsToHashMap kwords
    let unprovidedPosArgs := funcDecl.args.drop posArgs.length
    --every unprovided positional args must have a default value in the function signature or be provided in the kwargs
    let check_args := (unprovidedPosArgs.map (λ (name, _, default) => (name ∈ kwords.keys) || default.isSome)).all (fun a => a)
    let filledPosArgs ←
      if check_args then
        unprovidedPosArgs.mapM (λ (name, _, default) =>
          match kwords.get? name with
            | some expr => return expr
            | none => match default with
                  | some default => return default
                  | _ => throw (.internalError s!"Argument {name} must have a default value") )
      else
        throw (.internalError s!"{funcDecl.name} call miss default values for inputs")
    let posArgs := posArgs ++ filledPosArgs
    return (posArgs, kwordArgs, funcDecl.hasKwargs)
  | _ => return (posArgs, kwords, false)


/-- Translate a Python call expression to Laurel.
    Tries factory dispatch, then method dispatch on typed variables,
    then falls back to a static call by flattened name. -/
partial def translateCall (ctx : TranslationContext)
                          (f : Python.expr SourceRange)
                          (args : List (Python.expr SourceRange))
                          (kwords : List (Python.keyword SourceRange))
    : Except TranslationError StmtExprMd := do
  -- Step 1: factory dispatch (e.g., boto3.client('iam'))
  if let some className ← resolveDispatch ctx f args.toArray then
    return mkStmtExprMd (.New className)
  -- Step 2: method call on typed variable (e.g., iam.get_role())
  --   Resolve to ClassName_method(obj, args)

  let (funcName, opt_firstarg, _unknowtype) ←  refineFunctionCallExpr ctx f
  if !hasModel ctx funcName then
    return mkStmtExprMd .Hole
  -- Step 3: translate the resolved call
  let (args, kwords, funcdecl_hasKwargs) ← combinePositionalAndKeywordArgs args kwords (ctx.functionSignatures.find? (λ x => x.name == funcName))
  let trans_args ← args.mapM (translateExpr ctx)
  let trans_kwords ← translateKwargs ctx kwords
  let trans_kwords_exprs :=
    if kwords.length == 0 then
      if funcdecl_hasKwargs then [DictStrAny_empty] else []
    else [trans_kwords]
  match f with
  | .Name  _ _ _ =>  return mkStmtExprMd (StmtExpr.StaticCall funcName (trans_args ++ trans_kwords_exprs))
  | .Attribute _ val attr _ =>
      let target_trans ← translateExpr ctx val
      if opt_firstarg.isSome then
        return mkStmtExprMd (StmtExpr.InstanceCall target_trans attr.val (trans_args ++ trans_kwords_exprs))
      else
        return mkStmtExprMd (StmtExpr.StaticCall funcName (trans_args ++ trans_kwords_exprs))
  | _ =>  throw (.unsupportedConstruct "Invalid call construct" (toString (repr f)))


end

/-! ## Statement Translation

Translate Python statements to Laurel StmtExpr nodes.
These functions are mutually recursive.
-/

def withException (ctx : TranslationContext) (funcname: String) : Bool :=
  if funcname ∈ ctx.preludeFunctions then false else
  match ctx.preludeProcedures.lookup funcname with
  | some sig => sig.outputs.length > 0 && sig.outputs.getLast! == "Error"
  | _ => false

def maybeExceptVar := mkStmtExprMd (.Identifier "maybe_except")
def nullcall_var := mkStmtExprMd (.Identifier "nullcall_ret")

partial def translateAssign  (ctx : TranslationContext)
                             (lhs: Python.expr SourceRange)
                             (annotation: Option (Python.expr SourceRange) )
                             (rhs: Python.expr SourceRange)
                             (md: Imperative.MetaData Core.Expression)
                    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let rhs_trans ←  translateExpr ctx rhs
  if let .Hole := rhs_trans.val then
  {
    match lhs with
    | .Name _ n _ =>
      if n.val ∈ ctx.variableTypes.unzip.1 then
        let targetExpr := mkStmtExprMd (StmtExpr.Identifier n.val)
        return (ctx, [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)])
      else
        let initStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val AnyTy (mkStmtExprMd .Hole))
        let newctx := {ctx with variableTypes:=(n.val, "Any")::ctx.variableTypes}
        return (newctx, [initStmt])
    | _ => return (ctx, [mkStmtExprMd .Hole])
  }
  let mut newctx := ctx
  match lhs with
    | .Name _ n _ =>
        let targetExpr := mkStmtExprMd (StmtExpr.Identifier n.val)
        let assignStmts := match rhs_trans.val with
        | .StaticCall fnname args =>
            if ctx.compositeTypes.any (fun ct => ct.name == fnname) then
              let newExpr := mkStmtExprMd (StmtExpr.New fnname)
              let varType := mkHighTypeMd (.UserDefined fnname)
              let newStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val varType (some newExpr))
              let initStmt := mkStmtExprMd (StmtExpr.InstanceCall (mkStmtExprMd (StmtExpr.Identifier n.val)) "__init__" args)
              [newStmt, initStmt]
            else if withException ctx fnname.text then
              [mkStmtExprMd (StmtExpr.Assign [targetExpr, maybeExceptVar] rhs_trans)]
            else [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)]
        | _ => [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)]
        newctx := match rhs_trans.val with
        | .StaticCall fnname _ =>
            if ctx.compositeTypes.any (fun ct => ct.name == fnname) then
              {newctx with variableTypes:= newctx.variableTypes ++ [(n.val, fnname.text)]}
            else newctx
        | _=> newctx
        if n.val ∈ newctx.variableTypes.unzip.1 then
          return (newctx, assignStmts)
        else
          let inferType ← inferExprType ctx rhs
          let type := match annotation with
          | none => inferType
          | some annotation =>
               pyExprToString annotation
          let initStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val AnyTy AnyNone)
          newctx := {ctx with variableTypes:=(n.val, type)::ctx.variableTypes}
          return (newctx, initStmt::assignStmts)
    | .Subscript _ _ _ _ =>
        match getSubscriptList lhs with
        | target :: slices =>
            let target ← translateExpr ctx target
            let slices ← slices.mapM (translateExpr ctx)
            let anySetsExpr := mkStmtExprMd (StmtExpr.StaticCall "Any_sets" [target, ListAny_mk slices, rhs_trans])
            let assignStmts := [mkStmtExprMd (StmtExpr.Assign [target] anySetsExpr)]
            return (ctx,assignStmts)
        | _ =>  throw (.internalError "Invalid Subscript Expr")
    | .Attribute _ obj attr _ =>
      match obj with
      | .Name _ name _ =>
        if name.val == "self" && ctx.currentClassName.isSome then
          -- self.field : type = value in a method
          let fieldAccess := mkStmtExprMd (StmtExpr.FieldSelect
            (mkStmtExprMd (StmtExpr.Identifier "self"))
            attr.val)
          let assignStmt := mkStmtExprMdWithLoc (StmtExpr.Assign [fieldAccess] rhs_trans) md
          return (ctx, [assignStmt])
        else
          let targetExpr ← translateExpr ctx lhs  -- This will handle self.field via translateExpr
          let assignStmt := mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] rhs_trans) md
          return (ctx, [assignStmt])
      | _ => throw (.unsupportedConstruct "Assignment targets not yet supported" (toString (repr lhs)))
    | _ => throw (.unsupportedConstruct "Assignment targets not yet supported" (toString (repr lhs)))

mutual

partial def translateStmt (ctx : TranslationContext) (s : Python.stmt SourceRange)
    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let md := sourceRangeToMetaData ctx.filePath s.toAst.ann
  match s with
  -- Assignment: x = expr or self.field = expr
  | .Assign _ targets value _ => do
    -- For now, only support single target
    if targets.val.size != 1 then
      throw (.unsupportedConstruct "Multiple assignment targets not yet supported" (toString (repr s)))
    translateAssign ctx targets.val[0]! none value md

  -- Annotated assignment: x: int = expr or x: ClassName = ClassName(args) or self.field: int = expr
  | .AnnAssign _ target annotation value _ => do
    match value.val with
    | some value => translateAssign ctx target annotation value md
    | none =>
      -- Declaration without initializer (not allowed in pure context, but OK in procedures)
      let varType := pyExprToString annotation
      let varName := pyExprToString target
      let newctx := {ctx with variableTypes:=(varName, varType)::ctx.variableTypes}
      let varType ← translateType ctx varType
      let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType AnyNone)
      return (newctx, [declStmt])

  -- If statement
  | .If _ test body orelse => do
    let condExpr ← translateExpr ctx test
    -- Check if condition contains a Hole - if so, hoist to variable to avoid free variable errors
    let (condStmts, finalCondExpr, condCtx) :=
      match condExpr.val with
      | .Hole =>
        -- Hoist Hole to fresh variable
        let freshVar := s!"cond_{test.toAst.ann.start.byteIdx}"
        let varType := mkHighTypeMd .TBool  -- Conditions are bools
        let varDecl := mkStmtExprMd (StmtExpr.LocalVariable freshVar varType (some condExpr))
        let varRef := mkStmtExprMd (StmtExpr.Identifier freshVar)
        ([varDecl], varRef, { ctx with variableTypes := ctx.variableTypes ++ [(freshVar, "Bool")] })
      | _ => ([], condExpr, ctx)

    -- Translate body (list of statements)
    let (bodyCtx, bodyStmts) ← translateStmtList condCtx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    -- Translate else branch if present
    let elseBlock ← if orelse.val.isEmpty then
      .ok none
    else do
      let (_, elseStmts) ← translateStmtList bodyCtx orelse.val.toList
      .ok (some (mkStmtExprMd (StmtExpr.Block elseStmts none)))
    let ifStmt := mkStmtExprMdWithLoc (StmtExpr.IfThenElse (Any_to_bool finalCondExpr) bodyBlock elseBlock) md

    -- Wrap in block if we hoisted condition
    let result := if condStmts.isEmpty then
      ifStmt
    else
      mkStmtExprMdWithLoc (StmtExpr.Block (condStmts ++ [ifStmt]) none) md

    return (bodyCtx, [result])

  -- While loop
  | .While _ test body _orelse => do
    -- Note: Python while-else not supported yet
    let condExpr ← translateExpr ctx test
    -- Check if condition contains a Hole - if so, hoist to variable
    let (condStmts, finalCondExpr, condCtx) :=
      match condExpr.val with
      | .Hole =>
        let freshVar := s!"while_cond_{test.toAst.ann.start.byteIdx}"
        let varType := mkHighTypeMd .TBool
        let varDecl := mkStmtExprMd (StmtExpr.LocalVariable freshVar varType (some condExpr))
        let varRef := mkStmtExprMd (StmtExpr.Identifier freshVar)
        ([varDecl], varRef, { ctx with variableTypes := ctx.variableTypes ++ [(freshVar, "bool")] })
      | _ => ([], condExpr, ctx)

    let (loopCtx, bodyStmts) ← translateStmtList condCtx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    let whileStmt := mkStmtExprMdWithLoc (StmtExpr.While (Any_to_bool finalCondExpr) [] none bodyBlock) md

    -- Wrap in block if we hoisted condition
    let result := if condStmts.isEmpty then
      whileStmt
    else
      mkStmtExprMdWithLoc (StmtExpr.Block (condStmts ++ [whileStmt]) none) md

    return (loopCtx, [result])

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
    -- Check if condition contains a Hole - if so, hoist to variable
    let (condStmts, finalCondExpr, condCtx) :=
      match condExpr.val with
      | .Hole =>
        let freshVar := s!"assert_cond_{test.toAst.ann.start.byteIdx}"
        let varType := mkHighTypeMd .TBool
        let varDecl := mkStmtExprMd (StmtExpr.LocalVariable freshVar varType (some condExpr))
        let varRef := mkStmtExprMd (StmtExpr.Identifier freshVar)
        ([varDecl], varRef, { ctx with variableTypes := ctx.variableTypes ++ [(freshVar, "bool")] })
      | _ => ([], condExpr, ctx)

    let assertStmt := mkStmtExprMdWithLoc (StmtExpr.Assert (Any_to_bool finalCondExpr)) md

    -- Wrap in block if we hoisted condition
    let result := if condStmts.isEmpty then
      assertStmt
    else
      mkStmtExprMdWithLoc (StmtExpr.Block (condStmts ++ [assertStmt]) none) md

    return (condCtx, [result])

  -- Expression statement (e.g., function call)
  | .Expr _ value => do
    let expr ← translateExpr ctx value
    let expr := { expr with md := md }

    match expr.val with
    | .StaticCall fnname _ =>
        match ctx.functionSignatures.find? (λ funsig => funsig.name == fnname) with
        | some funsig =>
            let targets := if funsig.ret.isNone then [] else [nullcall_var]
            let targets := if withException ctx fnname.text then targets++[maybeExceptVar] else targets
            if targets.length > 0 then
              return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Assign targets expr) md])
            else
              return (ctx, [expr])
        | _ => return (ctx, [expr])
    | _ => return (ctx, [expr])

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
      let isException := mkStmtExprMd (StmtExpr.StaticCall "isError"
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
    let tryBlock := mkStmtExprMdWithLoc (StmtExpr.Block (bodyStmtsWithChecks ++ [handlerBlock]) (some tryLabel)) md
    return (bodyCtx, [tryBlock])

  | .Raise _ _ _ => return (ctx, [mkStmtExprMd .Hole])

  -- For loop: for target in iter: body
  -- Abstract: execute body once with havoc'd target, then havoc all modified variables
  -- This is sound: if there are 0 iterations, we havoc; if >0, we execute once and havoc
  | .For _ target iter body _orelse _ => do
    -- Extract target variable name
    let targetName ← match target with
      | .Name _ name _ => .ok name.val
      | _ => throw (.unsupportedConstruct "Only simple variable in for target supported" (toString (repr s)))

    -- The iterator expression (we abstract it away)
    let _iterExpr ← translateExpr ctx iter

    -- Create context with target variable
    let bodyCtx := { ctx with variableTypes := ctx.variableTypes ++ [(targetName, PyLauType.Any)] }

    -- Translate loop body
    let (finalCtx, bodyStmts) ← translateStmtList bodyCtx body.val.toList

    -- Create: { target = havoc; body_statements }
    -- This abstracts: execute body once with arbitrary target value
    let targetDecl := mkStmtExprMd (StmtExpr.LocalVariable targetName AnyTy (some (mkStmtExprMd .Hole)))
    let loopBlock := mkStmtExprMdWithLoc (StmtExpr.Block ([targetDecl] ++ bodyStmts) none) md

    return (finalCtx, [loopBlock])

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
  mkStmtExprMd (.LocalVariable "maybe_except" (mkCoreType "Error") (some NoError)) :: l

partial def getNestedSubscripts (expr:  Python.expr SourceRange) : List ( Python.expr SourceRange) :=
  match expr with
  | .Subscript _ val slice _ => [val] ++ (getNestedSubscripts slice)
  | _ => [expr]

partial def argumentTypeToString (arg: Python.expr SourceRange) : Except TranslationError String :=
  match arg with
  | .Name _ n _ => return n.val
  | .Subscript _ _ _ _ =>
    let subscript_list:= getNestedSubscripts arg
    let subscript_head := subscript_list[0]!
    let slice_head := subscript_list[1]!
    let v_name := pyExprToString subscript_head
    match v_name with
    | "Optional" => return "NoneOr" ++ pyExprToString slice_head
    | _ => return v_name
  | .Constant _ _ _ => return "None"
  | .Attribute _ _ _ _ => return pyExprToString arg
  | _ => throw (.internalError s!"Unhandled Expr: {repr arg}")

--The return is a List (inputname, type, default value) and a bool indicating if the function has Kwargs input
def unpackPyArguments (args: Python.arguments SourceRange)
    : Except TranslationError ((List (String × String × Option (Python.expr SourceRange))) × Bool):= do
  match args with
    | .mk_arguments _ _ args _ _ _ kwargs defaults =>
      let argscount := args.val.size
      let defaultscount := defaults.val.size;
      let listdefaults := (List.range (argscount - defaultscount)).map (λ _ => none)
                        ++ defaults.val.toList.map (λ x => some x)
      let argsinfo := args.val.toList.zip listdefaults
      let argtypes ←
        argsinfo.mapM (λ a: Python.arg SourceRange × Option (Python.expr SourceRange) =>
        match a.fst with
          | .mk_arg _ name oty _ =>
            match oty.val with
              | .some ty => return (name.val, ← argumentTypeToString ty, a.snd)
              | _ => return (name.val, PyLauType.Any, a.snd))
      return (argtypes, kwargs.val.isSome)

def pyFuncDefToPythonFunctionDecl  (ctx : TranslationContext) (f : Python.stmt SourceRange) : Except TranslationError PythonFunctionDecl := do
  match f with
  | .FunctionDef _ name args _body _decorator_list returns _type_comment _ =>
    let name := match ctx.currentClassName with | none => name.val | some classname => classname ++ "_" ++ name.val
    let args_trans ← unpackPyArguments args
    let args := if name.endsWith "@__init__" then args_trans.fst.tail else args_trans.fst
    let ret := if name.endsWith "@__init__" then some (name.dropEnd "@__init__".length).toString
        else
        match returns.val with
          | some retExpr => some (pyExprToString retExpr)
          | none => none
    let hasKwargs := args_trans.snd
    return {
      name
      args
      hasKwargs
      ret
    }
  | _ => throw (.internalError "Expected FunctionDef")

/-- Translate Python function to Laurel Procedure -/
def translateFunction (ctx : TranslationContext) (funcDecl : PythonFunctionDecl) (body: List (Python.stmt SourceRange))
    : Except TranslationError (Laurel.Procedure × TranslationContext) := do

    -- Translate parameters
    let mut inputs : List Parameter := []

    inputs := funcDecl.args.map (fun (name, ty, _) =>
        if ctx.compositeTypes.any (fun ct => ct.name == ty) then
          { name := name, type := mkHighTypeMd (.UserDefined ty) }
        else
          { name := name, type := AnyTy})
    if funcDecl.hasKwargs then
      let paramType ← translateType ctx PyLauType.DictStrAny
      inputs:= inputs ++ [{ name := "kwargs", type := paramType }]

    -- Translate return type


    -- Determine outputs based on return type
    let outputs : List Parameter :=
      match funcDecl.ret with
      | none => []
      | some _ => [{ name := "LaurelResult", type := AnyTy }]

    -- Translate function body
    let inputTypes := funcDecl.args.map (λ (name, type, _) => (name, type))
    let ctx := {ctx with variableTypes:= ("nullcall_ret", PyLauType.Any)::inputTypes}
    let (newctx, bodyStmts) ← translateStmtList ctx body
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyStmts := (mkStmtExprMd (.LocalVariable "nullcall_ret" AnyTy (some AnyNone))) :: bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    -- Create procedure with transparent body (no contracts for now)
    let proc : Procedure := {
      name := funcDecl.name
      inputs := inputs
      outputs := outputs
      preconditions := []
      determinism := .deterministic none -- TODO: need to set reads
      decreases := none
      body := Body.Transparent bodyBlock
      md := default
      isFunctional := false
    }

    return (proc, {newctx with variableTypes := []})

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

def preludeSignatureToPythonFunctionDecl (prelude : Core.Program) : List PythonFunctionDecl :=
  prelude.decls.filterMap fun decl =>
    match Core.Program.Procedure.find? prelude decl.name with
    | some proc =>
      let inputTypes := proc.header.inputs.values.map getTypeName
      let inputnames := proc.header.inputs.keys.map (λ n => n.name)
      let outputtypes := proc.header.outputs.values.map getTypeName
      let noneexpr : Python.expr SourceRange := .Constant default (.ConNone default) default
      some {
        name:= proc.header.name.name
        args:= (inputnames.zip inputTypes).map (λ(n,t) => (n,t,noneexpr))
        hasKwargs := false
        ret := if outputtypes.length == 0 then none else outputtypes[0]!
      }
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
      if argsList.val.size > 0 then
        for arg in argsList.val.toList.tail! do
          match arg with
          | .mk_arg _ paramName paramAnnotation _ =>
            let paramType ← match paramAnnotation.val with
              | some annot => translateType ctx (pyExprToString annot)
              | none => .ok (mkCoreType PyLauType.Any)  -- Default to PyAnyType
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
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    return {
      name := methodName
      inputs := inputs
      outputs := outputs
      preconditions := [mkStmtExprMd (StmtExpr.LiteralBool true)]
      determinism := .nondeterministic
      isFunctional := false
      decreases := none
      body := .Transparent bodyBlock
      md := default
    }
  | _ => throw (.internalError "Expected FunctionDef for method")

/-- Extract fields from __init__ method body by scanning for self.field : type = expr patterns -/
def extractFieldsFromInit (ctx : TranslationContext) (initBody : Array (Python.stmt SourceRange))
    : Except TranslationError (List Field) := do
  let mut fields : List Field := []
  for stmt in initBody do
    match stmt with
    | .AnnAssign _ (.Attribute _ (.Name _ selfName _) attr _) annotation _ _ =>
      if selfName.val == "self" then
        let fieldType ← translateType ctx (pyExprToString annotation)
        fields := fields ++ [{
          name := attr.val
          type := fieldType
          isMutable := true
        }]
    | _ => pure ()
  return fields

/-- Translate a Python class to a Laurel CompositeType -/
def translateClass (ctx : TranslationContext) (classStmt : Python.stmt SourceRange)
    : Except TranslationError CompositeType := do
  match classStmt with
  | .ClassDef _ className _bases _ body _ _ =>
    let className := className.val
    let ctx := {ctx with currentClassName:= className}
    let classFunDecls : List PythonFunctionDecl ← body.val.toList.filterMapM (λ s => do match s with
      | .FunctionDef _ _ _ _ _ _ _ _ =>
          let funcDecl ← pyFuncDefToPythonFunctionDecl ctx s
          .ok (some (funcDecl))
      | _ => .ok none)
    let ctx := {ctx with functionSignatures:= ctx.functionSignatures ++ classFunDecls}
    -- Extract fields from __init__ method body
    let mut fields : List Field := []
    for stmt in body.val do
      match stmt with
      | .FunctionDef _ name _ initBody _ _ _ _ =>
        if name.val == "__init__" then
          let initFields ← extractFieldsFromInit ctx initBody.val
          fields := fields ++ initFields
      | _ => pure ()

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

    return {
      name := className
      extending := []  -- No inheritance support for now
      fields := fields
      instanceProcedures := instanceProcedures
    }
  | _ => throw (.internalError "Expected ClassDef")

def getFunctions (decls: List Core.Decl) : List String :=
  decls.filterMap (λ decl =>
    match decl.kind with
        |.func => some decl.name.name
        | _ => none)

def getDatatypeFunctions (decls: List Core.Decl) : List String :=
  decls.flatMap (λ decl =>
    match h: decl.kind with
        |.type =>
          let typedec := decl.getTypeDecl (by simp_all)
          match typedec with
          | .data dtypes =>
            let constructors := dtypes.flatMap (λ t => t.constrs.map (λ c => c.name.name))
            let destructors := dtypes.flatMap (λ t => (t.constrs.flatMap (λ c => c.args.map (fun (n, _) => t.name ++ ".." ++ n.name))))
            let testers := dtypes.flatMap (λ t => t.constrs.map (λ c => c.testerName))
            constructors ++ destructors ++ testers
          | _ => []
        | _ => [])


def getPreludeFunctions (prelude: Core.Program) : List String := (getFunctions prelude.decls) ++ (getDatatypeFunctions prelude.decls)

/-- Translate Python module to Laurel Program -/
def pythonToLaurel (prelude: Core.Program)
    (pyModule : Python.Command SourceRange)
    (prev_ctx: Option TranslationContext:= none)
    (filePath : String := "")
    (overloadTable : Specs.ToLaurel.OverloadTable := {})
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

    -- FIRST PASS: Collect all class definitions
    let mut compositeTypes : List CompositeType := []
    for stmt in body.val do
      match stmt with
      | .ClassDef _ _ _ _ _ _ _ =>
        -- Create initial context with just prelude info for class translation
        let initCtx : TranslationContext := {
          preludeProcedures := preludeProcedures,
          preludeTypes := preludeTypes,
          compositeTypes := compositeTypes,
          filePath := filePath
        }
        let composite ← translateClass initCtx stmt
        compositeTypes := compositeTypes ++ [composite]
      | _ => pure ()

    let mut ctx : TranslationContext := match prev_ctx with
    | some prev_ctx => prev_ctx
    | _ =>
    {
      currentClassName := none,
      preludeProcedures := preludeProcedures,
      functionSignatures := preludeSignatureToPythonFunctionDecl prelude
      preludeFunctions := getPreludeFunctions prelude
      preludeTypes := preludeTypes,
      userFunctions := userFunctions,
      compositeTypes := compositeTypes,
      overloadTable := overloadTable,
      filePath := filePath
    }

    -- Separate functions from other statements
    let mut procedures : List Procedure := []
    let mut otherStmts : List (Python.stmt SourceRange) := []

    for stmt in body.val do
      match stmt with
      | .FunctionDef _ _ _ fbody _ _ _ _ =>
        let funcDecl ←  pyFuncDefToPythonFunctionDecl ctx stmt
        let proc ← translateFunction ctx funcDecl fbody.val.toList
        ctx := {ctx with functionSignatures:= ctx.functionSignatures ++ [funcDecl]}
        procedures := procedures ++ [proc.fst]
      | .ClassDef _ _ _ _ _ _ _ =>
        pure ()  -- Already processed in first pass
      | _ =>
        otherStmts := otherStmts ++ [stmt]

    ctx := {ctx with variableTypes:= [("nullcall_ret", PyLauType.Any)]}
    let (_, bodyStmts) ← translateStmtList ctx otherStmts
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyStmts := mkStmtExprMd (.LocalVariable "__name__" AnyTy (some <| strToAny "__main__")) :: bodyStmts
    let bodyStmts := (mkStmtExprMd (.LocalVariable "nullcall_ret" AnyTy (some AnyNone))) :: bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    let mainProc : Procedure := {
      name := "__main__",
      inputs := [],
      outputs := [],
      preconditions := [],
      determinism := .deterministic none, --TODO: need to set reads
      decreases := none,
      body := .Transparent bodyBlock
      md := default
      isFunctional := false
      }

    let preludeFunctions : List Procedure := (getPreludeFunctions prelude).map (λ funcname =>
    {
      name := {text:= funcname} ,
      inputs := [],
      outputs := [],
      preconditions := [],
      determinism := .deterministic none, --TODO: need to set reads
      decreases := none,
      body := .External
      md := default
      isFunctional := true
      }
    )

    let program : Laurel.Program := {
      staticProcedures := preludeFunctions ++ procedures ++ [mainProc]
      staticFields := []
      types := compositeTypes.map TypeDefinition.Composite
      constants := []
    }

    return (program, ctx)

  | _ => throw (.internalError "Expected Module")


end Strata.Python

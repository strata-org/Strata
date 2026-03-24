/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Elab
public import Strata.DDM.AST
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.LaurelToCoreTranslator
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Python.PythonDialect
public import Strata.Languages.Python.PythonLaurelCorePrelude
public import Strata.Languages.Python.Specs.ToLaurel
public import Strata.Languages.Core.Program

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

public section

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
  preludeProcedures : Std.HashMap String CoreProcedureSignature := {}
  /-- Names of prelude functions (non-procedure callables) -/
  preludeFunctions : List String := []
  /-- Names of user-defined functions -/
  userFunctions : List String := []
  /-- Names of user-defined classes -/
  userClasses : List String := []
  /-- Map ClassName -> (FieldName -> HighType) for field access coercions and type inference -/
  classFieldHighType: Std.HashMap String (Std.HashMap String HighType) := {}
  /-- Names of prelude types -/
  preludeTypes : Std.HashSet String := {}
  /-- Overload dispatch table from PySpec: function name → overloads -/
  overloadTable : Specs.ToLaurel.OverloadTable := {}
  /-- Behavior for unmodeled functions -/
  unmodeledBehavior : UnmodeledFunctionBehavior := .havocOutputs
  /-- File path for source location metadata -/
  filePath : String := ""
  /-- Known composite type names (user-defined classes + PySpec types) -/
  compositeTypeNames : Std.HashSet String := {}
  /-- Track current class during method translation -/
  currentClassName : Option String := none
  loopBreakLabel : Option String := none
  loopContinueLabel : Option String := none
deriving Inhabited

/-! ## Error Handling -/

/-- Translation errors with context -/
inductive TranslationError where
  | unsupportedConstruct (msg : String) (pyAst : String)
  | typeError (msg : String)
  | nameError (name : String)
  | internalError (msg : String)
  /-- A detected bug in the user's Python code (e.g., missing required arguments,
      unknown method calls, invalid service names). Unlike other errors which indicate
      tool limitations, this means the analysis successfully identified a problem. -/
  | userPythonError (range : SourceRange := .none) (msg : String)
deriving Repr

def TranslationError.toString : TranslationError → String
  | .unsupportedConstruct msg ast => s!"Unsupported construct: {msg}\nAST: {ast}"
  | .typeError msg => s!"Type error: {msg}"
  | .nameError name => s!"Name not found: {name}"
  | .internalError msg => s!"Internal error: {msg}"
  | .userPythonError _ msg => s!"User code error: {msg}"

instance : ToString TranslationError where
  toString := TranslationError.toString

/-- Throw a user code error indicating a detected bug in the Python source. -/
def throwUserError [MonadExceptOf TranslationError m] (range : SourceRange := .none) (msg : String) : m α :=
  throw (.userPythonError range msg)

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

/-- Convert a Laurel HighType to a PyLauType string for type inference. -/
def highTypeToPyLauType : HighType → String
  | .TInt => PyLauType.Int
  | .TBool => PyLauType.Bool
  | .TString => PyLauType.Str
  | .TFloat64 => PyLauType.Any
  | .TReal => PyLauType.Any
  | .UserDefined name => name.text
  | _ => PyLauType.Any

/-- Map Python type strings to Core type names -/
def pythonTypeToCoreType (typeStr : String) : Option String :=
  match typeStr with
  | "Dict[str, Any]" => some PyLauType.DictStrAny
  | "List[str]" => some PyLauType.ListStr
  | "Any" => some PyLauType.Any
  | "datetime" => some PyLauType.Datetime
  | "timedelta" => some PyLauType.Int
  | _ => none

/-- Check if a type string is recognized (primitive, core mapping, or prelude/composite type). -/
def isKnownType (ctx : TranslationContext) (typeStr : String) : Bool :=
  typeStr ∈ ["int", "bool", "str"] ||
  (pythonTypeToCoreType typeStr).isSome ||
  typeStr ∈ ctx.compositeTypeNames ||
  typeStr ∈ ctx.preludeTypes

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
      -- Check if it matches a known composite type (user-defined or PySpec)
      if typeStr ∈ ctx.compositeTypeNames then
        .ok (mkHighTypeMd (.UserDefined typeStr))
      -- Check if it's a prelude type (Core types like DictStrAny)
      else if typeStr ∈ ctx.preludeTypes then
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

/-- Wrap a field access expression in the appropriate Any constructor based on HighType.
    After heap parameterization, field reads return concrete types (int, bool, etc.)
    but Python operators expect Any. This coercion bridges the gap. -/
def wrapFieldInAny (ty : HighType) (expr : StmtExprMd) : Except TranslationError StmtExprMd :=
  match ty with
  | .TInt => .ok <| mkStmtExprMd (.StaticCall "from_int" [expr])
  | .TBool => .ok <| mkStmtExprMd (.StaticCall "from_bool" [expr])
  | .TFloat64 => .ok <| mkStmtExprMd (.StaticCall "from_float" [expr])
  | .TReal => .ok <| mkStmtExprMd (.StaticCall "from_float" [expr])
  | .TString => .ok <| mkStmtExprMd (.StaticCall "from_string" [expr])
  | .TCore "Any" => .ok expr
  | other => .error (.typeError s!"wrapFieldInAny: no Any constructor for field type '{repr other}'")

/-- Look up a field's HighType, returning `none` if the class or field is not found. -/
def tryLookupFieldHighType (ctx : TranslationContext) (className fieldName : String) : Option HighType :=
  ctx.classFieldHighType[className]?.bind (·[fieldName]?)

/-- Look up a field's HighType, throwing a TranslationError if the class is known but the field is not. -/
def lookupFieldHighType (ctx : TranslationContext) (className fieldName : String) : Except TranslationError HighType :=
  match ctx.classFieldHighType[className]? with
  | none => .error (.typeError s!"lookupFieldHighType: class '{className}' not found in classFieldHighType")
  | some fields =>
    match fields[fieldName]? with
    | none => .error (.typeError s!"lookupFieldHighType: field '{fieldName}' not found on class '{className}'")
    | some ty => .ok ty

def NoError : StmtExprMd := mkStmtExprMd (StmtExpr.StaticCall "NoError" [])
def optNone := mkStmtExprMd (StmtExpr.StaticCall "None" [])

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
  match ctx.overloadTable[funcName]? with
  | none => return none
  | some fnOverloads =>
    let .isTrue _ := decideProp (args.size > 0)
      | throw (.typeError
          s!"Dispatched function '{funcName}' called with no \
            arguments (expected a string literal first argument)")
    match args[0] with
    | .Constant range (.ConString _ s) _ =>
      let some ident := fnOverloads[s.val]?
        | let knownServices := fnOverloads.keysArray.insertionSort.take 2
          let suffix := if fnOverloads.size > 2 then s!" ... ({fnOverloads.size} total)" else ""
          throwUserError range
              s!"'{funcName}' called with unknown string \"{s.val}\"; known services: {knownServices}{suffix}"
      let className :=
        if ident.pythonModule.isEmpty then
          ident.name
        else
          ident.pythonModule ++ "_" ++ ident.name
      return some className
    | _ => return none

/-! ## Expression Translation -/


/-- Check if a function has a model (is in prelude or user-defined) -/
def hasModel (ctx : TranslationContext) (funcName : String) : Bool :=
  funcName ∈ ctx.preludeProcedures || funcName ∈ ctx.userFunctions ||
  ctx.preludeFunctions.contains funcName || funcName ∈ ctx.compositeTypeNames

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

partial def translateSlice (ctx : TranslationContext) (start stop step: Option (expr SourceRange))
    : Except TranslationError StmtExprMd := do
    if step.isSome then
        throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr step)))
    match start, stop with
        | some start, some stop =>
            let start ← translateExpr ctx start
            let stop ← translateExpr ctx stop
            let start := mkStmtExprMd (.StaticCall "Any..as_int!" [start])
            let stop := mkStmtExprMd (.StaticCall "Some" [mkStmtExprMd (.StaticCall "Any..as_int!" [stop])])
            return mkStmtExprMd (.StaticCall "from_Slice" [start, stop])
        | some start, none =>
            let start ← translateExpr ctx start
            let start := mkStmtExprMd (.StaticCall "Any..as_int!" [start])
            return mkStmtExprMd (.StaticCall "from_Slice" [start, optNone])
        | none, some stop =>
            let start := mkStmtExprMd (.LiteralInt 0)
            let stop ← translateExpr ctx stop
            let stop := mkStmtExprMd (.StaticCall "Some" [mkStmtExprMd (.StaticCall "Any..as_int!" [stop])])
            return mkStmtExprMd (.StaticCall "from_Slice" [start, stop])
        | _ , _ =>
            let start := mkStmtExprMd (.LiteralInt 0)
            return mkStmtExprMd (.StaticCall "from_Slice" [start, optNone])

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
    let index ←  match slice with
      | .Slice _ start stop step => translateSlice ctx start.val stop.val step.val
      | _ => translateExpr ctx slice
    return mkStmtExprMd (.StaticCall "Any_get" [dictOrList, index])

  -- Attribute access: obj.attr or obj.method
  | .Attribute _ obj attr _ => do
    -- Check if this is self.field access in a method
    match obj with
    | .Name _ name _ =>
      if name.val == "self" && ctx.currentClassName.isSome then
        -- self.field in a method - translate to field access
        let fieldExpr := mkStmtExprMd (StmtExpr.FieldSelect
          (mkStmtExprMd (StmtExpr.Identifier "self"))
          attr.val)
        let className := ctx.currentClassName.get!
        let ty ← lookupFieldHighType ctx className attr.val
        wrapFieldInAny ty fieldExpr
      else
        -- Regular object.field access
        let objExpr ← translateExpr ctx obj
        let fieldExpr := mkStmtExprMd (StmtExpr.FieldSelect objExpr attr.val)
        let objType ← inferExprType ctx obj
        match tryLookupFieldHighType ctx objType attr.val with
          | some ty => wrapFieldInAny ty fieldExpr
          | none => return fieldExpr
    | _ =>
      -- Complex object expression - translate and access field
      let objExpr ← translateExpr ctx obj
      let fieldExpr := mkStmtExprMd (StmtExpr.FieldSelect objExpr attr.val)
      let objType ← inferExprType ctx obj
      match tryLookupFieldHighType ctx objType attr.val with
        | some ty => wrapFieldInAny ty fieldExpr
        | none => return fieldExpr

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
    let vty ← inferExprType ctx v
    match tryLookupFieldHighType ctx vty attr.val with
      | some ty => return (highTypeToPyLauType ty)
      | none => return PyLauType.Any
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
    (displayName : String := "")
    (callRange : SourceRange)
      : Except TranslationError ((List (Python.expr SourceRange)) × (List (Python.keyword SourceRange)) × Bool):= do
  match funcDecl with
  | some funcDecl =>
    let name := if displayName.isEmpty then funcDecl.name else displayName
    let kwordArgs := removePosargsFromKwargs kwords funcDecl
    if !funcDecl.hasKwargs && kwordArgs.length > 0 then
      let extraNames := kwordArgs.filterMap fun kw => match kw with
        | .mk_keyword _ name _ => name.val.map (·.val)
      throwUserError callRange
        s!"'{name}' called with unknown keyword arguments: {extraNames}"
    let kwords := pyKwordsToHashMap kwords
    let unprovidedPosArgs := funcDecl.args.drop posArgs.length
    --every unprovided positional args must have a default value in the function signature or be provided in the kwargs
    let missingArgs := unprovidedPosArgs.filter fun (name, _, d) =>
      !(name ∈ kwords.keys) && d.isNone
    if missingArgs.length > 0 then
      let missingNames := missingArgs.map (·.1)
      throwUserError callRange s!"'{name}' called with missing required arguments: {missingNames}"
    let filledPosArgs ←
      unprovidedPosArgs.mapM (λ (argName, _, d) =>
        match kwords.get? argName with
          | some expr => return expr
          | none => match d with
                | some val => return val
                | _ => throw (.typeError s!"'{name}' missing required argument '{argName}'"))
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

  let (funcName, opt_firstarg, unknowtype) ←  refineFunctionCallExpr ctx f
  if !hasModel ctx funcName then
    if opt_firstarg.isSome && !unknowtype then
      let (methodName, range) := match f with
        | .Attribute range _ attr _ => (attr.val, range)
        | _ => (funcName, .none)
      throwUserError range s!"Unknown method '{methodName}'"
    return mkStmtExprMd .Hole
  -- Step 3: translate the resolved call
  let methodName := match f with
    | .Attribute _ _ attr _ => attr.val
    | _ => funcName
  let callRange := match f with
    | .Attribute range _ _ _ => range
    | .Name range _ _ => range
    | _ => .none
  let funcDecl := ctx.functionSignatures.find? fun x => x.name == funcName
  let (args, kwords, funcdecl_hasKwargs) ←
    combinePositionalAndKeywordArgs args kwords funcDecl methodName callRange
  let trans_args ← args.mapM (translateExpr ctx)
  let trans_kwords ← translateKwargs ctx kwords
  let trans_kwords_exprs :=
    if kwords.length == 0 then
      if funcdecl_hasKwargs then [DictStrAny_empty] else []
    else [trans_kwords]
  match f with
  | .Name  _ _ _ =>  return mkStmtExprMd (StmtExpr.StaticCall funcName (trans_args ++ trans_kwords_exprs))
  | .Attribute _ val _attr _ =>
      let _target_trans ← translateExpr ctx val
      if opt_firstarg.isSome then
        return mkStmtExprMd (.Hole)
        --return mkStmtExprMd (StmtExpr.InstanceCall target_trans attr.val (trans_args ++ trans_kwords_exprs))
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
  match ctx.preludeProcedures[funcname]? with
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
  -- Tuple unpacking: a, b = rhs  →  tmp = rhs; a = tmp[0]; b = tmp[1]
  if let .Tuple _ elts _ := lhs then
    let sr := lhs.ann
    let freshVar := s!"tuple_{sr.start.byteIdx}"
    let tmpRef := expr.Name sr ⟨sr, freshVar⟩ (expr_context.Load sr)
    let (tmpCtx, tmpStmts) ← translateAssign ctx
      (expr.Name sr ⟨sr, freshVar⟩ (expr_context.Store sr)) annotation rhs md
    let mut curCtx := tmpCtx
    let mut stmts : List StmtExprMd := tmpStmts
    for h : i in [:elts.val.size] do
      let elt := elts.val[i]
      let idx := expr.Constant sr (constant.ConPos sr ⟨sr, i⟩) ⟨sr, none⟩
      let subscriptRhs := expr.Subscript sr tmpRef idx (expr_context.Load sr)
      let (newCtx, eltStmts) ← translateAssign curCtx elt none subscriptRhs md
      curCtx := newCtx
      stmts := stmts ++ eltStmts
    return (curCtx, stmts)
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
            if fnname.text ∈ ctx.compositeTypeNames then
              let newExpr := mkStmtExprMd (StmtExpr.New fnname)
              let varType := mkHighTypeMd (.UserDefined fnname)
              if n.val ∈ ctx.variableTypes.unzip.1 then
                let assignStmt := mkStmtExprMd (StmtExpr.Assign [targetExpr] newExpr)
                let initStmt := mkStmtExprMd (StmtExpr.InstanceCall (mkStmtExprMd (StmtExpr.Identifier n.val)) "__init__" args)
                [assignStmt, initStmt]
              else
                let newStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val varType (some newExpr))
                let initStmt := mkStmtExprMd (StmtExpr.InstanceCall (mkStmtExprMd (StmtExpr.Identifier n.val)) "__init__" args)
                [newStmt, initStmt]
            else if withException ctx fnname.text then
              [mkStmtExprMd (StmtExpr.Assign [targetExpr, maybeExceptVar] rhs_trans)]
            else [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)]
        | .New className =>
            if n.val ∈ ctx.variableTypes.unzip.1 then
              [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)]
            else
              let varType := mkHighTypeMd (.UserDefined className)
              let newStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val varType (some rhs_trans))
              [newStmt]
        | _ => [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)]
        newctx := match rhs_trans.val with
        | .StaticCall fnname _ =>
            if fnname.text ∈ ctx.compositeTypeNames then
              {newctx with variableTypes:= newctx.variableTypes ++ [(n.val, fnname.text)]}
            else newctx
        | .New className =>
            {newctx with variableTypes:= newctx.variableTypes ++ [(n.val, className.text)]}
        | _=> newctx
        if n.val ∈ newctx.variableTypes.unzip.1 then
          return (newctx, assignStmts)
        else
          let inferType ← inferExprType ctx rhs
          let type := match annotation with
          | none => inferType
          | some annotation =>
               let annStr := pyExprToString annotation
               -- If the annotation isn't a recognized type, prefer the
               -- inferred type from the RHS (e.g., overload dispatch).
               if isKnownType ctx annStr then annStr else inferType
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

def collectDeclaredNamesAndTypes (stmts : List (Python.stmt SourceRange)) : List (String × String) :=
  stmts.filterMap fun s => match s with
    | .AnnAssign _ target annotation _ _ =>
      some (pyExprToString target, pyExprToString annotation)
    | .Assign _ targets _ _ => targets.val.toList.head?.map (fun t => (pyExprToString t, PyLauType.Any))
    | _ => none

def createVarDeclStmtsAndCtx (ctx : TranslationContext) (newDecls : List (String × String))
    : List StmtExprMd × TranslationContext :=
  let newDecls := newDecls.foldl (fun acc (n, ty) =>
      if acc.any (fun (an, _) => an == n) || ctx.variableTypes.any (fun (vn, _) => vn == n)
      then acc else acc ++ [(n, ty)]) []
  let hoistedDecls : List StmtExprMd := newDecls.map fun (name, tyStr) =>
      let ty := if tyStr ∈ ctx.compositeTypeNames || tyStr == "PythonError" then
          mkHighTypeMd (.UserDefined tyStr)
        else AnyTy
      mkStmtExprMd (StmtExpr.LocalVariable (name : String) ty (some (mkStmtExprMd .Hole)))
  let hoistedCtx := { ctx with variableTypes := ctx.variableTypes ++
      (newDecls.map fun (n, ty) =>
        if ty ∈ ctx.compositeTypeNames || ty == "PythonError" then (n, ty) else (n, PyLauType.Any)) }
  (hoistedDecls, hoistedCtx)

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
    let newDecls := collectDeclaredNamesAndTypes (body.val.toList ++ orelse.val.toList)
    let (varDecls, ctx) := createVarDeclStmtsAndCtx ctx newDecls
    let (bodyCtx, bodyStmts) ← translateStmtList ctx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    -- Translate else branch if present
    let elseBlock ← if orelse.val.isEmpty then
      .ok none
    else do
      let (_, elseStmts) ← translateStmtList bodyCtx orelse.val.toList
      .ok (some (mkStmtExprMd (StmtExpr.Block elseStmts none)))
    let ifStmt := mkStmtExprMdWithLoc (StmtExpr.IfThenElse (Any_to_bool condExpr) bodyBlock elseBlock) md

    return (bodyCtx, varDecls ++ [ifStmt])

  -- While loop
  | .While _ test body _orelse => do
    -- Note: Python while-else not supported yet
    let condExpr ← translateExpr ctx test
    let newDecls := collectDeclaredNamesAndTypes body.val.toList
    let (varDecls, ctx) := createVarDeclStmtsAndCtx ctx newDecls
    let breakLabel := s!"loop_break_{test.toAst.ann.start.byteIdx}"
    let continueLabel := s!"loop_continue_{test.toAst.ann.start.byteIdx}"
    let loopCtx := { ctx with loopBreakLabel := some breakLabel, loopContinueLabel := some continueLabel }
    let (_, bodyStmts) ← translateStmtList loopCtx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts (some continueLabel))
    let whileStmt := mkStmtExprMd (StmtExpr.While (Any_to_bool condExpr) [] none bodyBlock)
    let whileWrapped := mkStmtExprMdWithLoc (StmtExpr.Block [whileStmt] (some breakLabel)) md
    return (loopCtx, varDecls ++ [whileWrapped])

  -- Return statement: assign to the LaurelResult output parameter, then exit $body.
  | .Return _ value => do
    let stmts ← match value.val with
      | some expr => do
        let e ← translateExpr ctx expr
        let assign := mkStmtExprMd (StmtExpr.Assign [mkStmtExprMd (StmtExpr.Identifier "LaurelResult")] e)
        .ok [assign, mkStmtExprMd (StmtExpr.Exit "$body")]
      | none => .ok [mkStmtExprMd (StmtExpr.Exit "$body")]
    return (ctx, stmts)

  -- Assert statement
  | .Assert _ test _msg => do
    let condExpr ← translateExpr ctx test
    let assertStmt := mkStmtExprMdWithLoc (StmtExpr.Assert (Any_to_bool condExpr)) md
    return (ctx, [assertStmt])

  --Ignore comments in source code
  | .Expr _ (.Constant _ (.ConString _ _) _) => return (ctx, [])

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
    let tryLabel := s!"try_end_{s.toAst.ann.start.byteIdx}"
    let catchersLabel := s!"exception_handlers_{s.toAst.ann.start.byteIdx}"

    -- Pre-scan for variable declarations in both branches so they are
    -- declared in the outer scope (Python scoping: variables assigned
    -- in try/except are visible after the block).
    let bodyDecls := collectDeclaredNamesAndTypes body.val.toList

    let errorVarDecls: List (String × String) := (handlers.val.toList.filterMap (λ h => match h with
          | .ExceptHandler _ _ errname _ => errname.val)).map (λ h => (h.val, "PythonError"))

    let handlerDecls := handlers.val.toList.flatMap fun h => match h with
      | .ExceptHandler _ _ _ hBody => collectDeclaredNamesAndTypes hBody.val.toList

    let allNewDecls := (bodyDecls ++ errorVarDecls ++ handlerDecls)
    let (hoistedDecls, hoistedCtx) := createVarDeclStmtsAndCtx ctx allNewDecls

    -- Translate try body (with hoisted context so inner decls become assigns)
    let (bodyCtx, bodyStmts) ← translateStmtList hoistedCtx body.val.toList

    -- Translate exception handlers
    let mut handlerCtx := bodyCtx
    let mut handlerStmts : List StmtExprMd := []
    for handler in handlers.val do
      match handler with
      | .ExceptHandler _ _ _ handlerBody =>
        let (hCtx, hStmts) ← translateStmtList hoistedCtx handlerBody.val.toList
        handlerCtx := hCtx
        handlerStmts := handlerStmts ++ hStmts

    -- Insert exception checks after each statement in try body
    let bodyStmtsWithChecks := bodyStmts.flatMap fun stmt =>
      let isException := mkStmtExprMd (StmtExpr.StaticCall "isError"
        [mkStmtExprMd (StmtExpr.Identifier "maybe_except")])
      let exitToHandler := mkStmtExprMd (StmtExpr.IfThenElse isException
        (mkStmtExprMd (StmtExpr.Exit catchersLabel)) none)
      [stmt, exitToHandler]

    -- Normal completion: exit the try block, skipping handlers
    let exitTry := mkStmtExprMd (StmtExpr.Exit tryLabel)

    -- catchers block: body + exit try (normal path)
    let catchersBlock := mkStmtExprMd (StmtExpr.Block
      (bodyStmtsWithChecks ++ [exitTry]) (some catchersLabel))

    -- try block: catchers block + handler code
    let tryBlock := mkStmtExprMdWithLoc (StmtExpr.Block
      ([catchersBlock] ++ handlerStmts) (some tryLabel)) md
    let mergedVars := bodyCtx.variableTypes ++
      (handlerCtx.variableTypes.filter fun (n, _) =>
        !bodyCtx.variableTypes.any fun (bn, _) => bn == n)
    let finalCtx := { bodyCtx with variableTypes := mergedVars }
    return (finalCtx, hoistedDecls ++ [tryBlock])

  | .Raise _ _ _ => return (ctx, [mkStmtExprMd .Hole])

  -- With statement: with EXPR as VAR: BODY
  -- Desugars to: mgr = EXPR; VAR = mgr.__enter__(); BODY; mgr.__exit__()
  | .With _ items body _ => do
    let mut setupStmts : List StmtExprMd := []
    let mut cleanupStmts : List StmtExprMd := []
    let mut currentCtx := ctx
    for item in items.val do
      match item with
      | .mk_withitem _ ctxExpr optVars =>
        let mgrName := s!"with_mgr_{ctxExpr.toAst.ann.start.byteIdx}"
        let mgrExpr ← translateExpr currentCtx ctxExpr
        let mgrTy ← inferExprType currentCtx ctxExpr
        let mgrLauTy ← translateType currentCtx mgrTy
        let mgrDecl := mkStmtExprMd (StmtExpr.LocalVariable mgrName mgrLauTy (some mgrExpr))
        let mgrRef := mkStmtExprMd (StmtExpr.Identifier mgrName)
        currentCtx := {currentCtx with variableTypes := currentCtx.variableTypes ++ [(mgrName, mgrTy)]}
        let enterCall := mkStmtExprMd (StmtExpr.InstanceCall mgrRef "__enter__" [])
        match optVars.val with
        | some varExpr =>
          let varName := pyExprToString varExpr
          if varName ∈ currentCtx.variableTypes.unzip.fst then
            let assignStmt := mkStmtExprMd (StmtExpr.Assign
              [mkStmtExprMd (StmtExpr.Identifier varName)] enterCall)
            setupStmts := setupStmts ++ [mgrDecl, assignStmt]
          else
            let varDecl := mkStmtExprMd (StmtExpr.LocalVariable varName AnyTy (some enterCall))
            currentCtx := {currentCtx with variableTypes := currentCtx.variableTypes ++ [(varName, PyLauType.Any)]}
            setupStmts := setupStmts ++ [mgrDecl, varDecl]
        | none =>
          setupStmts := setupStmts ++ [mgrDecl, enterCall]
        cleanupStmts := cleanupStmts ++ [mkStmtExprMd (StmtExpr.InstanceCall mgrRef "__exit__" [])]
    let (bodyCtx, bodyStmts) ← translateStmtList currentCtx body.val.toList
    let block := mkStmtExprMdWithLoc (StmtExpr.Block (setupStmts ++ bodyStmts ++ cleanupStmts) none) md
    return (bodyCtx, [block])

  -- For loop: for target in iter: body (target may be any assignment target)
  -- Abstract: execute body once with havoc'd target, then havoc all modified variables
  -- This is sound: if there are 0 iterations, we havoc; if >0, we execute once and havoc
  | .For _ target iter body _orelse _ => do
    -- The iterator expression (we abstract it away)
    let _iterExpr ← translateExpr ctx iter
    let newDecls := collectDeclaredNamesAndTypes body.val.toList
    let (varDecls, ctx) := createVarDeclStmtsAndCtx ctx newDecls
    -- Create context with target(s) and loop labels
    let breakLabel := s!"for_break_{iter.toAst.ann.start.byteIdx}"
    let continueLabel := s!"for_continue_{iter.toAst.ann.start.byteIdx}"
    -- Havoc the target(s) (Ellipsis always translates to Hole)
    let sr := target.ann
    let holeRhs := expr.Constant sr (constant.ConEllipsis sr) ⟨sr, none⟩
    let (bodyCtxNoLabels, targetDecls) ← translateAssign ctx target none holeRhs md
    let bodyCtx := { bodyCtxNoLabels with
      loopBreakLabel := some breakLabel
      loopContinueLabel := some continueLabel }
    let (finalCtx, bodyStmts) ← translateStmtList bodyCtx body.val.toList
    let innerBlock := mkStmtExprMd (StmtExpr.Block bodyStmts (some continueLabel))
    let loopBlock := mkStmtExprMdWithLoc (StmtExpr.Block [innerBlock] (some breakLabel)) md
    return (finalCtx, targetDecls ++ varDecls ++ [loopBlock])

  | .Break _ =>
    match ctx.loopBreakLabel with
    | some lbl => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Exit lbl) md])
    | none => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Assert (mkStmtExprMd .Hole)) md])
  | .Continue _ =>
    match ctx.loopContinueLabel with
    | some lbl => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Exit lbl) md])
    | none => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Assert (mkStmtExprMd .Hole)) md])

  -- Augmented assignment: x += expr  →  x = x op expr
  | .AugAssign _ target op value => do
    let targetExpr ← translateExpr ctx target
    let valueExpr ← translateExpr ctx value
    let rhs := match op with
      | .Add _      => mkStmtExprMd (StmtExpr.StaticCall "PAdd"      [targetExpr, valueExpr])
      | .Sub _      => mkStmtExprMd (StmtExpr.StaticCall "PSub"      [targetExpr, valueExpr])
      | .Mult _     => mkStmtExprMd (StmtExpr.StaticCall "PMul"      [targetExpr, valueExpr])
      | .FloorDiv _ => mkStmtExprMd (StmtExpr.StaticCall "PFloorDiv" [targetExpr, valueExpr])
      | .Mod _      => mkStmtExprMd (StmtExpr.StaticCall "PMod"      [targetExpr, valueExpr])
      | _           => mkStmtExprMd .Hole
    let assignStmt := mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] rhs) md
    return (ctx, [assignStmt])

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
    let args := if ctx.currentClassName.isSome then args_trans.fst.tail else args_trans.fst
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
def translateFunction (ctx : TranslationContext) (sourceRange: SourceRange) (funcDecl : PythonFunctionDecl) (body: List (Python.stmt SourceRange))
    : Except TranslationError (Laurel.Procedure × TranslationContext) := do

    -- Translate parameters
    let mut inputs : List Parameter := []

    inputs := funcDecl.args.map (fun (name, ty, _) =>
        if ty ∈ ctx.compositeTypeNames then
          { name := name, type := mkHighTypeMd (.UserDefined ty) }
        else
          { name := name, type := AnyTy})
    if funcDecl.hasKwargs then
      let paramType ← translateType ctx PyLauType.DictStrAny
      inputs:= inputs ++ [{ name := "kwargs", type := paramType }]

    -- Translate return type


    -- Declare an output parameter when the function has a return type annotation.
    -- Return statements explicitly assign to LaurelResult and exit $body.
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
      md := sourceRangeToMetaData ctx.filePath sourceRange
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
        | _ => continue  -- Skip non-simple targets, consistent with extractFieldsFromInit

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
          | _ => [{name := "LaurelResult", type := AnyTy}])
      | none => pure []

    -- Translate method body with class context
    let ctxWithClass := {ctx with currentClassName := some className}
    let (_, bodyStmts) ← translateStmtList ctxWithClass body.val.toList
    let bodyStmts := prependExceptHandlingHelper bodyStmts
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)

    let md := sourceRangeToMetaData ctx.filePath methodStmt.ann
    return {
      name := methodName
      inputs := inputs
      outputs := outputs
      preconditions := [mkStmtExprMd (StmtExpr.LiteralBool true)]
      determinism := .nondeterministic
      isFunctional := false
      decreases := none
      body := .Transparent bodyBlock
      md := md
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
    : Except TranslationError (CompositeType × List Procedure) := do
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
    -- Extract fields from class-level annotations and __init__ body, with dedup
    let classLevelFields ← extractClassFields ctx body.val
    let mut fields := classLevelFields
    for stmt in body.val do
      match stmt with
      | .FunctionDef _ name _ initBody _ _ _ _ =>
        if name.val == "__init__" then
          let initFields ← extractFieldsFromInit ctx initBody.val
          -- Only add fields not already declared at class level
          for f in initFields do
            unless fields.any (fun existing => existing.name.text == f.name.text) do
              fields := fields ++ [f]
      | _ => pure ()

    -- Populate field type maps so method bodies can wrap field accesses in Any coercions
    let classFields := fields.foldl (fun m f => m.insert f.name.text f.type.val) (ctx.classFieldHighType[className]?.getD {})
    let ctx := {ctx with classFieldHighType := ctx.classFieldHighType.insert className classFields}

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

    return ({
      name := className
      extending := []  -- No inheritance support for now
      fields := fields
      instanceProcedures := [] -- Laurel does not yet support instance procedures, so treat them as if they were static
    }, instanceProcedures)
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
def getPreludeProcedures (prelude: Core.Program) : List String :=
  prelude.decls.filterMap (λ decl =>
    match decl.kind with
        |.proc => some decl.name.name
        | _ => none)

/-- Information extracted from the prelude that `pythonToLaurel'` needs.
    This decouples the translation from a specific `Core.Program` representation,
    allowing the caller to supply prelude info from Laurel-level declarations. -/
structure PreludeInfo where
  /-- Type names (datatype, synonym, constructor names) -/
  types : Std.HashSet String := {}
  /-- Composite type names (need UserDefined in Laurel, not TCore) -/
  compositeTypes : Std.HashSet String := {}
  /-- Procedure names with input/output type signatures -/
  procedures : Std.HashMap String CoreProcedureSignature := {}
  /-- Procedure signatures as PythonFunctionDecl (with arg names) -/
  functionSignatures : List PythonFunctionDecl := []
  /-- Function names (Core functions + datatype constructors/destructors/testers) -/
  functions : List String := []
  /-- Procedure names (non-function callables) -/
  procedureNames : List String := []

/-- Extract `PreludeInfo` from a `Core.Program`. -/
def PreludeInfo.ofCoreProgram (prelude : Core.Program) : PreludeInfo where
  types := .ofList (extractPreludeTypes prelude)
  procedures := .ofList (extractPreludeProcedures prelude)
  functionSignatures := preludeSignatureToPythonFunctionDecl prelude
  functions := getPreludeFunctions prelude
  procedureNames := getPreludeProcedures prelude

/-- Convert a Laurel `HighType` to the same string name that `getTypeName` would
    produce from the corresponding Core `LMonoTy` after translation. -/
def getHighTypeName : Laurel.HighType → String
  | .TInt => "int"
  | .TBool => "bool"
  | .TString => "string"
  | .TVoid => "void"
  | .TFloat64 => "real"
  | .THeap => "Heap"
  | .TTypedField _ => "Field"
  | .TCore s => s
  | .UserDefined name => name.text
  | .TSet _ => "Map"
  | .TMap _ _ => "Map"
  | _ => "unknown"

/-- Extract `PreludeInfo` from a Laurel `Program`. -/
def PreludeInfo.ofLaurelProgram (prog : Laurel.Program) : PreludeInfo where
  types :=
    prog.types.foldl (init := {}) fun s td =>
      match td with
      | .Composite _ => s
      | .Constrained ct => s.insert ct.name.text
      | .Datatype dt => s.insert dt.name.text
  compositeTypes :=
    prog.types.foldl (init := {}) fun s td =>
      match td with
      | .Composite ct => s.insert ct.name.text
      | _ => s
  procedures :=
    prog.staticProcedures.foldl (init := {}) fun m p =>
      if p.body.isExternal || p.isFunctional then m
      else
        let ins := p.inputs.map fun param => getHighTypeName param.type.val
        let outs := p.outputs.map fun param => getHighTypeName param.type.val
        m.insert p.name.text { inputs := ins, outputs := outs }
  functionSignatures :=
    prog.staticProcedures.filterMap fun p =>
      if p.body.isExternal then none
      else
        let noDefault : Option (Python.expr SourceRange) := none
        let args := p.inputs.map fun param =>
          (param.name.text, getHighTypeName param.type.val, noDefault)
        let ret := p.outputs.head?.map fun param => getHighTypeName param.type.val
        some { name := p.name.text, args := args, hasKwargs := false, ret := ret }
  functions :=
    let funcNames := prog.staticProcedures.filterMap fun p =>
      if p.body.isExternal || !p.isFunctional then none else some p.name.text
    let dtFuncs := prog.types.flatMap fun td =>
      match td with
      | .Datatype dt =>
        let ctors := dt.constructors.map fun c => c.name.text
        let destrs := dt.constructors.flatMap fun c =>
          c.args.flatMap fun a =>
            [dt.name.text ++ ".." ++ a.name.text,
             dt.name.text ++ ".." ++ a.name.text ++ "!"]
        let testers := dt.constructors.map fun c => "is" ++ c.name.text
        ctors ++ destrs ++ testers
      | _ => []
    funcNames ++ dtFuncs
  procedureNames :=
    prog.staticProcedures.filterMap fun p =>
      if p.body.isExternal || p.isFunctional then none else some p.name.text

/-- Merge two `PreludeInfo` values by concatenating each field. -/
def PreludeInfo.merge (a b : PreludeInfo) : PreludeInfo where
  types := b.types.fold (init := a.types) fun s n => s.insert n
  compositeTypes := b.compositeTypes.fold (init := a.compositeTypes) fun s n => s.insert n
  procedures := b.procedures.fold (init := a.procedures) fun m k v => m.insert k v
  functionSignatures := a.functionSignatures ++ b.functionSignatures
  functions := a.functions ++ b.functions
  procedureNames := a.procedureNames ++ b.procedureNames

/-- Translate Python module to Laurel Program using pre-extracted prelude info. -/
def pythonToLaurel' (info : PreludeInfo)
    (pyModule : Python.Command SourceRange)
    (prev_ctx: Option TranslationContext := none)
    (filePath : String := "")
    (overloadTable : Specs.ToLaurel.OverloadTable := {})
    : Except TranslationError (Laurel.Program × TranslationContext) := do
  match pyModule with
  | .Module _ body _ => do
    -- Collect user function names (top-level and class methods)
    let userFunctions := body.val.toList.flatMap fun stmt =>
      match stmt with
      | .FunctionDef _ name _ _ _ _ _ _ => [name.val]
      | .ClassDef _ className _ _ clsBody _ _ =>
        clsBody.val.toList.filterMap fun s =>
          match s with
          | .FunctionDef _ methodName _ _ _ _ _ _ =>
            some (className.val ++ "_" ++ methodName.val)
          | _ => none
      | _ => []

    let pyErrorTy : CompositeType := {
      name := {text := "PythonError"}
      extending := []  -- No inheritance support for now
      fields := [{name:= "response", isMutable:= false, type:= AnyTy}]
      instanceProcedures := []
    }

    let mut procedures : List Procedure := []

    -- FIRST PASS: Collect all class definitions and field type info
    let mut compositeTypes : List CompositeType := [pyErrorTy]
    let mut compositeTypeNames := info.compositeTypes.insert "PythonError"
    let mut classFieldHighType : Std.HashMap String (Std.HashMap String HighType) := {}
    for stmt in body.val do
      match stmt with
      | .ClassDef _ _ _ _ _ _ _ =>
        let initCtx : TranslationContext := {
          preludeProcedures := info.procedures,
          preludeTypes := info.types,
          compositeTypeNames := compositeTypeNames,
          classFieldHighType := classFieldHighType,
          filePath := filePath
        }
        let (composite, _instanceProcedures) ← translateClass initCtx stmt
        -- TODO uncomment this line and resolve compilation issues
        -- procedures := procedures ++ _instanceProcedures
        compositeTypes := compositeTypes ++ [composite]
        compositeTypeNames := compositeTypeNames.insert composite.name.text
        -- Collect field types for Any coercions in field accesses
        let fieldMap := composite.fields.foldl (fun m f => m.insert f.name.text f.type.val) (classFieldHighType[composite.name.text]?.getD {})
        classFieldHighType := classFieldHighType.insert composite.name.text fieldMap
      | _ => pure ()

    let mut ctx : TranslationContext := match prev_ctx with
    | some prev_ctx => prev_ctx
    | _ =>
    {
      currentClassName := none,
      preludeProcedures := info.procedures,
      functionSignatures := info.functionSignatures
      preludeFunctions := info.functions
      preludeTypes := info.types,
      userFunctions := userFunctions,
      compositeTypeNames := compositeTypeNames,
      classFieldHighType := classFieldHighType,
      overloadTable := overloadTable,
      filePath := filePath
    }

    -- Separate functions from other statements
    let mut otherStmts : List (Python.stmt SourceRange) := []

    for stmt in body.val do
      match stmt with
      | .FunctionDef _ _ _ fbody _ _ _ _ =>
        let funcDecl ←  pyFuncDefToPythonFunctionDecl ctx stmt
        let proc ← translateFunction ctx stmt.ann funcDecl fbody.val.toList
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

    let md := sourceRangeToMetaData ctx.filePath { start := 0, stop := 0 }
    let mainProc : Procedure := {
      name := "__main__",
      inputs := [],
      outputs := [],
      preconditions := [],
      determinism := .deterministic none,
      decreases := none,
      body := .Transparent bodyBlock
      md := md
      isFunctional := false
    }

    let program : Laurel.Program := {
      staticProcedures := procedures ++ [mainProc]
      staticFields := []
      types := compositeTypes.map TypeDefinition.Composite
      constants := []
    }

    return (program, ctx)

  | _ => throw (.internalError "Expected Module")

/-- Generate External procedure stubs for prelude names so the Laurel
    `resolve` pass can see them. -/
def preludeStubs (info : PreludeInfo) : List Laurel.Procedure :=
  let functionStubs := info.functions.map fun funcname =>
    { name := { text := funcname }, inputs := [], outputs := [],
      preconditions := [], determinism := .deterministic none,
      decreases := none, body := .External, md := default,
      isFunctional := true }
  let procedureStubs := info.procedureNames.map fun funcname =>
    { name := { text := funcname }, inputs := [], outputs := [],
      preconditions := [], determinism := .deterministic none,
      decreases := none, body := .External, md := default,
      isFunctional := false }
  functionStubs ++ procedureStubs

/-- Translate Python module to Laurel Program.
    Delegates to `pythonToLaurel'` after extracting prelude info,
    then prepends External stubs so the Laurel resolve pass can
    see prelude names. -/
def pythonToLaurel (prelude: Core.Program)
    (pyModule : Python.Command SourceRange)
    (prev_ctx: Option TranslationContext := none)
    (filePath : String := "")
    (overloadTable : Specs.ToLaurel.OverloadTable := {})
    : Except TranslationError (Laurel.Program × TranslationContext) := do
  let info := PreludeInfo.ofCoreProgram prelude
  let (program, ctx) ← pythonToLaurel' info pyModule prev_ctx filePath overloadTable
  let stubs := preludeStubs info
  return ({ program with
    staticProcedures := stubs ++ program.staticProcedures }, ctx)


end -- public section
end Strata.Python

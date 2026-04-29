/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.OverloadTable
public import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Util.DecideProp

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

structure PyArgInfo where
  name : String
  source : Option FileRange
  laurelType : HighTypeMd
  typeTesters : Array String
  default : Option (Python.expr SourceRange)

structure PyRetInfo where
  source : Option FileRange
  laurelType : HighTypeMd
  typeTesters : Array String

structure PythonFunctionDecl where
  name : String
  args : List PyArgInfo
  kwargsName: Option String
  ret : Option PyRetInfo
deriving Inhabited

/-- A symbol imported from a PySpec module, carrying its Laurel-internal
    name and enough metadata for the translator to use it directly. -/
inductive ImportedSymbol where
  /-- A composite type (user-defined class from PySpec). -/
  | compositeType (laurelName : String)
  /-- A procedure with its signature and whether it can be inlined. -/
  | procedure (laurelName : String) (sig : CoreProcedureSignature)
      (inlinable : Bool)
  /-- A function (pure, functional callable). -/
  | function (laurelName : String)
deriving Inhabited

structure TranslationContext where
  variableTypes : List (String × String) := []
  /-- List of function signatures -/
  functionSignatures : List PythonFunctionDecl := []
  /-- Names of user-defined functions -/
  userFunctions : List String := []
  /-- Function that may return Any of exception -/
  maybeExceptionFunctions : List String := []
  /-- Names of user-defined classes -/
  userClasses : List String := []
  /-- Map ClassName -> (FieldName -> HighType) for field access coercions and type inference -/
  classFieldHighType: Std.HashMap String (Std.HashMap String HighType) := {}
  /-- Names of prelude types -/
  preludeTypes : Std.HashSet String := {}
  /-- Prelude procedure signatures (for multi-output detection) -/
  preludeProcedures : Std.HashMap String CoreProcedureSignature := {}
  /-- Overload dispatch table from PySpec: function name → overloads -/
  overloadTable : OverloadTable := {}
  /-- Behavior for unmodeled functions -/
  unmodeledBehavior : UnmodeledFunctionBehavior := .havocOutputs
  /-- File path for source location metadata -/
  filePath : String := ""
  /-- Maps Python-visible names to their structured symbol info. -/
  importedSymbols : Std.HashMap String ImportedSymbol := {}
  /-- Reverse map: laurelName → pythonName for compositeType entries.
      Precomputed from importedSymbols for O(1) reverse lookups. -/
  compositeTypeReverse : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}
  /-- Track current class during method translation -/
  currentClassName : Option String := none
  /-- Dispatch-detected field types: ClassName → FieldName → CompositeTypeName.
      Used only by refineFunctionCallExpr for self.field.method() dispatch. -/
  dispatchFieldTypes : Std.HashMap String (Std.HashMap String String) := {}
  /-- Suppress factory dispatch for the current expression (set when translating
      the RHS of a self.field assignment to avoid composite coercion issues). -/
  suppressDispatch : Bool := false
  /-- Classes involved in inheritance (have bases or are subclassed).
      Method calls on these classes may be dynamically dispatched,
      so call sites conservatively emit holes. -/
  classesInHierarchy : Std.HashSet String := {}
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

/-- Runtime assertion that a decidable proposition holds; throws an internal
    error when it does not.  Used to obtain array-size proofs that Lean cannot
    infer through mutable `for`-loop state.
    TODO: This is generically useful — consider moving to `Strata.Util`. -/
private def guardProp {p : Prop} [Decidable p] (msg : String)
    : Except TranslationError (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error (.internalError msg)

/-! ## Helper Functions -/

/-- Create metadata from a SourceRange for attaching to Laurel statements. -/
def sourceRangeToFileRange (filePath : String) (sr : SourceRange) : FileRange :=
  let uri : Uri := .file filePath
  ⟨ uri, sr ⟩

/-- Backward-compatible: create source from a SourceRange. -/
def sourceRangeToSource (filePath : String) (sr : SourceRange) : Option FileRange :=
  some (sourceRangeToFileRange filePath sr)

/-- Create a HighTypeMd with default metadata -/
def mkHighTypeMd (ty : HighType) : HighTypeMd :=
  { val := ty, source := none }

/-- Create a HighTypeMd with source location metadata. -/
def mkHighTypeMdWithLoc (ty : HighType) (source : Option FileRange) : HighTypeMd :=
  { val := ty, source := source }

def mkCoreType (s: String): HighTypeMd :=
  {val := .TCore s, source := none }

/-- Create a StmtExprMd with default metadata -/
def mkStmtExprMd (expr : StmtExpr) : StmtExprMd :=
  { val := expr, source := none }

/-- Create a StmtExprMd with source location metadata. -/
def mkStmtExprMdWithLoc (expr : StmtExpr) (source : Option FileRange) : StmtExprMd :=
  { val := expr, source := source }

/-- Mangle a class name and method name into a flat procedure name: `ClassName@methodName`. -/
def manglePythonMethod (className : String) (methodName : String) : String :=
  className ++ "@" ++ methodName

/-- Build a StaticCall for an instance method: ClassName@methodName(self, args...).
    For Any-typed receivers (no model available), returns a Hole instead. -/
def mkInstanceMethodCall (className : String) (methodName : String)
    (self : StmtExprMd) (args : List StmtExprMd)
    (source : Option FileRange := none) : StmtExprMd :=
  if className == "Any" then mkStmtExprMdWithLoc .Hole source
  else mkStmtExprMdWithLoc (StmtExpr.StaticCall (manglePythonMethod className methodName) (self :: args)) source

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

def PyLauType.None := "None"
def PyLauType.Int := "int"
def PyLauType.Bool := "bool"
def PyLauType.Str := "str"
def PyLauType.Float := "float"
def PyLauType.Bytes := "bytes"
def PyLauType.Datetime := "datetime"
def PyLauType.DictStrAny := "DictStrAny"
def PyLauType.ListAny := "ListAny"
def PyLauType.ListStr := "ListStr"
def PyLauType.Package := "Package"
def PyLauType.Any := "Any"
def AnyConstructor.None := "from_None"

def isOfAnyType (ty: String): Bool := ty ∈ [PyLauType.None, PyLauType.Bool, PyLauType.Int, PyLauType.Float,
                           PyLauType.Str, PyLauType.Datetime, PyLauType.Bytes, PyLauType.ListAny, PyLauType.DictStrAny, PyLauType.Any]

def pyLauTypeTesters (tys : List String) : Array String :=
  tys.foldl (init := #[]) fun acc ty =>
    if isOfAnyType ty && ty ≠ "Any" then acc.push ("Any..isfrom_" ++ ty) else acc

def PyLauFuncReturnVar := "LaurelResult"

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
  | "None" => some PyLauType.Any
  | "datetime" => some PyLauType.Datetime
  | "timedelta" => some PyLauType.Int
  | _ => none

/-- Check if a type string is recognized (primitive, core mapping, or prelude/composite type). -/
def isKnownType (ctx : TranslationContext) (typeStr : String) : Bool :=
  typeStr ∈ ["int", "bool", "str"] ||
  (pythonTypeToCoreType typeStr).isSome ||
  typeStr ∈ ctx.importedSymbols ||
  typeStr ∈ ctx.preludeTypes

/-- Translate Python type annotation to Laurel HighType -/
def translateType (ctx : TranslationContext) (typeStr : String) : Except TranslationError HighTypeMd :=
  -- Check if it matches a known composite type (user-defined or PySpec)
  match ctx.importedSymbols[typeStr]? with
    | some (ImportedSymbol.compositeType laurelName) =>
        .ok (mkHighTypeMd (.UserDefined laurelName))
    | some _ =>
        .error (.userPythonError .none s!"'{typeStr}' is not a type")
    | none =>
        -- Check if it's a prelude type (Core types like DictStrAny)
        if typeStr ∈ ctx.preludeTypes then
          .ok (mkCoreType typeStr)
        else
          -- Map it to a core PyAnyType
          .ok (mkCoreType PyLauType.Any)

/-- Translate a field type annotation: builtins become Any, composites stay Composite.
    This matches the two-kind system where method signatures use Any for builtins. -/
def translateFieldType (ctx : TranslationContext) (typeStr : String) : Except TranslationError HighTypeMd :=
  match ctx.importedSymbols[typeStr]? with
  | some (ImportedSymbol.compositeType laurelName) =>
    .ok (mkHighTypeMd (.UserDefined laurelName))
  | _ => .ok (mkCoreType PyLauType.Any)

def AnyTy := mkCoreType PyLauType.Any
def compositeToStringName (typeName : String) : String := "$composite_to_string_" ++ typeName
def compositeToStringAnyName (typeName : String) : String := "$composite_to_string_any_" ++ typeName

def isCompositeType (ctx : TranslationContext) (typeName : String) : Bool :=
  typeName != PyLauType.Any && (ctx.importedSymbols[typeName]?.any fun s =>
    match s with | .compositeType _ => true | _ => false)

def pyArgLaurelType (ctx : TranslationContext) (tys : List String) : HighTypeMd :=
  match tys with
  | [ty] => if isCompositeType ctx ty then mkHighTypeMd (.UserDefined { text := ty }) else AnyTy
  | _ => AnyTy
def strToAny (s: String) := mkStmtExprMd (.StaticCall "from_str" [mkStmtExprMd (StmtExpr.LiteralString s)])
def intToAny (i: Int) := mkStmtExprMd (.StaticCall "from_int" [mkStmtExprMd (StmtExpr.LiteralInt i)])
def boolToAny (b: Bool) := mkStmtExprMd (.StaticCall "from_bool" [mkStmtExprMd (StmtExpr.LiteralBool b)])
def AnyNone := mkStmtExprMd (.StaticCall "from_None" [])

/-- Parse a Python float literal string (e.g. "0.0", "1.5", "1e10") into a Decimal.
    Returns `none` for formats that cannot be represented (e.g. "inf", "nan").
    Handles underscores in numeric literals (e.g. "1_000.5") by stripping them.
    -- TODO: prove round-trip: ∀ s d, parseFloatString s = some d → the Decimal d
    -- represents the same real number as the Python float literal s. -/
private def parseFloatString (s : String) : Option Decimal := do
  -- Non-finite floats cannot be represented as Decimal
  let lower := s.toLower
  if lower == "inf" || lower == "-inf" || lower == "nan" then none
  else
  -- Strip underscores (Python allows e.g. 1_000.5)
  let s := s.replace "_" ""
  -- Split on 'e'/'E' for scientific notation
  let (coeffStr, expPart) :=
    match s.splitOn "e" with
    | [c, e] => (c, (if e.startsWith "+" then e.drop 1 else e).toInt?)
    | _ => match s.splitOn "E" with
      | [c, e] => (c, (if e.startsWith "+" then e.drop 1 else e).toInt?)
      | _ => (s, some 0)
  let sciExp ← expPart
  -- Parse the coefficient, which may have a decimal point
  match coeffStr.splitOn "." with
  | [intPart, fracPart] =>
    let digits := intPart ++ fracPart
    let mantissa ← digits.toInt?
    let exponent := sciExp - fracPart.length
    some { mantissa, exponent }
  | [intPart] =>
    let mantissa ← intPart.toInt?
    some { mantissa, exponent := sciExp }
  | _ => none

def floatToAny (d : Decimal) := mkStmtExprMd (.StaticCall "from_float" [mkStmtExprMd (StmtExpr.LiteralDecimal d)])
def Any_to_bool (b: StmtExprMd) := mkStmtExprMd (.StaticCall "Any_to_bool" [b])

/-- The set of PyLauType names that have runtime type-tester predicates
    (`Any..isfrom_<type>`). -/
private def pyLauTypesWithTesters : List String := ["int", "str", "bool", "float"]

/-- Return the Laurel type-tester predicate name for a Python type annotation, if known.
    E.g., `"int"` → `"Any..isfrom_int"`. The recognized type set is defined by
    `pyLauTypesWithTesters` above. -/
def typeTester? (typeName : String) : Option String :=
  if typeName ∈ pyLauTypesWithTesters then some ("Any..isfrom_" ++ typeName)
  else none

/-- Wrap a field access expression in the appropriate Any constructor based on HighType.
    After heap parameterization, field reads return concrete types (int, bool, etc.)
    but Python operators expect Any. This coercion bridges the gap. -/
def wrapFieldInAny (ty : HighType) (expr : StmtExprMd) : Except TranslationError StmtExprMd :=
  match ty with
  | .TInt => .ok <| mkStmtExprMd (.StaticCall "from_int" [expr])
  | .TBool => .ok <| mkStmtExprMd (.StaticCall "from_bool" [expr])
  | .TFloat64 => .ok <| mkStmtExprMd (.StaticCall "from_float" [expr])
  | .TReal => .ok <| mkStmtExprMd (.StaticCall "from_float" [expr])
  | .TString => .ok <| mkStmtExprMd (.StaticCall "from_str" [expr])
  | .TCore "Any" => .ok expr
  | .UserDefined name => .error (.unsupportedConstruct
    s!"Coercion from user-defined class '{name.text}' to Any is not yet supported" name.text)
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
def optNone := mkStmtExprMd (StmtExpr.StaticCall "OptNone" [])

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

/-- Extract a value from a dictionary for a function parameter.
    For required params, generates `Any_get(dict, from_str(key))` (with precondition).
    For optional params, generates `Any_get_or_none(dict, from_str(key))` (returns `None` if absent).
    Both operate on `Any`-typed dictionaries. -/
def DictStrAny_get_param (dict : StmtExprMd) (key : String) (isOptional : Bool) : StmtExprMd :=
  let func := if isOptional then "Any_get_or_none" else "Any_get"
  mkStmtExprMd (.StaticCall func [dict, strToAny key])

/-- Look up a function call in the overload dispatch table.
    Extracts the bare function name from the call target, then
    returns the class name if the first arg is a string literal
    matching an overload entry. -/
def resolveDispatch (ctx : TranslationContext)
    (f : Python.expr SourceRange)
    (args : Array (Python.expr SourceRange))
    (kwords : List (Python.keyword SourceRange) := [])
    : Except TranslationError (Option String) := do
  let funcName := match f with
    | .Attribute _ _ attr _ => attr.val
    | .Name _ n _ => n.val
    | _ => ""
  match ctx.overloadTable[funcName]? with
  | none => return none
  | some fnOverloads =>
    let kwPairs := kwords.map Python.keyword.nameAndValue
    let some firstArg := fnOverloads.findDispatchArg args kwPairs
      | let msg := match fnOverloads.paramName, kwPairs.filterMap (·.1) with
          | some expected, provided@(_ :: _) =>
            s!"Dispatched function '{funcName}' called with wrong \
              keyword argument, expected '{expected}' but got \
              '{String.intercalate "', '" provided}'"
          | _, _ =>
            s!"Dispatched function '{funcName}' called with no \
              arguments (expected a string literal first argument)"
        throw (.typeError msg)
    match firstArg with
    | .Constant range (.ConString _ s) _ =>
      let some ident := fnOverloads.entries[s.val]?
        | let knownServices := fnOverloads.entries.keysArray.insertionSort.take 2
          let suffix := if fnOverloads.entries.size > 2 then s!" ... ({fnOverloads.entries.size} total)" else ""
          throwUserError range
              s!"'{funcName}' called with unknown string \"{s.val}\"; known services: {knownServices}{suffix}"
      let className :=
        if ident.pythonModule.isEmpty then
          ident.name
        else
          ident.pythonModule.replace "." "_" ++ "_" ++ ident.name
      return some className
    | _ => return none

/-! ## Expression Translation -/


/-- Check if a function has a model (is in prelude or user-defined) -/
def hasModel (ctx : TranslationContext) (funcName : String) : Bool :=
  funcName ∈ ctx.importedSymbols || funcName ∈ ctx.userFunctions

/-- Check if a type's spec is exhaustive, meaning unmodeled method
    calls should be reported as errors. -/
def isExhaustiveType (ctx : TranslationContext) (typeName : String) : Bool :=
  ctx.exhaustiveClasses.contains typeName

def ListAny_mk (es: List StmtExprMd) : StmtExprMd := match es with
  | [] => mkStmtExprMd (.StaticCall "ListAny_nil" [])
  | e::t => mkStmtExprMd (.StaticCall "ListAny_cons" [e, ListAny_mk t])

def createBoolOrExpr (exprs: List StmtExprMd) : StmtExprMd :=
  match exprs with
  | [] => mkStmtExprMd (.LiteralBool false)
  | [expr] => expr
  | expr::exprs => mkStmtExprMd (.PrimitiveOp .Or [expr, createBoolOrExpr exprs])

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
  return  mkStmtExprMd (.StaticCall "from_DictStrAny" [DictStrAny_mk (keys.zip val_trans)])

partial def translateSlice (ctx : TranslationContext) (start stop step: Option (expr SourceRange))
    : Except TranslationError StmtExprMd := do
    if step.isSome then
        throw (.unsupportedConstruct "Expression type not yet supported" (toString (repr step)))
    match start, stop with
        | some start, some stop =>
            let start ← translateExpr ctx start
            let stop ← translateExpr ctx stop
            let start := mkStmtExprMd (.StaticCall "Any..as_int!" [start])
            let stop := mkStmtExprMd (.StaticCall "OptSome" [mkStmtExprMd (.StaticCall "Any..as_int!" [stop])])
            return mkStmtExprMd (.StaticCall "from_Slice" [start, stop])
        | some start, none =>
            let start ← translateExpr ctx start
            let start := mkStmtExprMd (.StaticCall "Any..as_int!" [start])
            return mkStmtExprMd (.StaticCall "from_Slice" [start, optNone])
        | none, some stop =>
            let start := mkStmtExprMd (.LiteralInt 0)
            let stop ← translateExpr ctx stop
            let stop := mkStmtExprMd (.StaticCall "OptSome" [mkStmtExprMd (.StaticCall "Any..as_int!" [stop])])
            return mkStmtExprMd (.StaticCall "from_Slice" [start, stop])
        | _ , _ =>
            let start := mkStmtExprMd (.LiteralInt 0)
            return mkStmtExprMd (.StaticCall "from_Slice" [start, optNone])

/-- Translate Python expression to Laurel StmtExpr -/
partial def translateExpr (ctx : TranslationContext) (e : Python.expr SourceRange)
    : Except TranslationError StmtExprMd := do
  let md := sourceRangeToSource ctx.filePath e.toAst.ann
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
  | .Constant _ (.ConFloat _ f) _ =>
    match parseFloatString f.val with
    | some d => return floatToAny d
    | none => return mkStmtExprMd .Hole

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
      | .Pow _ => .ok "PPow"
      | .LShift _ => .ok "PLShift"
      | .RShift _ => .ok "PRShift"
      | .BitAnd _ => return mkStmtExprMd .Hole --TODO: Adding BitVector subtype in Any type, then the related operations
      | .BitOr _ => return mkStmtExprMd .Hole
      | .BitXor _ => return mkStmtExprMd .Hole
      -- Unsupported for now
      | _ => throw (.unsupportedConstruct s!"Binary operator not yet supported: {repr op}" (toString (repr e)))
    return mkStmtExprMdWithLoc (StmtExpr.StaticCall preludeOpnames [leftExpr, rightExpr]) md

  -- Comparison operations
  | .Compare _ left ops comparators => do
    let n := ops.val.size
    if h: (n == 0 || comparators.val.size != n) then
      throw (.internalError "Compare: ops/comparators size mismatch")
    else
      have ⟨hN, hComp⟩ : 0 < n ∧ comparators.val.size = n := by
        simp_all [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]; omega
      -- Translate a single comparison operator to its Laurel prelude name.
      -- `is`/`is not` are only sound when the RHS is None, because Python's
      -- `is` checks object identity, not equality (e.g., True == 1 but
      -- True is not 1). In the Any value model, None is a singleton so
      -- identity and equality coincide for None comparisons.
      let cmpopName (i : Nat) (hi : i < n) : Except TranslationError String := do
        match ops.val[i]'hi with
          | .Eq _ => .ok "PEq"
          | .NotEq _ => .ok "PNEq"
          | .Lt _ => .ok "PLt"
          | .LtE _ => .ok "PLe"
          | .Gt _ => .ok "PGt"
          | .GtE _ => .ok "PGe"
          | .In _ => .ok "PIn"
          | .NotIn _ => .ok "PNotIn"
          | .Is _ => match comparators.val[i]'(by omega) with
              | .Constant _ (.ConNone _) _ => .ok "PEq"
              | _ => throw (.unsupportedConstruct "`is` is only supported with None" (toString (repr e)))
          | .IsNot _ => match comparators.val[i]'(by omega) with
              | .Constant _ (.ConNone _) _ => .ok "PNEq"
              | _ => throw (.unsupportedConstruct "`is not` is only supported with None" (toString (repr e)))
      -- Check if a Python expression is simple (no side effects when duplicated).
      -- Only `Name` and `Constant` are treated as simple. `Subscript` (e.g.,
      -- `a[0]`) and `Attribute` (e.g., `self.x`) are intentionally non-simple
      -- because Python's `__getitem__`/`__getattr__` can have side effects.
      -- Similarly, `BoolOp`, `UnaryOp`, and `BinOp` with simple sub-expressions
      -- are technically pure, but treating them as non-simple is correct since
      -- the temp variable overhead is negligible and avoids subtle bugs.
      let isSimple (pyExpr : Python.expr SourceRange) : Bool :=
        match pyExpr with
        | .Name .. | .Constant .. => true
        | _ => false
      -- Translate all operands
      let leftExpr ← translateExpr ctx left
      let mut compExprs : Array StmtExprMd := #[]
      for c in comparators.val do
        compExprs := compExprs.push (← translateExpr ctx c)
      let ⟨hCompSize⟩ ← guardProp (p := compExprs.size ≥ n) "compExprs size < n"
      -- For chained comparisons (n > 1), introduce temp variables for
      -- intermediate operands that are not simple names/literals.
      -- This preserves Python's evaluate-once semantics for side-effecting
      -- intermediate expressions (e.g., `a < f() < b` calls `f()` only once).
      let mut tempDecls : Array StmtExprMd := #[]
      let mut operandRefs : Array StmtExprMd := #[leftExpr]
      for h : i in [:n] do
        have hi : i < n := Membership.mem.upper h
        have : i < comparators.val.size := by omega
        have : i < compExprs.size := by omega
        let comp := compExprs[i]
        if n > 1 && i < n - 1 && !isSimple (comparators.val[i]) then
          -- TODO: Prove that this naming scheme cannot conflict with existing
          -- user variables. Shadowing is semantically fine, but a formal
          -- non-collision proof would require threading variable-scope info
          -- through the translator.
          let freshVar := s!"$cmp_tmp_{e.toAst.ann.start.byteIdx}_{i}"
          let varDecl := mkStmtExprMd (StmtExpr.LocalVariable freshVar AnyTy (some comp))
          tempDecls := tempDecls.push varDecl
          operandRefs := operandRefs.push (mkStmtExprMd (StmtExpr.Identifier freshVar))
        else
          operandRefs := operandRefs.push comp
      let ⟨hOpSize⟩ ← guardProp (p := operandRefs.size ≥ n + 1) "operandRefs size < n+1"
      -- Build pairwise comparisons and chain with PAnd.
      -- operandRefs has n+1 elements (leftExpr + n comparators).
      let mut pairs : Array StmtExprMd := #[]
      for h : i in [:n] do
        have hi : i < n := Membership.mem.upper h
        have : i < operandRefs.size := by omega
        have : i + 1 < operandRefs.size := by omega
        let opName ← cmpopName i hi
        let lhs := operandRefs[i]
        let rhs := operandRefs[i+1]
        pairs := pairs.push (mkStmtExprMd (StmtExpr.StaticCall opName [lhs, rhs]))
      let ⟨hPairsSize⟩ ← guardProp (p := pairs.size ≥ 1) "pairs is empty"
      -- Fold pairs with PAnd (pairs has n ≥ 1 elements)
      have : 0 < pairs.size := by omega
      let mut result := pairs[0]
      for h : i in [1:pairs.size] do
        have hi :  i < pairs.size := Membership.mem.upper h
        result := mkStmtExprMd (StmtExpr.StaticCall "PAnd" [result, pairs[i]])
      -- Wrap in a block if we emitted temp variable declarations
      if tempDecls.isEmpty then
        return { result with source := md }
      else
        return mkStmtExprMdWithLoc (StmtExpr.Block (tempDecls.toList ++ [result]) none) md

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
    return {result with source := md}

  -- Unary operations
  | .UnaryOp _ op operand => do
    let operandExpr ← translateExpr ctx operand
    let preludeOpnames ← match op with
      | .Not _ => .ok "PNot"
      | .USub _ => .ok "PNeg"
      | .Invert _ => .ok "PBitNot"
      | _ => throw (.unsupportedConstruct s!"Unary operator not yet supported: {repr op}" (toString (repr e)))
    return mkStmtExprMdWithLoc (StmtExpr.StaticCall preludeOpnames [operandExpr]) md

  -- FormattedValue (f-string interpolation {expr}) - convert to string-typed Any
  | .FormattedValue _ value _ _ =>
    let ty ← inferExprType ctx value
    let inner ← translateExpr ctx value
    let asAny ← if isCompositeType ctx ty then
        let fields := (ctx.classFieldHighType[ty]?.getD {}).toList
        let dict ← fields.foldlM (fun acc (fname, fty) =>
          return mkStmtExprMd (.StaticCall "DictStrAny_cons"
            [mkStmtExprMd (.LiteralString fname),
             ← wrapFieldInAny fty (mkStmtExprMd (.FieldSelect inner fname)), acc]))
          (mkStmtExprMd (.StaticCall "DictStrAny_empty" []))
        pure <| mkStmtExprMd (.StaticCall "from_ClassInstance"
          [mkStmtExprMd (.LiteralString ty), dict])
      else pure inner
    return mkStmtExprMd (.StaticCall "to_string_any" [asAny])

  -- JoinedStr (f-strings) - concatenate string parts via str.concat
  | .JoinedStr _ values =>
    if values.val.isEmpty then
      return strToAny ""
    else
      let parts ← values.val.toList.mapM (translateExpr ctx ·)
      let unwrap (e : StmtExprMd) := mkStmtExprMd (.StaticCall "Any..as_string!" [e])
      let concat := parts.foldl (fun acc part =>
        mkStmtExprMd (.PrimitiveOp .StrConcat [acc, unwrap part]))
        (mkStmtExprMd (.LiteralString ""))
      return mkStmtExprMd (.StaticCall "from_str" [concat])

  -- Interpolation / TemplateStr (Python 3.14+ t-strings) - not yet supported
  | .Interpolation .. => return mkStmtExprMd .Hole
  | .TemplateStr .. => return mkStmtExprMd .Hole

  | .IfExp _ cond thenb elseb =>
    let condExpr ← translateExpr ctx cond
    let thenExpr ← translateExpr ctx thenb
    let elseExpr ← translateExpr ctx elseb
    return mkStmtExprMdWithLoc (StmtExpr.IfThenElse (Any_to_bool condExpr) thenExpr elseExpr) md

  | .Call _ f args kwargs =>
      let result ← translateCall ctx f args.val.toList kwargs.val.toList
      return {result with source := md}

  -- Subscript access: dict['key'] or list[0]
  -- Abstract: return havoc'd value (sound for any dict/list operation)
  -- Note: Creates free variables which cause type errors in some contexts (if conditions)
  -- TODO: Handle by creating explicit variable declarations
  | .Subscript _ val slice _ =>
    let dictOrList ← translateExpr ctx val
    match slice with
      | .Slice _ start stop step =>
          let index ← translateSlice ctx start.val stop.val step.val
          return mkStmtExprMdWithLoc (.StaticCall "Any_get_slice" [dictOrList, index]) md
      | _ =>
          let index ← translateExpr ctx slice
          -- Emit bounds check for negative integer indices on lists (e.g., xs[-1])
          -- and convert to positive index: xs[-n] becomes xs[len(xs) - n].
          -- Skip for dicts, where negative integer keys are valid dict lookups.
          -- Note: Python's AST represents `-1` as UnaryOp(USub, Constant(1)),
          -- not Constant(-1), so we must match both forms.
          let valType := (inferExprType ctx val).toOption.getD PyLauType.Any
          let isDictType := valType == PyLauType.DictStrAny
          let negLitVal? := match slice with
            | .Constant _ (.ConNeg _ n) _ => some n.val
            | .UnaryOp _ (.USub _) (.Constant _ (.ConPos _ n) _) => some n.val
            | _ => none
          let index := match negLitVal? with
            | some n =>
              if isDictType then index
              else
                -- xs[-n] becomes xs[len(xs) - n]
                let listExpr := mkStmtExprMd (.StaticCall "Any..as_ListAny!" [dictOrList])
                let lenExpr := mkStmtExprMd (.StaticCall "List_len" [listExpr])
                let nLit := mkStmtExprMd (.LiteralInt n)
                mkStmtExprMd (.StaticCall "from_int"
                  [mkStmtExprMd (.PrimitiveOp .Sub [lenExpr, nLit])])
            | none => index
          return mkStmtExprMdWithLoc (.StaticCall "Any_get" [dictOrList, index]) md

  -- Attribute access: obj.attr or obj.method
  | .Attribute _ obj attr _ => do
    -- Check if this is self.field access in a method
    match obj with
    | .Name _ name _ =>
      if name.val == "self" && ctx.currentClassName.isSome then
        -- self.field in a method - field type is Any (builtins) or Composite (classes)
        let fieldExpr := mkStmtExprMd (StmtExpr.FieldSelect
          (mkStmtExprMd (StmtExpr.Identifier "self"))
          attr.val)
        let className := ctx.currentClassName.get!
        match tryLookupFieldHighType ctx className attr.val with
        | some (.UserDefined _) =>
          -- Only return Hole if this field has a dispatch type (tracked in
          -- dispatchFieldTypes). Method dispatch on self.field.method() is
          -- handled by refineFunctionCallExpr via dispatchFieldTypes.
          -- For non-dispatch UserDefined fields, return the field expression
          -- so standalone reads like `x = self.field` are not silently lost.
          let hasDispatch := ctx.dispatchFieldTypes[className]?.any (·.contains attr.val)
          if hasDispatch then
            return mkStmtExprMd .Hole
          else
            return fieldExpr
        | _ =>
          return fieldExpr
      else if isPackage ctx obj then
        -- FIXME: Module attribute (e.g., sys.argv): modules are not modeled as
        -- Laurel values, so return Hole like we do for unmodeled package calls.
        return mkStmtExprMd .Hole
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
  | .List _ elems _ => translateList ctx elems.val.toList

  -- Dict literal: {'a': 1}
  | .Dict _ keys vals => translateDictStrAny ctx keys.val.toList vals.val.toList

  -- Set literal: {1, 2, 3}
  -- Abstract: return havoc'd set (sound abstraction)
  | .Set .. => return mkStmtExprMd .Hole

  -- Tuple literal: (1, 2)
  | .Tuple _ elems _ => translateList ctx elems.val.toList

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

partial def reMapFunctionName (_ctx: TranslationContext) (fname: String) : String :=
  match fname with
  | "str" => "to_string_any"
  | "int" => "to_int_any"
  | "bool" => "to_bool_any"
  | "len" => "Any_len_to_Any"
  | "timedelta" => "timedelta_func" -- We handle timedelta as an int, not a class
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
  | .Constant _ (.ConNone _) _ => return PyLauType.None
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

  -- JoinedStr (f-strings) produce strings
  | .JoinedStr _ _ => return PyLauType.Str
  -- FormattedValue produces string-typed Any
  | .FormattedValue _ _ _ _ => return PyLauType.Str

  | .Call _ f args kwargs =>
    getFunctionReturnType ctx f args.val kwargs.val.toList

  | _ => return PyLauType.Any

partial def getFunctionReturnType (ctx : TranslationContext) (func: Python.expr SourceRange) (args : Array (Python.expr SourceRange))
    (kwords : List (Python.keyword SourceRange) := [])
    : Except TranslationError String := do
  match resolveDispatch ctx func args kwords with
  | .ok (some classname) => return classname
  | .error e => throw e
  | .ok none =>
    let (fname, _) ← refineFunctionCallExpr ctx func
    match ctx.functionSignatures.find? (λ f => f.name == fname) with
      | some funcDecl =>
        match funcDecl.ret with
        | some retInfo => return highTypeToPyLauType retInfo.laurelType.val
        | none => return PyLauType.Any
      | _ => return PyLauType.Any


/-
Python function call can be caller.function_name(arg1, arg2, ...)
If a is a variable, and type of a can be inferred, then the call should be translated to TypeOfcaller_function_name (caller, arg1, arg2)
If a is a variable, and type of a can NOT be inferred, then the call should be translated to AnyType_function_name (TypeOf(caller), caller, arg1, arg2)
If a is a package, this should be translated to a_function_name (arg1, arg2)
If the function_name is a class, add __init__ into it
The following function return a tuple (translated function name, first argument, is the first argument of unknown type)
-/

/-- Coerce an expression to Any if its inferred type is a Composite class.
    Composite values are replaced with a Hole (unconstrained Any value)
    since Composite→Any coercion is not yet modeled. This limits
    bug-finding ability but avoids type unification errors. -/
partial def coerceToAny (ctx : TranslationContext) (expr : Python.expr SourceRange)
    (translated : StmtExprMd) : Except TranslationError StmtExprMd := do
  let ty ← inferExprType ctx expr
  if isCompositeType ctx ty then
    pure <| mkStmtExprMd (.Hole)
  else pure translated

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
          -- Check if this is self.field where the field was initialized via
          -- dispatch (e.g. self.client = boto3.client('s3')).
          let dispatchTy : Option String := match v with
            | .Attribute _ (.Name _ selfName _) fieldAttr _ =>
              if selfName.val == "self" then
                match ctx.currentClassName with
                | some cn => ctx.dispatchFieldTypes[cn]?.bind (·[fieldAttr.val]?)
                | none => none
              else none
            | _ => none
          match dispatchTy with
          | some ty =>
            let resolvedTy :=
              match ctx.importedSymbols[ty]? with
              | some (ImportedSymbol.compositeType laurelName) => laurelName
              | _ => ty
            let unprefixedTy := ctx.compositeTypeReverse[ty]?
            -- Try three name-mangling strategies for the method:
            let candidates := [
              -- 1. Raw dispatch name from overload table (e.g., "s3_S3Client@method")
              manglePythonMethod ty callname,
              -- 2. Laurel-resolved name with module prefix (e.g., "boto3_s3_S3Client@method")
              manglePythonMethod resolvedTy callname] ++
              -- 3. Python-visible short name (e.g., "S3Client@method" from `from mod import S3Client`)
              (match unprefixedTy with | some u => [manglePythonMethod u callname] | none => [])
            let funcName := candidates.find? (ctx.importedSymbols.contains ·)
              |>.getD (manglePythonMethod resolvedTy callname)
            return (funcName, some v, false)
          | none =>
            return (manglePythonMethod "AnyTyInstance" callname, some v, true)
        else
          let resolvedTy :=
            match ctx.importedSymbols[callerTy]? with
            | some (ImportedSymbol.compositeType laurelName) => laurelName
            | _ => callerTy
          return (manglePythonMethod resolvedTy callname, some v, false)
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
        | some n => n.val ∉ funcDecl.args.map (·.name)
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
    if funcDecl.kwargsName.isNone && kwordArgs.length > 0 then
      let extraNames := kwordArgs.filterMap fun kw => match kw with
        | .mk_keyword _ name _ => name.val.map (·.val)
      throwUserError callRange
        s!"'{name}' called with unknown keyword arguments: {extraNames}"
    let kwords := pyKwordsToHashMap kwords
    -- Extra positional args beyond the signature are an arity error.
    if posArgs.length > funcDecl.args.length then
      throwUserError callRange
        s!"'{name}' called with too many positional arguments: expected at most {funcDecl.args.length}, got {posArgs.length}"
    let unprovidedPosArgs := funcDecl.args.drop posArgs.length
    --every unprovided positional args must have a default value in the function signature or be provided in the kwargs
    let missingArgs := unprovidedPosArgs.filter fun arg =>
      !(arg.name ∈ kwords.keys) && arg.default.isNone
    if missingArgs.length > 0 then
      let missingNames := missingArgs.map (·.name)
      throwUserError callRange s!"'{name}' called with missing required arguments: {missingNames}"
    let filledPosArgs ←
      unprovidedPosArgs.mapM (λ arg =>
        match kwords.get? arg.name with
          | some expr => return expr
          | none => match arg.default with
                | some val => return val
                | _ => throw (.typeError s!"'{name}' missing required argument '{arg.name}'"))
    let posArgs := posArgs ++ filledPosArgs
    return (posArgs, kwordArgs, funcDecl.kwargsName.isSome)
  | _ => return (posArgs, kwords, false)


/-- Translate an expression used as a method receiver, building FieldSelect
    chains for UserDefined composite fields without coercion. Falls back to
    translateExpr for non-composite or non-attribute expressions. -/
partial def translateExprAsReceiver (ctx : TranslationContext)
    (e : Python.expr SourceRange) : Except TranslationError StmtExprMd := do
  match e with
  | .Attribute _ obj fieldAttr _ =>
    let objType ← inferExprType ctx obj
    match tryLookupFieldHighType ctx objType fieldAttr.val with
    | some (.UserDefined _) =>
      let objExpr ← translateExprAsReceiver ctx obj
      pure <| mkStmtExprMd (StmtExpr.FieldSelect objExpr fieldAttr.val)
    | _ => translateExpr ctx e
  | _ => translateExpr ctx e

/-- Translate a Python call expression to Laurel.
    Tries factory dispatch, then method dispatch on typed variables,
    then falls back to a static call by flattened name. -/
partial def translateCall (ctx : TranslationContext)
                          (f : Python.expr SourceRange)
                          (args : List (Python.expr SourceRange))
                          (kwords : List (Python.keyword SourceRange))
    : Except TranslationError StmtExprMd := do
  -- Step 1: factory dispatch (e.g., boto3.client('iam'))
  -- Suppressed when translating the RHS of self.field assignments to avoid
  -- composite coercion issues; dispatch-initialized fields are tracked
  -- separately via dispatchFieldTypes.
  if !ctx.suppressDispatch then
    if let some className ← resolveDispatch ctx f args.toArray kwords then
      return mkStmtExprMd (.New className)
  -- Reset suppressDispatch so nested calls within the RHS are not affected
  let ctx := {ctx with suppressDispatch := false}
  -- Step 2: method call on typed variable (e.g., iam.get_role())
  --   Resolve to ClassName_method(obj, args)

  let (funcName, opt_firstarg, unknowtype) ←  refineFunctionCallExpr ctx f
  if !hasModel ctx funcName then
    if opt_firstarg.isSome && !unknowtype then
      -- Only report "Unknown method" when the receiver type has an
      -- exhaustive spec, meaning unmodeled methods are genuine errors.
      let typePrefix := funcName.splitOn "@" |>.head!
      if isExhaustiveType ctx typePrefix then
        let (methodName, range) := match f with
          | .Attribute range _ attr _ => (attr.val, range)
          | _ => (funcName, .none)
        throwUserError range s!"Unknown method '{methodName}'"
    -- Havoc the receiver since the unmodeled call may mutate it and
    -- value-typed locals are not reachable via heap havoc.
    let receiverHavoc := match f with
      | .Attribute _ (.Name _ receiverName _) _ _ =>
        if receiverName.val ∈ ctx.variableTypes.unzip.1 then
          [mkStmtExprMd (StmtExpr.Assign
            [mkStmtExprMd (StmtExpr.Identifier receiverName.val)]
            (mkStmtExprMd .Hole))]
        else []
      | _ => []
    let havocStmts := receiverHavoc
    if havocStmts.isEmpty then
      return mkStmtExprMd .Hole
    else
      return mkStmtExprMd (.Block (havocStmts ++ [mkStmtExprMd .Hole]) none)
  -- Step 3: translate the resolved call
  let methodName := match f with
    | .Attribute _ _ attr _ => attr.val
    | _ => funcName
  let callRange := match f with
    | .Attribute range _ _ _ => range
    | .Name range _ _ => range
    | _ => .none
  let funcDecl := ctx.functionSignatures.find? fun x => (x.name == funcName || x.name == funcName ++ "@__init__")
  if funcDecl.isNone && kwords.length > 0 then
    throwUserError f.ann s!"Undeclared function '{funcName}' called with keyword args"
  -- Emit the final call, handling Name vs Attribute dispatch and transparent procedures.
  let callMd := sourceRangeToSource ctx.filePath callRange
  let emitCall (callArgs : List StmtExprMd) : Except TranslationError StmtExprMd := do
    let mkCall (name : String) := mkStmtExprMdWithLoc (StmtExpr.StaticCall name callArgs) callMd
    -- Check for len() on Composite types (class instances without __len__)
    if funcName == "Any_len_to_Any" && args.length == 1 then
      match inferExprType ctx args[0]! with
      | .ok argType =>
        if isCompositeType ctx argType then
          throwUserError f.ann s!"len() is not supported on '{argType}' (no __len__ method)"
      | .error _ => pure ()
    match f with
    | .Name  _ _ _ =>
        -- If calling str() on a composite-typed variable, use $composite_to_string_any_<type>
        -- so that heap parameterization adds the heap dependency.
        let funcName' :=
          if funcName == "to_string_any" && args.length == 1 then
            match inferExprType ctx args[0]! with
            | .ok argType =>
              if isCompositeType ctx argType then
                compositeToStringAnyName argType
              else funcName
            | .error _ => funcName
          else funcName
        return mkCall funcName'
    | .Attribute _ val _attr _ =>
        let target_trans ← translateExprAsReceiver ctx val
        if opt_firstarg.isSome then
          if let some (ImportedSymbol.procedure _ _ true) := ctx.importedSymbols[funcName]? then
            return mkCall funcName
          else if funcName ∈ ctx.userFunctions then
            -- funcName is already resolved to "ClassName@method" using the
            -- receiver's *static* type (from refineFunctionCallExpr). If the
            -- class is involved in inheritance, the runtime type may differ
            -- (e.g., variable typed as Base could hold a Child instance),
            -- so the static resolution may be wrong. Emit a Hole in that case.
            let classPrefix := funcName.splitOn "@" |>.head!
            if ctx.classesInHierarchy.contains classPrefix then
              return mkStmtExprMdWithLoc (.Hole) callMd
            let callWithSelf := mkStmtExprMdWithLoc
              (StmtExpr.StaticCall funcName (target_trans :: callArgs)) callMd
            return callWithSelf
          else
            return mkStmtExprMdWithLoc (.Hole) callMd
        else return mkCall funcName
    | _ => throw (.unsupportedConstruct "Invalid call construct" (toString (repr f)))
  -- When ** is used at the call site and we have a known function signature,
  -- expand the dictionary into individual arguments using DictStrAny_get
  if isVarKwargs kwords && funcDecl.isSome then
    let funcDecl := funcDecl.get!
    let name := if methodName.isEmpty then funcDecl.name else methodName
    if args.length > funcDecl.args.length then
      throwUserError callRange
        s!"'{name}' called with too many positional arguments: expected at most {funcDecl.args.length}, got {args.length}"
    let trans_posArgs ← args.mapM (translateExpr ctx)
    let trans_dict ← translateVarKwargs ctx kwords
    let remainingParams := funcDecl.args.drop args.length
    let trans_dictArgs := remainingParams.map fun arg =>
      DictStrAny_get_param trans_dict arg.name arg.default.isSome
    let allArgs := trans_posArgs ++ trans_dictArgs
    let kwargsArg := if funcDecl.kwargsName.isSome then [trans_dict] else []
    -- Emit type assertions: if a key is present in the dict, its value
    -- must match the declared parameter type. This catches {"key": None}
    -- where the parameter type is str/int/bool/float.
    let mut typeAsserts : Array StmtExprMd := #[]
    let dictExpr := mkStmtExprMd (.StaticCall "Any..as_Dict!" [trans_dict])
    for arg in remainingParams do
      if arg.typeTesters.size > 0 then
        let keyPresent := mkStmtExprMd (.StaticCall "DictStrAny_contains"
          [dictExpr, mkStmtExprMd (.LiteralString arg.name)])
        let val := DictStrAny_get_param trans_dict arg.name true
        let checks := arg.typeTesters.map fun callee =>
          mkStmtExprMd (.StaticCall (mkId callee) [val])
        let isCorrectType := createBoolOrExpr checks.toList
        let cond := mkStmtExprMd (.PrimitiveOp .Implies [keyPresent, isCorrectType])
        typeAsserts := typeAsserts.push (mkStmtExprMd (.Assert { condition := cond }))
    let typeAssertsOrdered := typeAsserts.toList
    let call ← emitCall (allArgs ++ kwargsArg)
    if typeAssertsOrdered.isEmpty then
      return call
    else
      return mkStmtExprMd (.Block (typeAsserts.toList ++ [call]) none)
  else
  let (args, kwords, funcdecl_hasKwargs) ←
    combinePositionalAndKeywordArgs args kwords funcDecl methodName callRange
  let trans_args ← args.mapM (translateExpr ctx)
  let trans_kwords ← translateKwargs ctx kwords
  let trans_kwords_exprs :=
    if kwords.length == 0 then
      if funcdecl_hasKwargs then [DictStrAny_empty] else []
    else [trans_kwords]
  emitCall (trans_args ++ trans_kwords_exprs)


end

/-! ## Statement Translation

Translate Python statements to Laurel StmtExpr nodes.
These functions are mutually recursive.
-/

private def hasErrorOutput (sig : CoreProcedureSignature) : Bool :=
  sig.outputs.length > 0 && sig.outputs.getLast! == "Error"

def withException (ctx : TranslationContext) (funcname: String) : Bool :=
  match ctx.importedSymbols[funcname]? with
  | some (ImportedSymbol.function _) => false
  | some (ImportedSymbol.procedure _ sig _) => hasErrorOutput sig
  | _ =>
    match ctx.preludeProcedures[funcname]? with
    | some sig => hasErrorOutput sig
    | none => false

def freeVar (name: String) := mkStmtExprMd (.Identifier name)
def maybeExceptVar := freeVar "maybe_except"
def nullcall_var := freeVar "nullcall_ret"

partial def translateAssign  (ctx : TranslationContext)
                             (lhs: Python.expr SourceRange)
                             (annotation: Option (Python.expr SourceRange) )
                             (rhs: Python.expr SourceRange)
                             (source: Option FileRange)
                    : Except TranslationError (TranslationContext × List StmtExprMd × Bool) := do
  -- Returns (ctx, stmts, typeAssertSafe) where typeAssertSafe indicates
  -- whether a post-assignment type assertion on the target variable is valid.
  -- It is safe when translateAssign produces a simple assignment (the variable
  -- holds the assigned value), but not for complex translations like tuple
  -- unpacking or composite __init__ calls.
  -- Tuple unpacking: a, b = rhs  →  tmp = rhs; a = tmp[0]; b = tmp[1]
  if let .Tuple _ elts _ := lhs then
    let sr := lhs.ann
    let freshVar := s!"tuple_{sr.start.byteIdx}"
    let tmpRef := expr.Name sr ⟨sr, freshVar⟩ (expr_context.Load sr)
    let (tmpCtx, tmpStmts, _) ← translateAssign ctx
      (expr.Name sr ⟨sr, freshVar⟩ (expr_context.Store sr)) annotation rhs source
    let mut curCtx := tmpCtx
    let mut stmts : List StmtExprMd := tmpStmts
    for h : i in [:elts.val.size] do
      let elt := elts.val[i]
      let idx := expr.Constant sr (constant.ConPos sr ⟨sr, i⟩) ⟨sr, none⟩
      let subscriptRhs := expr.Subscript sr tmpRef idx (expr_context.Load sr)
      let (newCtx, eltStmts, _) ← translateAssign curCtx elt none subscriptRhs source
      curCtx := newCtx
      stmts := stmts ++ eltStmts
    return (curCtx, stmts, false)
  -- Suppress factory dispatch when translating the RHS of self.field assignments
  -- to avoid composite coercion issues; dispatch-initialized fields are tracked
  -- separately via dispatchFieldTypes for method resolution.
  let isSelfFieldAssign := match lhs with
    | .Attribute _ (.Name _ name _) _ _ => name.val == "self" && ctx.currentClassName.isSome
    | _ => false
  let rhsCtx := if isSelfFieldAssign then {ctx with suppressDispatch := true} else ctx
  let rhs_trans ←  translateExpr rhsCtx rhs
  -- When an unmodeled call produces a Hole, also havoc maybe_except since
  -- the call is a black box that could throw any exception.
  let rhsIsCall := match rhs with | .Call _ _ _ _ => true | _ => false
  if let .Hole := rhs_trans.val then
  {
    let exceptHavoc :=
      if rhsIsCall then
        [mkStmtExprMdWithLoc (StmtExpr.Assign [maybeExceptVar] (mkStmtExprMd (.Hole false none))) source]
      else []
    match lhs with
    | .Name _ n _ =>
      if n.val ∈ ctx.variableTypes.unzip.1 then
        let targetExpr := mkStmtExprMd (StmtExpr.Identifier n.val)
        return (ctx, [mkStmtExprMd (StmtExpr.Assign [targetExpr] rhs_trans)] ++ exceptHavoc, true)
      else
        -- Use type annotation if it matches a known composite type
        let annType := annotation.map (fun a => pyExprToString a) |>.getD "Any"
        let (varTy, trackType) ← match ctx.importedSymbols[annType]? with
          | some (ImportedSymbol.compositeType laurelName) =>
            pure (mkHighTypeMd (.UserDefined (mkId laurelName)), laurelName)
          | some _ =>
            throw (.userPythonError lhs.ann s!"'{annType}' is not a type")
          | _ => pure (AnyTy, "Any")
        let initStmt := mkStmtExprMd (StmtExpr.LocalVariable n.val varTy (mkStmtExprMd .Hole))
        let newctx := {ctx with variableTypes:=(n.val, trackType)::ctx.variableTypes}
        return (newctx, [initStmt] ++ exceptHavoc, true)
    | _ => return (ctx, [mkStmtExprMd .Hole] ++ exceptHavoc, false)
  }
  let mut newctx := ctx
  match lhs with
    | .Name _ n _ =>
        let targetExpr := mkStmtExprMd (StmtExpr.Identifier n.val)
        let assignStmts := match rhs_trans.val with
        | .StaticCall fnname args =>
            if let some (ImportedSymbol.compositeType laurelName) := ctx.importedSymbols[fnname.text]? then
              let resolvedId := mkId laurelName
              let newExpr := mkStmtExprMd (StmtExpr.New resolvedId)
              let varType := mkHighTypeMd (.UserDefined resolvedId)
              let selfRef := mkStmtExprMd (StmtExpr.Identifier n.val)
              let initStmt := mkInstanceMethodCall laurelName "__init__" selfRef args source
              if n.val ∈ ctx.variableTypes.unzip.1 then
                let assignStmt := mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] newExpr) source
                [assignStmt, initStmt]
              else
                let newStmt := mkStmtExprMdWithLoc (StmtExpr.LocalVariable n.val varType (some newExpr)) source
                [newStmt, initStmt]
            else if withException ctx fnname.text then
              [mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr, maybeExceptVar] rhs_trans) source]
            else
                [mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] rhs_trans) source]
        | .New className =>
            if n.val ∈ ctx.variableTypes.unzip.1 then
              [mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] rhs_trans) source]
            else
              let varType := mkHighTypeMd (.UserDefined className)
              let newStmt := mkStmtExprMdWithLoc (StmtExpr.LocalVariable n.val varType (some rhs_trans)) source
              [newStmt]
        | _ => [mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] rhs_trans) source]
        newctx := match rhs_trans.val with
        | .StaticCall fnname _ =>
            if let some (ImportedSymbol.compositeType laurelName) := ctx.importedSymbols[fnname.text]? then
              {newctx with variableTypes:= newctx.variableTypes ++ [(n.val, laurelName)]}
            else newctx
        | .New className =>
            {newctx with variableTypes:= newctx.variableTypes ++ [(n.val, className.text)]}
        | _=> newctx
        if n.val ∈ newctx.variableTypes.unzip.1 then
          return (newctx, assignStmts, true)
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
          return (newctx, initStmt :: assignStmts, true)
    | .Subscript _ _ _ _ =>
        match getSubscriptList lhs with
        | target :: slices =>
            let target ← translateExpr ctx target
            let slices ← slices.mapM (translateExpr ctx)
            let source := sourceRangeToSource ctx.filePath lhs.toAst.ann
            let anySetsExpr := mkStmtExprMdWithLoc (StmtExpr.StaticCall "Any_sets!" [ListAny_mk slices, target, rhs_trans]) source
            let assignStmts := [mkStmtExprMdWithLoc (StmtExpr.Assign [target] anySetsExpr) source]
            return (ctx,assignStmts, false)
        | _ =>  throw (.internalError "Invalid Subscript Expr")
    | .Attribute _ obj attr _ =>
      match obj with
      | .Name _ name _ =>
        if name.val == "self" && ctx.currentClassName.isSome then
          -- self.field : type = value in a method
          let fieldAccess := mkStmtExprMd (StmtExpr.FieldSelect
            (mkStmtExprMd (StmtExpr.Identifier "self"))
            attr.val)
          -- When the annotation is a composite type, the RHS (which is Any)
          -- cannot be assigned directly; use New to initialize the field.
          let rhs' ← match annotation with
            | some ann =>
              let annStr := pyExprToString ann
              if let some (.compositeType laurelName) := ctx.importedSymbols[annStr]? then
                pure (mkStmtExprMd (StmtExpr.New (mkId laurelName)))
              else pure rhs_trans
            | none => pure rhs_trans
          let assignStmt := mkStmtExprMdWithLoc (StmtExpr.Assign [fieldAccess] rhs') source
          return (ctx, [assignStmt], true)
        else
          let targetExpr ← translateExpr ctx lhs  -- This will handle self.field via translateExpr
          let assignStmt := mkStmtExprMdWithLoc (StmtExpr.Assign [targetExpr] rhs_trans) source
          return (ctx, [assignStmt], true)
      | _ => throw (.unsupportedConstruct "Assignment targets not yet supported" (toString (repr lhs)))
    | _ => throw (.unsupportedConstruct "Assignment targets not yet supported" (toString (repr lhs)))

/-- Extracts variable bindings from `with` statement items.
    Returns a list of (variable name, type) pairs, where type defaults to `Any`.
    Items without an `as` clause (e.g. `with open(...)`) are ignored. -/
partial def getWithItemsVars (withItems: List (Python.withitem SourceRange))
    :List (String × String) :=
  withItems.filterMap fun item => match item with
    | .mk_withitem _ _ var =>
      match var.val with
        | some var => some (pyExprToString var, PyLauType.Any)
        | _ => none

/-- Extracts loop variables from a `for` loop target expression.
    Handles single var or tuple/list unpacking targets. -/
partial def getForLoopVars (targetIter: Python.expr SourceRange) :List (String × String) :=
  match targetIter with
    | .Name _ n _ => [(n.val, PyLauType.Any)]  -- `for x in ...`
    | .Tuple _ tup _ | .List _ tup _ =>
        tup.val.toList.flatMap fun n => getForLoopVars n -- `for x, y in ...` or `for [x, y] in ...`
    | _ => []

def inferClassTypeFromLaurelExpr (ctx : TranslationContext) (value : Python.expr SourceRange) : Option String :=
  match translateExpr ctx value with
  | .ok {val := .New classname, ..} => classname.text
  | .ok {val := .StaticCall funcname _, ..} =>
      if isCompositeType ctx funcname.text then funcname.text else none
  | _ => none

partial def collectDeclaredNamesAndTypes (ctx : TranslationContext) (stmts : List (Python.stmt SourceRange)) : List (String × String) :=
  let rec go (s : Python.stmt SourceRange) : List (String × String) :=
    match s with
    | .Assign _ lhs value _ =>
      let ty := (inferClassTypeFromLaurelExpr ctx value).getD PyLauType.Any
      let names := (lhs.val.toList.filter (λ e => match e with |.Name _ _ _ => true | _=> false)).map pyExprToString
      names.map (λ n => (n, ty))
    | .AnnAssign _ lhs annoTy value _ =>
      let ty := match value.val with
        | some value => (inferClassTypeFromLaurelExpr ctx value).getD $ pyExprToString annoTy
        | _ => pyExprToString annoTy
      [(pyExprToString lhs, ty)]
    | .If _ _ body elsebody => body.val.toList.flatMap go ++ elsebody.val.toList.flatMap go
    | .For _ targetIter _ body _ _
    | .AsyncFor _ targetIter _ body _ _ => getForLoopVars targetIter ++ (body.val.toList.flatMap go)
    | .While _ _ body _ => body.val.toList.flatMap go
    | .Try _ body handlers orelse finalbody
    | .TryStar _ body handlers orelse finalbody =>
        let handlers_bodies := handlers.val.toList.map (λ h => match h with
          | .ExceptHandler _ _ _ body => body.val.toList)
        let error_var := (handlers.val.toList.filterMap (λ h => match h with
          | .ExceptHandler _ _ errname _ => errname.val)).map (λ h => (h.val, "PythonError"))
        error_var ++ (body.val.toList.flatMap go) ++ (handlers_bodies.flatten.flatMap go)
          ++ (finalbody.val.toList.flatMap go) ++ (orelse.val.toList.flatMap go)
    | .With _ items body _
    | .AsyncWith _ items body _=> (getWithItemsVars items.val.toList) ++ (body.val.toList.flatMap go)
    | .Match _ _ cases => cases.val.toList.flatMap (λ c => match c with
          | .mk_match_case _ _ _ body => body.val.toList.flatMap go)
    | _ => []
  stmts.flatMap go

def createVarDeclStmtsAndCtx (ctx : TranslationContext) (newDecls : List (String × String))
    : Except TranslationError (List StmtExprMd × TranslationContext) := do
  let newDecls := newDecls.foldl (fun acc (n, ty) =>
      if acc.any (fun (an, _) => an == n) || ctx.variableTypes.any (fun (vn, _) => vn == n)
      then acc else acc ++ [(n, ty)]) []
  let hoistedDecls : List StmtExprMd ←  newDecls.mapM fun (name, tyStr) => do
      let ty ← translateType ctx tyStr
      pure $ mkStmtExprMd (StmtExpr.LocalVariable (name : String) ty (some (mkStmtExprMd .Hole)))
  let hoistedCtx := { ctx with variableTypes := ctx.variableTypes ++
      (newDecls.map fun (n, ty) =>
        if isCompositeType ctx ty then (n, ty) else (n, PyLauType.Any)) }
  return (hoistedDecls, hoistedCtx)

--Check if a prelude function returns a value of Any type, which may be an exception (such as PAdd, PMul, ...)
def isMaybeExceptAnyFunc (ctx : TranslationContext) (funcName: String) : Bool := funcName ∈ ctx.maybeExceptionFunctions

partial def getMaybeExceptionExprs (ctx : TranslationContext) (e : StmtExprMd) : List StmtExprMd :=
  match e.val with
  | .StaticCall funcname args =>
    /-When the prelude function returns a value of Any type, which may be an exception, it should
    propagates the exceptions from its arguments (see the body of PAdd, PMul,..),
    so we don't need to recurse this function here.-/
    if isMaybeExceptAnyFunc ctx funcname.text then
      [e]
    else args.flatMap $ getMaybeExceptionExprs ctx
  | .PrimitiveOp _ args => args.flatMap $ getMaybeExceptionExprs ctx
  | .IfThenElse cond thenBranch elseBranch =>
      ([cond, thenBranch] ++ elseBranch.toList).flatMap $ getMaybeExceptionExprs ctx
  | _ => []

partial def getExceptionAssertions (ctx : TranslationContext) (e : StmtExprMd) : List StmtExprMd :=
  let maybeExceptExprs := getMaybeExceptionExprs ctx e
  maybeExceptExprs.map fun mbe =>
    let funcName := match mbe.val with | .StaticCall f _ => f.text | _ => "expression"
    let condExpr := mkStmtExprMd (.PrimitiveOp .Not [mkStmtExprMd $ .StaticCall "Any..isexception" [mbe]])
    let cond : Condition := { condition := condExpr, summary := some s!"Check {funcName} exception" }
    mkStmtExprMdWithLoc (.Assert cond) mbe.source

def withExceptionChecks (ctx : TranslationContext)
    (result : TranslationContext × List StmtExprMd)
    : TranslationContext × List StmtExprMd :=
  let (newctx, stmts) := result
  let rhs_exprs := stmts.flatMap fun s =>
    match s.val with | .Assign _ value => [value] | _ => []
  let exceptionCheck := rhs_exprs.flatMap $ getExceptionAssertions ctx
  (newctx, exceptionCheck ++ stmts)

mutual

partial def translateStmt (ctx : TranslationContext) (s : Python.stmt SourceRange)
    : Except TranslationError (TranslationContext × List StmtExprMd) := do
  let md := sourceRangeToSource ctx.filePath s.toAst.ann
  match s with
  -- Assignment: x = expr or self.field = expr
  | .Assign _ targets value _ => do
    if targets.val.size == 1 then
      let (ctx, stmts, _) ← translateAssign ctx targets.val[0]! none value md
      return withExceptionChecks ctx (ctx, stmts)
    -- Multiple targets: evaluate RHS once into a temporary, then assign temp to each target
    let sr := value.ann
    let freshVar := s!"multi_assign_{sr.start.byteIdx}"
    let tmpStore := expr.Name sr ⟨sr, freshVar⟩ (expr_context.Store sr)
    let tmpLoad := expr.Name sr ⟨sr, freshVar⟩ (expr_context.Load sr)
    let (tmpCtx, tmpStmts, _) ← translateAssign ctx tmpStore none value md
    let mut curCtx := tmpCtx
    let mut stmts : List StmtExprMd := tmpStmts
    for h : i in [:targets.val.size] do
      let (newCtx, newStmts, _) ← translateAssign curCtx targets.val[i] none tmpLoad md
      curCtx := newCtx
      stmts := stmts ++ newStmts
    return withExceptionChecks curCtx (curCtx, stmts)


  -- Annotated assignment: x: int = expr or x: ClassName = ClassName(args) or self.field: int = expr
  | .AnnAssign _ target annotation value _ => do
    match value.val with
    | some value =>
      let (ctx, stmts, typeAssertSafe) ← translateAssign ctx target annotation value md
      -- Emit type assertion for concrete type annotations (int, str, bool, float).
      -- This catches bugs like `x: int = None` where None is not a valid int.
      -- Only safe when translateAssign signals that the target variable holds
      -- the assigned value (simple assignment path).
      let typeAssert := match target with
        | .Name _ n _ =>
          if !typeAssertSafe then []
          else if s.toAst.ann == default then [] -- compiler-generated statement, no source location
          else
          let annStr := pyExprToString annotation
          match typeTester? annStr with
          | some testerName =>
            let varExpr := mkStmtExprMd (StmtExpr.Identifier n.val)
            let cond := mkStmtExprMd (StmtExpr.StaticCall testerName [varExpr])
            [mkStmtExprMdWithLoc (StmtExpr.Assert { condition := cond }) md]
          | none => []
        | _ => []
      return withExceptionChecks ctx (ctx, stmts ++ typeAssert)
    | none =>
      -- Declaration without initializer (not allowed in pure context, but OK in procedures)
      let varType := pyExprToString annotation
      let varName := pyExprToString target
      if varName ∈ ctx.variableTypes.unzip.1 then
          return (ctx, [])
      let newctx := {ctx with variableTypes:=(varName, varType)::ctx.variableTypes}
      let varType ← translateType ctx varType
      let declStmt := mkStmtExprMd (StmtExpr.LocalVariable varName varType AnyNone)
      return (newctx, [declStmt])

  -- If statement
  | .If _ test body orelse => do
    let condExpr ← translateExpr ctx test
    let (bodyCtx, bodyStmts) ← translateStmtList ctx body.val.toList
    let bodyBlock := mkStmtExprMd (StmtExpr.Block bodyStmts none)
    -- Translate else branch if present
    let elseBlock ← if orelse.val.isEmpty then
      .ok none
    else do
      let (_, elseStmts) ← translateStmtList bodyCtx orelse.val.toList
      .ok (some (mkStmtExprMd (StmtExpr.Block elseStmts none)))
    let ifStmt := mkStmtExprMdWithLoc (StmtExpr.IfThenElse (Any_to_bool condExpr) bodyBlock elseBlock) md

    return (bodyCtx, (getExceptionAssertions ctx condExpr) ++ [ifStmt])

  -- While loop
  | .While _ test body _orelse => do
    -- Note: Python while-else not supported yet
    let condExpr ← translateExpr ctx test
    let breakLabel := s!"loop_break_{test.toAst.ann.start.byteIdx}"
    let continueLabel := s!"loop_continue_{test.toAst.ann.start.byteIdx}"
    let loopCtx := { ctx with loopBreakLabel := some breakLabel, loopContinueLabel := some continueLabel }
    let (_, bodyStmts) ← translateStmtList loopCtx body.val.toList
    let bodyBlock := mkStmtExprMdWithLoc (StmtExpr.Block bodyStmts (some continueLabel)) md
    let whileStmt := mkStmtExprMdWithLoc (StmtExpr.While (Any_to_bool condExpr) [] none bodyBlock) md
    let whileWrapped := mkStmtExprMdWithLoc (StmtExpr.Block [whileStmt] (some breakLabel)) md
    return (loopCtx, (getExceptionAssertions ctx condExpr) ++ [whileWrapped])

  -- Return statement: assign to the LaurelResult output parameter, then exit $body.
  | .Return _ value => do
    let stmts ← match value.val with
      | some expr => do
        let e ← translateExpr ctx expr
        let exceptionCheck := getExceptionAssertions ctx e
        -- Coerce Composite return values to Any for LaurelResult : Any
        let e ← coerceToAny ctx expr e
        let assign := mkStmtExprMdWithLoc (StmtExpr.Assign [mkStmtExprMd (StmtExpr.Identifier PyLauFuncReturnVar)] e) md
        .ok $ exceptionCheck ++ [assign, mkStmtExprMdWithLoc (StmtExpr.Exit "$body") md]
      | none => .ok [mkStmtExprMdWithLoc (StmtExpr.Exit "$body") md]
    return (ctx, stmts)

  -- Assert statement
  | .Assert _ test msg => do
    let condExpr ← translateExpr ctx test
    -- Extract assert message as property summary
    let summary := match msg.val with
      | some (.Constant _ (.ConString _ str) _) => some str.val
      | _ => none
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

    let assertStmt := mkStmtExprMdWithLoc (StmtExpr.Assert { condition := Any_to_bool finalCondExpr, summary }) md

    -- Wrap in block if we hoisted condition
    let result := if condStmts.isEmpty then
      assertStmt
    else
      mkStmtExprMdWithLoc (StmtExpr.Block (condStmts ++ [assertStmt]) none) md

    return (condCtx, (getExceptionAssertions ctx condExpr) ++ [result])

  --Ignore comments in source code
  | .Expr _ (.Constant _ (.ConString _ _) _) => return (ctx, [])

  -- Expression statement (e.g., function call)
  | .Expr _ value => do
    let expr ← translateExpr ctx value
    let expr := { expr with source := md }
    let exceptionCheck := getExceptionAssertions ctx expr

    -- When a call has no model (translates to Hole), also havoc maybe_except
    -- since an unmodeled call is a black box that could throw any exception.
    let holeExceptHavoc :=
      if let .Call _ _ _ _ := value then
        [mkStmtExprMdWithLoc (StmtExpr.Assign [maybeExceptVar] (mkStmtExprMd (.Hole false none))) md]
      else []
    match expr.val with
    | .StaticCall fnname _ =>
        match ctx.functionSignatures.find? (λ funsig => funsig.name == fnname) with
        | some funsig =>
            let targets := if funsig.ret.isNone then [] else [nullcall_var]
            let targets := if withException ctx fnname.text then targets++[maybeExceptVar] else targets
            if targets.length > 0 then
              return (ctx, exceptionCheck ++ [mkStmtExprMdWithLoc (StmtExpr.Assign targets expr) md])
            else
              return (ctx, exceptionCheck ++ [expr])
        | _ => return (ctx, exceptionCheck ++ [expr])
    -- Unmodeled call: skip exception checks (no model to check against),
    -- but havoc maybe_except since the call could throw.
    -- Unmodeled call: havoc is now handled in translateCall via Block.
    | .Hole => return (ctx, [expr] ++ holeExceptHavoc)
    | .Block _ _ => return (ctx, [expr] ++ holeExceptHavoc)
    | _ => return (ctx, exceptionCheck ++ [expr])

  | .Import _ _ | .ImportFrom _ _ _ _ |.Pass _ => return (ctx, [])

  -- Try/except - wrap body with exception checks and handlers
  | .Try _ body handlers _ _ => do
    let tryLabel := s!"try_end_{s.toAst.ann.start.byteIdx}"
    let catchersLabel := s!"exception_handlers_{s.toAst.ann.start.byteIdx}"
    let (bodyCtx, bodyStmts) ← translateStmtList ctx body.val.toList

    -- Translate exception handlers
    let mut handlerCtx := bodyCtx
    let mut handlerStmts : List StmtExprMd := []
    for handler in handlers.val do
      match handler with
      | .ExceptHandler _ _ _ handlerBody =>
        let (hCtx, hStmts) ← translateStmtList ctx handlerBody.val.toList
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
    return (finalCtx, [tryBlock])

  -- FIXME: Placeholder — `raise` is dropped so the Hole type inferrer doesn't
  -- produce Unknown types. Must be replaced to correctly model exceptions later.
  | .Raise _ _ _ => return (ctx, [])

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
        let enterCall := mkInstanceMethodCall mgrTy "__enter__" mgrRef [] md
        let exitCall := mkInstanceMethodCall mgrTy "__exit__" mgrRef [] md
        match optVars.val with
        | some varExpr =>
          let varName := pyExprToString varExpr
          if varName ∈ currentCtx.variableTypes.unzip.fst then
            let assignStmt := mkStmtExprMd (StmtExpr.Assign
              [mkStmtExprMd (StmtExpr.Identifier varName)] enterCall)
            setupStmts := setupStmts ++ [mgrDecl, assignStmt]
          else
            -- New variable — declare outside the block so it's visible after
            let varDecl := mkStmtExprMd (StmtExpr.LocalVariable varName AnyTy (some enterCall))
            currentCtx := {currentCtx with variableTypes := currentCtx.variableTypes ++ [(varName, PyLauType.Any)]}
            setupStmts := setupStmts ++ [mgrDecl, varDecl]
        | none =>
          setupStmts := setupStmts ++ [mgrDecl, enterCall]
        cleanupStmts := cleanupStmts ++ [exitCall]
    let (bodyCtx, bodyStmts) ← translateStmtList currentCtx body.val.toList
    let block := mkStmtExprMdWithLoc (StmtExpr.Block (setupStmts ++ bodyStmts ++ cleanupStmts) none) md
    return (bodyCtx, [block])

  -- For loop is translated into a while loop:
  -- for x in iter : \n body
  -- is translated into
  -- @for_loop_counter_xxx = 0
  -- while (@for_loop_counter_xxx < Any_len(iter)):
  --  body
  --  @for_loop_counter_xxx += 1
  -- Invariant: for `for x in iter: body`, the emitted while loop visits
  -- each index 0 ≤ i < len(iter) exactly once with x = iter[i], and all
  -- variables modified in body are properly havocked by while semantics.
  -- Incompleteness: The functions Any_len, Any_iter_index are now opaque.
  -- Note that Any_iter_index(iter, index) should not return an exception when 0 <= index < Any_len(iter)
  -- and Any_iter_index is only called inside the loop body where that condition is satisfied,
  -- so it is sound to not put it inside AnyMaybeExceptionList
  | .For _ target iter body _orelse _ => do
    -- The iterator expression (we abstract it away)
    let iterExpr ← translateExpr ctx iter
    if let .Call _ (.Name _ {val:= "range",..} _) _ _  := iter then
      if let .StaticCall "range" _ := iterExpr.val then
        pure ()
      else
        throw (.internalError "Translation of Python range function changed")
    -- Create context with target(s) and loop labels
    let breakLabel := s!"for_break_{iter.toAst.ann.start.byteIdx}"
    let continueLabel := s!"for_continue_{iter.toAst.ann.start.byteIdx}"
    -- Havoc the target(s) (Ellipsis always translates to Hole)
    let sr := target.ann
    let counterName := s!"@for_loop_counter_{s.toAst.ann.start.byteIdx}"
    let counterVar := freeVar counterName
    let counterDecl := mkStmtExprMd $ .LocalVariable counterName (mkHighTypeMd $ .TInt) (mkStmtExprMd $ .LiteralInt 0)
    let counterIncrease := mkStmtExprMd $ .Assign [counterVar] (mkStmtExprMd $ .PrimitiveOp .Add [counterVar, mkStmtExprMd $ .LiteralInt 1])
    let indexRhs := expr.Call sr (.Name sr {val:= "Any_iter_index", ann:= sr} default)
                        {val:= #[iter, .Name sr {val:= counterName, ann:= sr} default], ann:= sr} {val:= #[], ann:= sr}
    -- Any_iter_index is defined in PythonRuntimeLaurelPart, so indexRhs would be translated into .StaticCall "Any_iter_index" ..., hot .Hole
    let (bodyCtxNoLabels, targetDecls, _) ← translateAssign ctx target none indexRhs md
    let bodyCtx := { bodyCtxNoLabels with
      loopBreakLabel := some breakLabel
      loopContinueLabel := some continueLabel
      variableTypes := bodyCtxNoLabels.variableTypes ++ [(counterName, "int")]}
    let (finalCtx, bodyStmts) ← translateStmtList bodyCtx body.val.toList
    let assumeStmts : List StmtExprMd ← do match target with
      | .Name _ n _ =>
        let targetVar := mkStmtExprMd (StmtExpr.Identifier n.val)
        let isAnyNone (s: StmtExprMd) := match s.val with
          | .StaticCall constructor _ => constructor == AnyConstructor.None | _ => false
        match iterExpr.val with
          | .StaticCall "range" (startExpr::stopExpr::stepExpr::_) =>
            if ¬ (isAnyNone stopExpr && isAnyNone stepExpr) then
              throw (.unsupportedConstruct "Unsupport range function with more than 1 input" (toString (repr iter)))
            let asIntStart := mkStmtExprMd $ .StaticCall "Any..as_int!" [startExpr]
            let assumeTypeInt := mkStmtExprMdWithLoc (.Assume $ mkStmtExprMd (.StaticCall "Any..isfrom_int" [targetVar])) md
            let asIntTarget := mkStmtExprMd $ .StaticCall "Any..as_int!" [targetVar]
            let inRangeExpr := mkStmtExprMd $ .PrimitiveOp .And [
                  (mkStmtExprMd $ .PrimitiveOp .Geq [asIntTarget, mkStmtExprMd $ .LiteralInt 0]),
                  (mkStmtExprMd $ .PrimitiveOp .Lt [asIntTarget, asIntStart]) ]
            let assumeInRange := mkStmtExprMdWithLoc (.Assume inRangeExpr) md
            pure [assumeTypeInt, assumeInRange]
          | _ =>
            let targetInIter := mkStmtExprMd (.StaticCall "PIn" [targetVar, iterExpr])
            let assumeInStmt := mkStmtExprMdWithLoc (.Assume (Any_to_bool targetInIter)) md
            pure [assumeInStmt]
      | _ => pure []
    let counterLtLen := match iterExpr.val with
      | .StaticCall "range" (boundExpr::_) =>
          mkStmtExprMd $ .PrimitiveOp .Lt [counterVar,
                          mkStmtExprMd $ .StaticCall "Any..as_int!" [boundExpr]]
      | _ =>
          mkStmtExprMd $ .PrimitiveOp .Lt [counterVar,
                          mkStmtExprMd $ .StaticCall "Any_len" [iterExpr]]
    let bodyStmts := targetDecls ++ assumeStmts ++ bodyStmts ++ [counterIncrease]
    let innerBlock := mkStmtExprMd (StmtExpr.Block bodyStmts (some continueLabel))
    let loopStmt := mkStmtExprMdWithLoc (StmtExpr.While counterLtLen [] none innerBlock) md
    let loopBlock := mkStmtExprMdWithLoc (StmtExpr.Block [loopStmt] (some breakLabel)) md
    return (finalCtx, (getExceptionAssertions ctx iterExpr) ++ [counterDecl] ++ [loopBlock])

  | .Break _ =>
    match ctx.loopBreakLabel with
    | some lbl => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Exit lbl) md])
    | none => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Assert { condition := mkStmtExprMd .Hole }) md])
  | .Continue _ =>
    match ctx.loopContinueLabel with
    | some lbl => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Exit lbl) md])
    | none => return (ctx, [mkStmtExprMdWithLoc (StmtExpr.Assert { condition := mkStmtExprMd .Hole }) md])

  -- Augmented assignment: x += expr  →  x = x op expr
  | .AugAssign sr target op value => do
    -- For subscript targets like l[i][j], we extract the index expressions,
    -- bind them to temp variables (to avoid double-evaluation), and
    -- reconstruct the target using the temp var names.
    let (target, tempVars, slices) := match target with
      | .Subscript _ _ _ _ =>
        match getSubscriptList target with
        | base :: slices =>
            let tempVars := (List.range slices.length).map λ n => s!"$augAssignTempVar_{sr.start}_{n}"
            let tempVarExprs: List (Python.expr SourceRange) := tempVars.map
                (fun var => .Name sr {val:= var, ann:= sr} (.Load sr))
            let target: Python.expr SourceRange := tempVarExprs.foldl (λ s t =>
              .Subscript sr s t (.Load sr)) base
            (target, tempVars, slices)
        | _ =>  (target, [], [])
      | _ => (target, [], [])
    let slices ← slices.mapM (translateExpr ctx)
    let tempVarDecls := (tempVars.zip slices).map λ (var, slice) =>
              mkStmtExprMd (.LocalVariable { text := var } AnyTy slice)
    let rhs : Python.expr SourceRange := .BinOp sr target op value
    let pyNormalAssign : Python.stmt SourceRange :=
          .Assign sr {val:= #[target], ann:= target.ann} rhs {val:= none, ann:= sr}
    let (ctx, assignStmt) ← translateStmt ctx pyNormalAssign
    return (ctx, tempVarDecls ++ assignStmt)

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

def getUnionTypes (arg: Python.expr SourceRange) : List (Python.expr SourceRange) :=
  match arg with
  | .BinOp _ left _ right => getUnionTypes left ++ getUnionTypes right
  | _ => [arg]

-- Could
def checkValidInputTypeList (ctx : TranslationContext) (tys: List String) : Except TranslationError (List String) := do
  for ty in tys do
    let _ ← translateType ctx ty
  if tys.length > 1 && tys.any (λ ty => ¬ isOfAnyType ty) then
    throw (.unsupportedConstruct "Argument of union of class types is not supported" (toString tys))
  return tys

private def normalizeTypingName (e : Python.expr SourceRange) : String :=
  match e with
  | .Attribute _ _ {val := s, ..} _ =>
    if s ∈ ["Dict", "List", "Callable", "Optional", "Union"] then s
    else pyExprToString e
  | _ => pyExprToString e

partial def getArgumentTypes (arg: Python.expr SourceRange) : Except TranslationError (List String) :=
  match arg with
  | .Name _ n _ => return [n.val]
  | .Subscript _ _ slice _ =>
    let subscriptList:= getNestedSubscripts arg
    let subscriptRoot := normalizeTypingName subscriptList[0]!
    let sliceHead := subscriptList[1]!
    match subscriptRoot with
    | "Optional" => return (← getArgumentTypes slice) ++ ["None"]
    | "Union" =>  match sliceHead with
        | .Tuple _ tys _ => return (← tys.val.toList.mapM getArgumentTypes).flatten
        | _ => throw (.internalError s!"Unhandled Expr: {repr arg}")
    | "List" | "list" => return ["ListAny"]
    | "Dict" | "dict" => return ["DictStrAny"]
    | "Callable" => return ["Any"]
    | _ =>  throw (.internalError s!"Unhandled Expr: {repr arg}")
  | .Constant _ _ _ => return ["None"]
  | .Attribute _ _ _ _ => return [pyExprToString arg]
  | .BinOp _ _ _ _ => return (← (getUnionTypes arg).mapM getArgumentTypes).flatten
  --Temporary: just to handle "typing:some_type ... "
  | .Slice _ lower upper _ => match lower.val, upper.val with
      | some (.Name  _ _ _ ), some upper => getArgumentTypes upper
      | _, _ => throw (.internalError s!"Unhandled Expr: {repr arg}")
  | _ => throw (.internalError s!"Unhandled Expr: {repr arg}")

--The return is a List (inputname, type, default value) and a bool indicating if the function has Kwargs input
def unpackPyArguments (ctx : TranslationContext) (args: Python.arguments SourceRange)
    : Except TranslationError ((List PyArgInfo) × (Option String)):= do
  match args with
    | .mk_arguments _ _ args _ _ _ kwargs defaults =>
      let argscount := args.val.size
      let defaultscount := defaults.val.size;
      let listdefaults := (List.range (argscount - defaultscount)).map (λ _ => none)
                        ++ defaults.val.toList.map (λ x => some x)
      let argsinfo := args.val.toList.zip listdefaults
      let mut argtypes : Array PyArgInfo := #[]
      for (arg, default) in argsinfo do
        match arg with
          | .mk_arg sr name oty _ =>
            let md := sourceRangeToSource ctx.filePath sr
            let defaultType := match default.mapM (inferExprType ctx) with
                  | .ok (some ty) => some ty
                  | _ => none
            let mut tys : List String := []
            tys ← match oty.val with
              | .some ty => getArgumentTypes ty
              | _ => pure [PyLauType.Any]
            match defaultType with
            | .some "None" => --Only None is allowed to add to type list
              if tys != [PyLauType.Any] then
                tys:= (PyLauType.None::tys).dedup
            | .some defaultType =>
              if isOfAnyType defaultType && tys != [PyLauType.Any] && defaultType ∉ tys then
                throw (.unsupportedConstruct "Default value type is invalid" (toString (repr arg)))
            | _ =>
              pure ()
            tys ← checkValidInputTypeList ctx tys
            argtypes := argtypes.push {
              name:= name.val,
              source := md,
              laurelType := pyArgLaurelType ctx tys,
              typeTesters := pyLauTypeTesters tys,
              default:= default
            }
      let kwargsName := kwargs.val.map (λ kwarg => match kwarg with | .mk_arg _ name _ _ => name.val)
      return (argtypes.toList, kwargsName)

def pyFuncDefToPythonFunctionDecl  (ctx : TranslationContext) (f : Python.stmt SourceRange) : Except TranslationError PythonFunctionDecl := do
  match f with
  | .FunctionDef _ name args _body _decorator_list returns _type_comment _ =>
    let name := match ctx.currentClassName with | none => name.val | some classname => manglePythonMethod classname name.val
    let args_trans ← unpackPyArguments ctx args
    let args := if ctx.currentClassName.isSome then args_trans.fst.tail else args_trans.fst
    let ret ←  if name.endsWith "@__init__" then
          let retSource := sourceRangeToSource ctx.filePath f.ann
          let className := (name.dropEnd "@__init__".length).toString
          pure $ some {
            source := retSource,
            laurelType := mkHighTypeMd (.UserDefined { text := className }),
            typeTesters := #[]
          }
        else
        match returns.val with
          | some retTy =>
              let retSource := sourceRangeToSource ctx.filePath retTy.ann
              match checkValidInputTypeList ctx (← getArgumentTypes retTy) with
              | .ok tys =>
                pure $ some {
                  source := retSource,
                  laurelType := pyArgLaurelType ctx tys,
                  typeTesters := pyLauTypeTesters tys
                }
              | _ => pure none
          | none => pure none
    let kwargsName := args_trans.snd
    return {
      name
      args
      kwargsName
      ret
    }
  | _ => throw (.internalError "Expected FunctionDef")

/-- Prefix applied to Core input parameters so the original name can be used
    for a mutable local copy inside the procedure body. -/
def paramInputPrefix : String := "$in_"

def getTypeConstraint (var : String) (source : Option FileRange) (testers : Array String)
    (funcname : String) (displayName : String := var) : Option Condition :=
  let constraints := testers.toList.map fun callee =>
    mkStmtExprMd (.StaticCall (mkId callee) [freeVar var])
  if constraints.isEmpty then none else
    some { condition := { createBoolOrExpr constraints with source := source },
           summary := some $ "(" ++ funcname ++ " requires) Type constraint of " ++ displayName }

def getReturnTypeEnsure (source : Option FileRange) (testers : Array String) (funcname : String) : Option Condition :=
  getTypeConstraint PyLauFuncReturnVar source testers funcname
  |>.map fun c => { c with summary := some $ "(" ++ funcname ++ " ensures) Return type constraint" }


/-- Rename input parameters with `paramInputPrefix` and produce local-copy
    statements so the function body can freely modify the original names.
    Parameters for which `exclude` returns true are left unchanged (e.g. `self`). -/
def renameInputParams (inputs : List Parameter) (exclude : String → Bool := fun _ => false)
    : List Parameter × List StmtExprMd :=
  let renamed := inputs.map fun p =>
    if exclude p.name.text then p
    else { p with name := mkId (paramInputPrefix ++ p.name.text) }
  let copies := inputs.filter (fun p => !exclude p.name.text) |>.map fun p =>
    let orig : String := p.name.text
    let prefixed : String := paramInputPrefix ++ orig
    mkStmtExprMd (StmtExpr.LocalVariable (mkId orig) p.type
      (some (mkStmtExprMd (StmtExpr.Identifier prefixed))))
  (renamed, copies)

/-- Translate a Python function body: collect all variable declarations, hoist them
    to the top, and translate the remaining statements. --/
def translateFunctionBody (ctx : TranslationContext) (kwargsName : Option String) (inputs: List Parameter) (body: List (Python.stmt SourceRange))
  : Except TranslationError (StmtExprMd × TranslationContext) := do
    let newDecls := collectDeclaredNamesAndTypes ctx body
    let (varDecls, ctx) ←  createVarDeclStmtsAndCtx ctx newDecls
    let (newctx, bodyStmts) ← translateStmtList ctx body
    let bodyStmts := prependExceptHandlingHelper (varDecls ++ bodyStmts)
    let nonSelfParams := inputs.filter (fun p => p.name.text != "self")
    let (_, paramCopies) := renameInputParams nonSelfParams
      (match kwargsName with | some kw => (· == kw) | none => fun _ => false)
    let noneReturn := mkStmtExprMd (.Assign [mkStmtExprMd (.Identifier PyLauFuncReturnVar)] AnyNone)
    let bodyStmts := noneReturn::paramCopies ++ bodyStmts
    let bodyStmts := (mkStmtExprMd (.LocalVariable "nullcall_ret" AnyTy (some AnyNone))) :: bodyStmts
    return (mkStmtExprMd (StmtExpr.Block bodyStmts none), newctx)

/-- Translate Python function to Laurel Procedure -/
def translateFunction (ctx : TranslationContext) (sourceRange: SourceRange) (funcDecl : PythonFunctionDecl)
    (body: Option (List (Python.stmt SourceRange)))
    : Except TranslationError (Laurel.Procedure × TranslationContext) := do

    -- Translate parameters
    let mut inputs : List Parameter := []

    inputs := funcDecl.args.map fun arg =>
      { name := arg.name, type := arg.laurelType }

    inputs := match ctx.currentClassName with
    | some className =>
      -- First parameter is self (typed as Composite to match call-site convention)
      let selfParam : Parameter := {
        name := "self"
        type := mkHighTypeMd (.UserDefined (mkId className))
      }
      [selfParam] ++ inputs
    | _ => inputs

    match funcDecl.kwargsName with
    | some kwargs => inputs:= inputs ++ [{ name := kwargs, type := mkCoreType PyLauType.DictStrAny}]
    | _ => pure ()

    let typeConstraintPreconditions := funcDecl.args.filterMap
      (fun arg => getTypeConstraint (paramInputPrefix ++ arg.name) arg.source arg.typeTesters funcDecl.name arg.name)
    let typeConstraintPostcondition :=
      if funcDecl.name.endsWith "@__init__" then [] else
      match funcDecl.ret with
        | some retInfo =>
          match getReturnTypeEnsure retInfo.source retInfo.typeTesters funcDecl.name with
          | some constraint => [constraint]
          | none => []
        | _ => []

    -- Translate return type
    -- All methods return Any (void methods return Any via from_None)
    let outputs : List Parameter := [{ name := PyLauFuncReturnVar, type := AnyTy }]

    -- Translate function body
    let inputTypes := funcDecl.args.map fun arg =>
      (arg.name, highTypeToPyLauType arg.laurelType.val)
    let ctx := {ctx with variableTypes:= ("nullcall_ret", PyLauType.Any)::inputTypes}
    let (bodyTrans, newCtx) ← match body with
    | some body =>
        let (bodyBlock, newCtx) ←  translateFunctionBody ctx funcDecl.kwargsName inputs body
        if typeConstraintPostcondition.isEmpty then
            pure $ (Body.Transparent bodyBlock, newCtx)
        else
            pure $ (Body.Opaque typeConstraintPostcondition bodyBlock [], newCtx)
    | _ =>  pure $ (Body.Opaque [] none [], ctx)

    let renamedInputs := inputs.map fun p =>
      if p.name.text == "self" then p
      else { p with name := mkId ("$in_" ++ p.name.text) }

    -- Create procedure with transparent body (no contracts for now)
    let proc : Procedure := {
      name := { text := funcDecl.name, source := sourceRangeToSource ctx.filePath sourceRange }
      inputs := renamedInputs
      outputs := outputs
      preconditions := typeConstraintPreconditions
      decreases := none
      body := bodyTrans
      isFunctional := false
    }

    return (proc, {newCtx with variableTypes := []})

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
      let noneexpr : Python.expr SourceRange := .Constant default (.ConNone default) default
      let retParam := proc.header.outputs.head?
      let ret := retParam.map fun (_, tp) =>
        let tys := [getTypeName tp]
        { source := none,
          laurelType := mkHighTypeMd (.UserDefined (mkId (getTypeName tp))),
          typeTesters := pyLauTypeTesters tys : PyRetInfo }
      some {
        name:= proc.header.name.name
        args:=  proc.header.inputs |>.map λ(nm,tp) =>
        {
          name:= nm.name,
          source := none,
          laurelType := AnyTy,
          typeTesters := pyLauTypeTesters [getTypeName tp],
          default:= noneexpr
        }
        kwargsName := none
        ret
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

      let fieldType ← translateFieldType ctx (pyExprToString annotation)

      fields := fields ++ [{
        name := fieldName
        type := fieldType
        isMutable := true  -- Python fields are mutable by default
      }]
    | _ => pure ()  -- Ignore non-field statements

  return fields

/-- Extract fields from __init__ method body by scanning for self.field : type = expr patterns -/
def extractFieldsFromInit (ctx : TranslationContext) (initBody : Array (Python.stmt SourceRange))
    : Except TranslationError (List Field) := do
  let mut fields : List Field := []
  for stmt in initBody do
    match stmt with
    | .AnnAssign _ (.Attribute _ (.Name _ selfName _) attr _) annotation _ _ =>
      if selfName.val == "self" then
        let fieldType ← translateFieldType ctx (pyExprToString annotation)
        fields := fields ++ [{
          name := attr.val
          type := fieldType
          isMutable := true
        }]
    | _ => pure ()
  return fields

/-- Match a `self.field = dispatch_call(...)` pattern and return (fieldName, compositeType). -/
private def matchDispatchField (ctx : TranslationContext) (target value : Python.expr SourceRange)
    : Except TranslationError (Option (String × String)) := do
  if let .Attribute _ (.Name _ selfName _) attr _ := target then
    if selfName.val == "self" then
      if let .Call _ f callArgs _ := value then
        if let some cn ← resolveDispatch ctx f callArgs.val then
          return some (attr.val, cn)
  return none

/-- Recursively scan statements for `self.field = dispatch_call(...)` patterns.
    Descends into if/try/for/while/with blocks to find dispatch calls in
    nested control flow (e.g., `try: self.client = boto3.client('s3')`). -/
private partial def scanDispatchFields (ctx : TranslationContext)
    (stmts : List (Python.stmt SourceRange))
    : Except TranslationError (List (String × String)) := do
  let mut result : List (String × String) := []
  for s in stmts do
    let fields ← match s with
      | .Assign _ targets value _ =>
        if let some target := targets.val[0]? then
          (matchDispatchField ctx target value).map (·.toList)
        else pure []
      | .AnnAssign _ target _ value _ =>
        if let some value := value.val then
          (matchDispatchField ctx target value).map (·.toList)
        else pure []
      | .If _ _ body orelse =>
        let a ← scanDispatchFields ctx body.val.toList
        let b ← scanDispatchFields ctx orelse.val.toList
        pure (a ++ b)
      | .Try _ body handlers orelse finalbody =>
        let a ← scanDispatchFields ctx body.val.toList
        let b ← handlers.val.toList.flatMapM fun h =>
          match h with | .ExceptHandler _ _ _ hbody => scanDispatchFields ctx hbody.val.toList
        let c ← scanDispatchFields ctx orelse.val.toList
        let d ← scanDispatchFields ctx finalbody.val.toList
        pure (a ++ b ++ c ++ d)
      | .For _ _ _ body orelse _ =>
        let a ← scanDispatchFields ctx body.val.toList
        let b ← scanDispatchFields ctx orelse.val.toList
        pure (a ++ b)
      | .While _ _ body orelse =>
        let a ← scanDispatchFields ctx body.val.toList
        let b ← scanDispatchFields ctx orelse.val.toList
        pure (a ++ b)
      | .With _ _ body _ =>
        scanDispatchFields ctx body.val.toList
      | _ => pure []
    result := result ++ fields
  return result

/-- Synthesize a default `__init__` declaration and procedure for a class that lacks one.
    Returns a `PythonFunctionDecl` (for call-site arity checking) and a `Procedure` (for verification).
    The procedure is derived from the decl so that both stay in sync when the calling convention changes.
    TODO: The synthesized procedure has an `.Opaque` body, so the verifier cannot reason about
    default field values. Wire default field values through as postconditions to enable full verification. -/
def mkDefaultInitDecl (className : String) : PythonFunctionDecl × Procedure :=
  let initDeclName := className ++ "@__init__"
  -- Build the decl as the single source of truth
  let decl : PythonFunctionDecl := {
    name := initDeclName
    -- `args` excludes `self`, matching the convention in `pyFuncDefToPythonFunctionDecl`
    -- where `self` is stripped via `.tail` for methods inside a class.
    args := []
    kwargsName := none
    ret := some { source := none,
                  laurelType := mkHighTypeMd (.UserDefined { text := className }),
                  typeTesters := #[] }
  }
  -- Derive the procedure from the decl, mirroring translateMethod's convention
  let selfParam : Parameter := {
    name := "self"
    type := mkHighTypeMd (.UserDefined (mkId className))
  }
  let inputs := [selfParam]
  let proc : Procedure := {
    name := { text := decl.name }
    inputs := inputs
    outputs := [{name := "LaurelResult", type := AnyTy}]
    preconditions := [{ condition := mkStmtExprMd (StmtExpr.LiteralBool true) }]
    isFunctional := false
    decreases := none
    body := .Opaque [] .none []
  }
  (decl, proc)

/-- Translate a Python class to a Laurel CompositeType. returns:
   - `CompositeType`: the type definition (fields, name); its `instanceProcedures` is set to `[]`
     because the Laurel→Core translator does not yet support instance procedures.
   - `Array Procedure`: the translated method procedures, added as top-level static procedures
     with mangled names (`ClassName@method`) so they can be called via `StaticCall`.
   - `List PythonFunctionDecl`: function signatures for the class methods. -/
def translateClass (ctx : TranslationContext) (classStmt : Python.stmt SourceRange)
    : Except TranslationError (CompositeType × Array Procedure × List PythonFunctionDecl) := do
  match classStmt with
  | .ClassDef _ className _bases _ ⟨_, body⟩ _ _ =>
    let className := className.val
    let ctx := {ctx with currentClassName:= className}
    let classFunDeclsAndBody  ← body.toList.filterMapM (λ s => do match s with
      | .FunctionDef sr _ _ funcBody _ _ _ _ =>
          let funcDecl ← pyFuncDefToPythonFunctionDecl ctx s
          .ok (some (funcDecl, sr, funcBody.val.toList))
      | _ => .ok none)
    let classFunDecls := classFunDeclsAndBody.unzip.fst
    -- Synthesize a default __init__ if the class doesn't define one
    let hasInit := classFunDecls.any (fun d => d.name == className ++ "@__init__")
    let (classFunDecls, defaultInitProc) :=
      if hasInit then (classFunDecls, none)
      else
        let (decl, proc) := mkDefaultInitDecl className
        (decl :: classFunDecls, some proc)

    let ctx := {ctx with functionSignatures:= ctx.functionSignatures ++ classFunDecls}
    -- Extract fields from class-level annotations and __init__ body, with dedup
    let classLevelFields ← extractClassFields ctx body
    let mut fields := classLevelFields
    for stmt in body do
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
    -- Detect dispatch calls in __init__ (e.g. self.client = boto3.client('s3'))
    -- and record the resolved composite type for method dispatch only.
    -- Handles both plain assignments and annotated assignments.
    -- Scans recursively into nested blocks (if/try/for/while/with).
    let mut dispatchFields : Std.HashMap String String := {}
    let mut conflictingFields : Std.HashSet String := {}
    for stmt in body do
      if let .FunctionDef _ name _ initBody _ _ _ _ := stmt then
        if name.val == "__init__" then
          let dispatchResult ← scanDispatchFields ctx initBody.val.toList
          for (fieldName, cn) in dispatchResult do
            match dispatchFields[fieldName]? with
            | some existing =>
              if existing != cn then
                conflictingFields := conflictingFields.insert fieldName
                continue
            | none => pure ()
            dispatchFields := dispatchFields.insert fieldName cn
    -- Remove fields with conflicting types (e.g., different types in if/else branches)
    for f in conflictingFields do
      dispatchFields := dispatchFields.erase f
    let ctx := {ctx with
      classFieldHighType := ctx.classFieldHighType.insert className classFields
      dispatchFieldTypes := ctx.dispatchFieldTypes.insert className dispatchFields}

    -- Translate each method
    -- Keep the translated body only for classes not involved in inheritance;
    -- for hierarchy classes, strip to opaque since call sites emit holes anyway
    -- and the resolution pass may not handle all constructs in method bodies.
    let inHierarchy := ctx.classesInHierarchy.contains className
    let mut instanceProcedures : Array Procedure := #[]

    for (funcDecl, sr,  funcBody) in classFunDeclsAndBody do
      let (proc, _) ← translateFunction ctx sr funcDecl $ if inHierarchy then none else funcBody
      instanceProcedures := instanceProcedures.push proc
    -- Add synthesized default __init__ if needed
    if let some initProc := defaultInitProc then
      instanceProcedures := instanceProcedures.push initProc


    return ({
      name := className
      extending := []  -- No inheritance support for now
      fields := fields
      instanceProcedures := [] -- Laurel→Core does not yet translate CompositeType.instanceProcedures
                               -- (see LaurelToCoreTranslator.translateTypes, which emits NotYetImplemented);
                               -- methods are instead returned as top-level static procedures with
                               -- mangled names (ClassName@method) and explicit self parameters.
    }, instanceProcedures, classFunDecls)
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

/-- Information extracted from the prelude that `pythonToLaurel` needs.
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
  /-- Function that may return Any of exception -/
  maybeExceptionFunctions : List String := []
  /-- Procedure names (non-function callables) -/
  procedureNames : List String := []
  /-- Names of procedures with transparent bodies (can be inlined). -/
  inlinableProcedures : Std.HashSet String := {}
  /-- Maps Python-visible names to their structured symbol info.
      Includes both canonical Laurel names and unprefixed aliases. -/
  importedSymbols : Std.HashMap String ImportedSymbol := {}
  /-- Classes whose spec is considered exhaustive (lists all methods).
      Only these classes trigger "Unknown method" errors for unmodeled calls. -/
  exhaustiveClasses : Std.HashSet String := {}

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
      | .Alias ta => s.insert ta.name.text
  compositeTypes :=
    prog.types.foldl (init := {}) fun s td =>
      match td with
      | .Composite ct => s.insert ct.name.text
      | _ => s
  procedures :=
    prog.staticProcedures.foldl (init := {}) fun m p =>
      if p.body.isExternal || p.isFunctional then m
      else
        -- Use "Any" for all parameter types to match the Python→Laurel
        -- pipeline's Any-wrapping convention at call sites.
        let ins := p.inputs.map fun _ => "Any"
        let outs := p.outputs.map fun _ => "Any"
        m.insert p.name.text { inputs := ins, outputs := outs }
  functionSignatures :=
    prog.staticProcedures.filterMap fun p =>
      if p.body.isExternal then none
      else
        let noneexpr : Python.expr SourceRange := .Constant default (.ConNone default) default
        let args := p.inputs.map fun param =>
          let argName := if param.name.text.startsWith paramInputPrefix then
            (param.name.text.drop paramInputPrefix.length).toString
          else param.name.text
          {name:= argName, source := none, laurelType := param.type, typeTesters := pyLauTypeTesters [getHighTypeName param.type.val], default:= some noneexpr}
        let ret := p.outputs.head?.map fun param =>
          let tys := [getHighTypeName param.type.val]
          { source := none, laurelType := param.type,
            typeTesters := pyLauTypeTesters tys : PyRetInfo }
        some { name := p.name.text, args := args, kwargsName := none, ret := ret }
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
  maybeExceptionFunctions :=  prog.staticProcedures.filterMap fun p =>
    if p.name.text ∈ AnyMaybeExceptionList then some p.name.text else none
  procedureNames :=
    prog.staticProcedures.filterMap fun p =>
      if p.body.isExternal || p.isFunctional then none else some p.name.text
  inlinableProcedures :=
    prog.staticProcedures.foldl (init := {}) fun s p =>
      if p.body.isTransparent then s.insert p.name.text else s

/-- Merge two `PreludeInfo` values by concatenating each field. -/
def PreludeInfo.merge (a b : PreludeInfo) : PreludeInfo where
  types := b.types.fold (init := a.types) fun s n => s.insert n
  compositeTypes := b.compositeTypes.fold (init := a.compositeTypes) fun s n => s.insert n
  procedures := b.procedures.fold (init := a.procedures) fun m k v => m.insert k v
  functionSignatures := a.functionSignatures ++ b.functionSignatures
  functions := a.functions ++ b.functions
  maybeExceptionFunctions := a.maybeExceptionFunctions ++ b.maybeExceptionFunctions
  procedureNames := a.procedureNames ++ b.procedureNames
  inlinableProcedures := b.inlinableProcedures.fold (init := a.inlinableProcedures) fun s n => s.insert n
  importedSymbols := b.importedSymbols.fold (init := a.importedSymbols) fun m k v => m.insert k v

/-- Translate Python module to Laurel Program using pre-extracted prelude info. -/
def pythonToLaurel (info : PreludeInfo)
    (body : Array (stmt SourceRange))
    (filePath : String := "")
    (overloadTable : OverloadTable := {})
    : Except TranslationError (Laurel.Program × TranslationContext) := do
  -- Collect user function names (top-level and class methods)
  let userFunctions := body.toList.flatMap fun stmt =>
    match stmt with
    | .FunctionDef _ name _ _ _ _ _ _ => [name.val]
    | .ClassDef _ className _ _ clsBody _ _ =>
      clsBody.val.toList.filterMap fun s =>
        match s with
        | .FunctionDef _ methodName _ _ _ _ _ _ =>
          some (manglePythonMethod className.val methodName.val)
        | _ => none
    | _ => []
  -- Identify classes involved in inheritance hierarchies. Method calls on
  -- these classes may be dynamically dispatched, so call sites conservatively
  -- emit holes instead of static calls.
  let classesInHierarchy : Std.HashSet String := body.toList.foldl (init := {}) fun acc stmt =>
    match stmt with
    | .ClassDef _ className bases _ _ _ _ =>
      let hasNontrivialBases := bases.val.toList.any fun b =>
        match b with
        | Python.expr.Name _ ⟨_, "object"⟩ _ => false
        | _ => true
      let acc := bases.val.toList.foldl (init := acc) fun acc' b =>
        match b with
        | Python.expr.Name _ ⟨_, baseName⟩ _ =>
          if baseName == "object" then acc' else acc'.insert baseName
        | _ => acc'
      if hasNontrivialBases then acc.insert className.val else acc
    | _ => acc
  let pyErrorTy : CompositeType := {
    name := {text := "PythonError" }
    extending := []  -- No inheritance support for now
    fields := [{name:= "response", isMutable:= false, type:= AnyTy}]
    instanceProcedures := []
  }

  let overloadCompositeType := Std.HashSet.ofList $
      (overloadTable.values.flatMap (·.entries.values)).map fun ident =>
        if ident.pythonModule.isEmpty then
          ident.name
        else
          ident.pythonModule ++ "_" ++ ident.name
  let mut compositeTypeNames := info.compositeTypes.union overloadCompositeType

  -- FIRST PASS: Collect all class definitions and field type info
  let mut procedures : Array Procedure := #[]
  let mut compositeTypes : Array TypeDefinition := #[.Composite pyErrorTy]
  compositeTypeNames := compositeTypeNames.insert "PythonError"
  let mut classFieldHighType : Std.HashMap String (Std.HashMap String HighType) := {}
  let mut allClassFuncDecls : List PythonFunctionDecl := []
  let mut exhaustiveClasses := info.exhaustiveClasses
  for stmt in body do
    match stmt with
    | .ClassDef _ _ _ _ _ _ _ =>
      -- Build importedSymbols with user-defined classes discovered so far
      let localSymbols := compositeTypeNames.fold
        (init := info.importedSymbols) fun m name =>
          m.insert name (ImportedSymbol.compositeType name)
      let initCtx : TranslationContext := {
        functionSignatures := info.functionSignatures ++ allClassFuncDecls
        preludeTypes := info.types,
        importedSymbols := localSymbols,
        compositeTypeReverse := localSymbols.fold (init := ({}:Std.HashMap String String)) fun m k v =>
          match v with
          | .compositeType laurelName => if laurelName != k then m.insert laurelName k else m
          | _ => m,
        overloadTable := overloadTable,
        classFieldHighType := classFieldHighType,
        userFunctions := userFunctions,
        classesInHierarchy := classesInHierarchy,
        filePath := filePath
      }
      let (composite, instanceProcedures, classFuncDecls) ← translateClass initCtx stmt
      allClassFuncDecls := allClassFuncDecls ++ classFuncDecls
      procedures := procedures ++ instanceProcedures
      compositeTypes := compositeTypes.push <| .Composite composite
      compositeTypeNames := compositeTypeNames.insert composite.name.text
      -- User-defined classes are exhaustive: all methods are visible
      exhaustiveClasses := exhaustiveClasses.insert composite.name.text
      -- Collect field types for Any coercions in field accesses
      let fieldMap := composite.fields.foldl (fun m f => m.insert f.name.text f.type.val) (classFieldHighType[composite.name.text]?.getD {})
      classFieldHighType := classFieldHighType.insert composite.name.text fieldMap
    | _ => pure ()

  -- Merge user-defined class names into importedSymbols
  let importedSymbols := compositeTypeNames.fold
    (init := info.importedSymbols) fun m name =>
      m.insert name (ImportedSymbol.compositeType name)

  -- Precompute reverse map: laurelName → pythonName for composite types
  let compositeTypeReverse := importedSymbols.fold (init := ({}:Std.HashMap String String)) fun m k v =>
    match v with
    | .compositeType laurelName => if laurelName != k then m.insert laurelName k else m
    | _ => m

  let mut ctx : TranslationContext := {
    currentClassName := none,
    functionSignatures := info.functionSignatures ++ allClassFuncDecls
    preludeTypes := info.types,
    preludeProcedures := info.procedures,
    userFunctions := userFunctions,
    maybeExceptionFunctions := info.maybeExceptionFunctions
    classFieldHighType := classFieldHighType,
    overloadTable := overloadTable,
    importedSymbols := importedSymbols,
    compositeTypeReverse := compositeTypeReverse,
    exhaustiveClasses := exhaustiveClasses,
    classesInHierarchy := classesInHierarchy,
    filePath := filePath
  }

  -- Separate functions from other statements
  let mut otherStmts : Array (Python.stmt SourceRange) := #[]

  for stmt in body do
    match stmt with
    | .FunctionDef _ _ _ fbody _ _ _ _ =>
      let funcDecl ←  pyFuncDefToPythonFunctionDecl ctx stmt
      let proc ← translateFunction ctx stmt.ann funcDecl fbody.val.toList
      ctx := {ctx with functionSignatures:= ctx.functionSignatures ++ [funcDecl]}
      procedures := procedures.push proc.fst
    | .ClassDef _ _ _ _ _ _ _ =>
      pure ()  -- Already processed in first pass
    | .Assign _ targets value _ =>
      -- Detect type alias pattern: `MyInt = int` (single Name target, Name RHS that is a known type).
      -- Current scope (intentional limitations for initial version):
      --   • Only simple `X = <name>` where RHS passes `isKnownType` (primitives, core mappings,
      --     imported composites, prelude types).
      --   • Chained aliases (`A = int; B = A`) are not detected — newly created aliases are not
      --     added to `isKnownType`'s lookup sets. The transitive resolution in `TypeAliasElim`
      --     handles chains, but the Python frontend won't produce them yet.
      --   • Complex type aliases (`MyDict = Dict[str, Any]`) are not detected — the RHS must be
      --     a `.Name` node, not `.Subscript`.
      --   • PEP 695 `type` statements (`type X = int`) are not handled.
      if targets.val.size == 1 then
        match targets.val[0]!, value with
        | .Name _ lhsName _, .Name _ rhsName _ =>
          if isKnownType ctx rhsName.val then
            let targetTy ← translateType ctx rhsName.val
            compositeTypes := compositeTypes.push (.Alias { name := mkId lhsName.val, target := targetTy })
          else
            otherStmts := otherStmts.push stmt
        | _, _ => otherStmts := otherStmts.push stmt
      else
        otherStmts := otherStmts.push stmt
    | _ =>
      otherStmts := otherStmts.push stmt

  let nameDecl : Python.stmt SourceRange := .AnnAssign default (.Name default {val:= "__name__", ann:= default} default)
                              (.Name default {val:= "str", ann:= default} default)
                              {val:= some $ .Constant default (.ConString default {val:= "__main__", ann:= default}) default , ann:= default}
                              default
  let (bodyBlock, _) ← translateFunctionBody ctx none [] (nameDecl::otherStmts.toList)

  let md := sourceRangeToSource ctx.filePath { start := 0, stop := 0 }
  let mainProc : Procedure := {
    name := { text := "__main__", source := md },
    inputs := [],
    outputs := [{ name := PyLauFuncReturnVar, type := AnyTy }],
    preconditions := [],
    decreases := none,
    body := .Transparent bodyBlock
    isFunctional := false
  }

  -- Generate $composite_to_string_<type> and $composite_to_string_any_<type>
  -- for each composite type. These take a composite, so heap parameterization
  -- will add a Heap parameter, ensuring the verifier does not assume referential
  -- transparency across heap mutations.
  for ct in compositeTypes do
    match ct with
    | .Alias _ => pure ()  -- aliases have no composite layout; skip
    | _ =>
    let selfParam : Parameter := { name := "self", type := mkHighTypeMd (.UserDefined ct.name.text) }
    procedures := procedures.push
      { name := { text := compositeToStringName ct.name.text }
        inputs := [selfParam]
        outputs := [{ name := "result", type := mkHighTypeMd .TString }]
        preconditions := []
        decreases := none
        body := .Opaque [] none []
        isFunctional := false }
    procedures := procedures.push
      { name := { text := compositeToStringAnyName ct.name.text }
        inputs := [selfParam]
        outputs := [{ name := "result", type := AnyTy }]
        preconditions := []
        decreases := none
        body := .Opaque [] none []
        isFunctional := false }

  let program : Laurel.Program := {
    staticProcedures := (procedures.push mainProc).toList
    staticFields := []
    types := compositeTypes.toList
    constants := []
  }

  return (program, ctx)

end -- public section
end Strata.Python

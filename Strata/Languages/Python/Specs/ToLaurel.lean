/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
import Strata.DDM.Format
import Strata.Languages.Python.OverloadTable
import Strata.Languages.Python.PythonLaurelTypedExpr
public import Strata.Languages.Python.Specs.Decls
public import Strata.Languages.Python.Specs.Error
import Strata.Languages.Python.Specs.DDM
import Strata.Util.DecideProp

/-!
# PySpec to Laurel Translation

This module provides translation from PySpec signatures to Laurel declarations.

PySpec files contain type signatures extracted from Python code. This translator
converts those signatures into Laurel programs that can be verified.

## Translation Strategy

- `functionDecl`: Functions become Laurel procedures with opaque bodies
- `classDef`: Classes become composite types plus methods as procedures
- `typeDef`: Type definitions become composite type placeholders
- `externTypeDecl`: Ignored — PySpec fully qualifies imported class names
-/

namespace Strata.Python

public section

/-- Map a PythonIdent to its PyLauType string name, if it's a recognized
    builtin type. This is the single source of truth for which Python builtins
    map to PyLauType names. Used by PySpecPipeline (for type extraction).
    Keep in sync with `pyLauTypesWithTesters` in PythonToLaurel.lean. -/
def PythonIdent.toPyLauType? (id : PythonIdent) : Option String :=
  if id == PythonIdent.builtinsInt then some "int"
  else if id == PythonIdent.builtinsStr then some "str"
  else if id == PythonIdent.builtinsBool then some "bool"
  else if id == PythonIdent.builtinsFloat then some "float"
  else if id == PythonIdent.noneType then some "None"
  else none

end -- public section
end Strata.Python

namespace Strata.Python.Specs.ToLaurel

open Strata.Laurel
open Strata.Python.Laurel
open Strata.Python.Specs (SpecError)

/-! ## ToLaurelM Monad -/

/-- Context for PySpec to Laurel translation. -/
structure ToLaurelContext where
  filepath : System.FilePath
  /-- Module prefix prepended to generated type and procedure names
      to avoid collisions when multiple PySpec files are combined. -/
  modulePrefix : String

/-- State for PySpec to Laurel translation. -/
structure ToLaurelState where
  errors : Array SpecError := #[]
  procedures : Array Procedure := #[]
  types : Array TypeDefinition := #[]
  overloads : OverloadTable := {}
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}

/-- Monad for PySpec to Laurel translation. -/
abbrev ToLaurelM := ReaderT ToLaurelContext (StateM ToLaurelState)

/-- Report an error during translation. -/
def reportError (kind : WarningKind) (loc : SourceRange) (message : String) : ToLaurelM Unit := do
  let e : SpecError := ⟨(←read).filepath, loc, kind, message⟩
  modify fun s => { s with errors := s.errors.push e }

def runChecked (act : ToLaurelM α) : ToLaurelM (α × Bool) := do
  let old := (←get).errors.size
  let r ← act
  let new := (←get).errors.size
  pure (r, old = new)

/-- Add a Laurel procedure to the output. -/
def pushProcedure (proc : Procedure) : ToLaurelM Unit :=
  modify fun s => { s with procedures := s.procedures.push proc }

/-- Add a Laurel type definition to the output. -/
def pushType (td : TypeDefinition) : ToLaurelM Unit :=
  modify fun s => { s with types := s.types.push td }

/-- Add an overload dispatch entry for a function. -/
def pushOverloadEntry (funcName : String) (paramName : String)
    (literalValue : String) (returnType : PythonIdent) : ToLaurelM Unit :=
  modify fun s =>
    let existing := s.overloads.getD funcName {}
    let updated : FunctionOverloads := { existing with
      paramName := existing.paramName <|> some paramName
      entries := existing.entries.insert literalValue returnType }
    if existing.paramName.any (· != paramName) then
      dbg_trace s!"Warning: overload entries for '{funcName}' disagree on \
        dispatch parameter name: existing '{existing.paramName.get!}', new '{paramName}'"
      { s with overloads := s.overloads.insert funcName updated }
    else
      { s with overloads := s.overloads.insert funcName updated }

/-- Prepend the module prefix to a name. Returns the name unchanged
    if the prefix is empty. -/
def prefixName (name : String) : ToLaurelM String := do
  let ctx ← read
  if ctx.modulePrefix.isEmpty then return name
  return ctx.modulePrefix ++ "_" ++ name

/-! ## Helper Functions -/

/-- Create a HighTypeMd with default metadata. -/
private def mkTy (ty : HighType) : HighTypeMd :=
  { val := ty, source := none }

/-- Create a UserDefined type referencing a Laurel prelude type by name. -/
private def mkUserDefined (s : String) : HighTypeMd :=
  { val := .UserDefined (mkId s), source := none }

/-- Placeholder for types not yet supported in CorePrelude.
    Returns TString so translation can proceed. Callers should
    report a warning via `reportError` so the gap is visible. -/
private def unsupportedType : HighTypeMd :=
  { val := .TString, source := none }

/-! ### Laurel type constants

Named constants for Laurel `HighTypeMd` values used in type translation.
Prelude types (`Any`, `Error`, `DictStrAny`, etc.) use `UserDefined` so
they participate in Laurel resolution. -/

private def tyBool     : HighTypeMd := mkTy .TBool
private def tyInt      : HighTypeMd := mkTy .TInt
private def tyReal     : HighTypeMd := mkTy .TReal
private def tyString   : HighTypeMd := mkTy .TString
private def tyVoid     : HighTypeMd := mkTy .TVoid

private def tyAny         : HighTypeMd := mkUserDefined "Any"
private def tyDictStrAny  : HighTypeMd := mkUserDefined "DictStrAny"
private def tyError       : HighTypeMd := mkUserDefined "Error"
private def tyListStr     : HighTypeMd := mkUserDefined "ListStr"
private def tyStrOrNone   : HighTypeMd := mkUserDefined "StrOrNone"
private def tyIntOrNone   : HighTypeMd := mkUserDefined "IntOrNone"
private def tyBoolOrNone  : HighTypeMd := mkUserDefined "BoolOrNone"

mutual

/-- Convert a SpecAtomType to a string for error messages. -/
def atomTypeToString (a : SpecAtomType) : String :=
  match a with
  | .ident nm args =>
    if nm == PythonIdent.noneType && args.isEmpty then "None"
    else if args.isEmpty then toString nm
    else
      let argStrs := args.map specTypeToString
      s!"{nm}[{String.intercalate ", " argStrs.toList}]"
  | .intLiteral v => s!"Literal[{v}]"
  | .stringLiteral v => s!"Literal[\"{v}\"]"
  | .typedDict _ _ _ => "TypedDict"
termination_by sizeOf a

/-- Convert a SpecType to a string for error messages. -/
def specTypeToString (t : SpecType) : String :=
  if h : t.atoms.size = 1 then
    atomTypeToString t.atoms[0]
  else
    let strs := t.atoms.map atomTypeToString
    String.intercalate " | " strs.toList
termination_by sizeOf t
decreasing_by
  · cases t
    decreasing_tactic
  · cases t
    decreasing_tactic

end

/-- Pretty print a union type. -/
def formatUnionType (atoms : Array SpecAtomType) : String :=
  let strs := atoms.map atomTypeToString
  String.intercalate " | " strs.toList

/-! ## Type Translation -/

/--
Detect if a SpecType is a Union[None, T] pattern and return the appropriate Laurel type.
Handles:
- Union[None, str] → UserDefined "StrOrNone"
- Union[None, int] → UserDefined "IntOrNone"
- Union[None, bool] → UserDefined "BoolOrNone"
- Union[None, Literal["A"], ...] → UserDefined "StrOrNone"
- Union[None, Literal[1], ...] → UserDefined "IntOrNone"
- Union[None, TypedDict] → UserDefined "DictStrAny"
- Union[None, float/List/Dict/Any/bytes] → TString (unsupported, pending CorePrelude)
-/
def detectOptionalType (ty : SpecType) : ToLaurelM (Option HighTypeMd) := do
  let isNoneType (atom : SpecAtomType) : Bool :=
    match atom with
    | .ident nm args => nm == PythonIdent.noneType && args.isEmpty
    | _ => false

  if !ty.atoms.any isNoneType then
    return none

  let otherAtoms := ty.atoms.filter (fun a => !isNoneType a)

  -- All non-None string literals → StrOrNone
  if otherAtoms.all (fun a => match a with | .stringLiteral _ => true | _ => false) then
    return some tyStrOrNone

  -- All non-None int literals → IntOrNone
  if otherAtoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
    return some tyIntOrNone

  -- All non-None TypedDicts → DictStrAny
  if otherAtoms.all (fun a => match a with | .typedDict _ _ _ => true | _ => false) then
    return some tyDictStrAny

  if otherAtoms.size == 1 then
    match otherAtoms[0]! with
    | .ident nm _ =>
      if nm == PythonIdent.builtinsStr then return some tyStrOrNone
      else if nm == PythonIdent.builtinsInt then return some tyIntOrNone
      else if nm == PythonIdent.builtinsBool then return some tyBoolOrNone
      -- TODO: add CorePrelude types for these Optional patterns
      else if nm == PythonIdent.builtinsFloat then
        reportError .unsupportedOptionalFloat default s!"Optional[float] mapped to TString"
        return some unsupportedType
      else if nm == PythonIdent.typingList then
        reportError .unsupportedOptionalList default s!"Optional[List] mapped to TString"
        return some unsupportedType
      else if nm == PythonIdent.typingDict then
        reportError .unsupportedOptionalDict default s!"Optional[Dict] mapped to TString"
        return some unsupportedType
      else if nm == PythonIdent.typingAny then
        reportError .unsupportedOptionalAny default s!"Optional[Any] mapped to TString"
        return some unsupportedType
      else if nm == PythonIdent.builtinsBytes then
        reportError .unsupportedOptionalBytes default s!"Optional[bytes] mapped to TString"
        return some unsupportedType
      else return none
    | .typedDict _ _ _ => return some tyDictStrAny
    | .intLiteral _ => return some tyIntOrNone
    | _ => return none
  else
    return none

/-- Known PythonIdent → Laurel type mappings for single-atom ident types.
    Matches PythonToLaurel's type mapping: only int, str, bool, float get
    concrete Laurel types; everything else maps to Any. -/
private def knownIdentTypes : Std.HashMap PythonIdent HighTypeMd :=
  .ofList [
    (.builtinsBool,      tyBool),
    (.builtinsBytearray, tyAny),
    (.builtinsBytes,     tyAny),
    (.builtinsComplex,   tyAny),
    (.builtinsDict,      tyAny),
    (.builtinsException, tyAny),
    (.builtinsFloat,     tyReal),
    (.builtinsInt,       tyInt),
    (.builtinsStr,       tyString),
    (.noneType,          tyVoid),
    (.typingAny,         tyAny),
    (.typingBinaryIO,    tyAny),
    (.typingDict,        tyAny),
    (.typingList,        tyAny),
  ]

/-- Convert a SpecType to a Laurel HighTypeMd. -/
def specTypeToLaurelType (ty : SpecType) : ToLaurelM HighTypeMd := do
  match ty.atoms.size with
  | 0 =>
    reportError .emptyType default "Empty type (no atoms) encountered in Laurel conversion"
    return tyString
  | _ =>
    -- Check for union types
    if ty.atoms.size > 1 then
      -- All string literals → TString
      if ty.atoms.all (fun a => match a with | .stringLiteral _ => true | _ => false) then
        return tyString
      -- All int literals → TInt
      if ty.atoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
        return tyInt
      -- All TypedDicts → DictStrAny
      if ty.atoms.all (fun a => match a with | .typedDict _ _ _ => true | _ => false) then
        return tyDictStrAny
      -- Check Union[None, T] patterns
      match ← detectOptionalType ty with
      | some laurelType => return laurelType
      | none =>
        let unionStr := formatUnionType ty.atoms
        reportError .unsupportedUnion default s!"Union type ({unionStr}) not yet supported in Laurel"
        return tyString
    else
      pure ()
    -- Single atom type
    match ty.atoms[0]! with
    | .ident nm _args =>
      if let some ty := knownIdentTypes[nm]? then
        return ty
      let prefixed ← prefixName nm.name
      return mkTy (.UserDefined { text := prefixed })
    | .intLiteral _ => return tyInt
    | .stringLiteral _ => return tyString
    | .typedDict _ _ _ => return tyDictStrAny

/-! ## SpecExpr to Laurel Translation -/

/-- Create file-level source from the current pyspec filepath.
    Uses a default (zero) source range; callers with a specific location
    should use `mkSourceWithFileRange` instead. -/
private def mkFileSource : ToLaurelM (Option FileRange) := do
  let ctx ← read
  let fr : FileRange := { file := .file ctx.filepath.toString, range := default }
  return some fr

/-- Create source with a file range from the current pyspec file. -/
private def mkSourceWithFileRange (loc : SourceRange)
    : ToLaurelM (Option FileRange) := do
  let ctx ← read
  let fr : FileRange := { file := .file ctx.filepath.toString, range := loc }
  return some fr

/-- Wrap a StmtExpr with source containing a file range. -/
private def mkStmtWithLoc (e : StmtExpr) (loc : SourceRange)
    : ToLaurelM StmtExprMd := do
  let ctx ← read
  let fr : FileRange := { file := .file ctx.filepath.toString, range := loc }
  return { val := e, source := some fr }

/--
Context for resolving identifiers.
-/
structure SpecExprContext where
  procName : String
  argTypes : Std.HashMap String HighType

abbrev ToLaurelExprM := ReaderT SpecExprContext ToLaurelM

private def asAny (loc : SourceRange) (act : ToLaurelExprM SomeTypedStmtExpr) : ToLaurelExprM (TypedStmtExpr Laurel.tyAny) := do
  let ctx ← read
  let (se, success) ← runChecked <| act ctx
  if !success then
    return ⟨se.2.stmt⟩
  match se with
  | ⟨.UserDefined "Any", e⟩ => pure e
  | ⟨tp, e⟩ =>
    let pn := (← read).procName
    reportError .typeError loc s!"Expected Any-typed expression but got {repr tp} in '{pn}'"
    pure ⟨e.stmt⟩

private def asBool (loc : SourceRange) (act : ToLaurelExprM SomeTypedStmtExpr) : ToLaurelExprM (TypedStmtExpr .TBool) := do
  let ctx ← read
  let (se, success) ← runChecked <| act ctx
  if !success then
    return ⟨se.2.stmt⟩
  match se with
  | ⟨.TBool, e⟩ => pure e
  | ⟨tp, e⟩ =>
    let pn := (← read).procName
    reportError .typeError loc s!"Expected Bool-typed expression but got {repr tp} in '{pn}'"
    pure ⟨e.stmt⟩

/-- Look up an identifier's type from the SpecExprContext and create a typed identifier.
    Reports a typeError if the name is not found in argTypes. -/
private def lookupIdentifier (name : String) (loc : SourceRange) (source : Option FileRange)
    : ToLaurelExprM SomeTypedStmtExpr := do
  match (← read).argTypes[name]? with
  | some tp => return .mkSome <| .identifier name tp source
  | none =>
    let pn := (← read).procName
    reportError .typeError loc s!"Unknown identifier '{name}' in '{pn}'"
    return default

/-- Translate a SpecExpr to a typed Laurel expression (`SomeTypedStmtExpr`).
    Returns `default` (a `Hole`) for unsupported expressions; callers use
    `runChecked` to detect whether errors were reported during translation.
    Uses Core prelude function names (Any_len, DictStrAny_contains, etc.)
    which are resolved after the Core prelude is prepended. -/
def specExprToLaurel (e : SpecExpr) (source : Option FileRange)
  : ToLaurelExprM SomeTypedStmtExpr :=
  -- Use per-node source range when available, falling back to the
  -- nearest ancestor's source for nodes with default (empty) locations.
  -- This is intentional: the parent's location is a closer approximation
  -- than the function-level source for nodes without their own location.
  let nodeSource (loc : SourceRange) : ToLaurelM (Option FileRange) := do
    if loc == default then
      pure source
    else do
      let fr : FileRange := { file := .file (← read).filepath.toString, range := loc }
      pure (some fr)
  match e with
  | .placeholder loc => do
    reportError .placeholderExpr loc "Placeholder expression not translatable"
    return default
  | .var name loc => do
    let src ← nodeSource loc
    lookupIdentifier name loc src
  | .intLit v loc => do
    let src ← nodeSource loc
    return .mkSome <| .fromInt (.literalInt v src)
  | .floatLit _ loc => do
    reportError .floatLiteral loc "Float literals not yet supported in preconditions"
    return default
  | .getIndex subject field loc =>
    match subject with
    | .var "kwargs" .. => do
      let src ← nodeSource loc
      lookupIdentifier field loc src
    | _ => do
      let src ← nodeSource loc
      let s ← asAny loc <| specExprToLaurel subject src
      let from_str := .fromStr (.literalString field src) src
      return .mkSome <| .anyGet s from_str src
  | .isInstanceOf _ typeName loc => do
    reportError .isinstanceUnsupported loc s!"isinstance check for '{typeName}' not yet supported in preconditions"
    return default
  | .len subject loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    return .mkSome <| .fromInt (.strLength (.anyAsString s))
  | .intGe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    return .mkSome <| .intGeq (.anyAsInt s) (.anyAsInt b)
  | .intLe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    return .mkSome <| .intLeq (.anyAsInt s) (.anyAsInt b)
  | .floatGe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    return .mkSome <| .realGeq (.anyAsFloat s) (.anyAsFloat b)
  | .floatLe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    return .mkSome <| .realLeq (.anyAsFloat s) (.anyAsFloat b)
  | .not inner loc => do
    let src ← nodeSource loc
    let i ← asBool loc <| specExprToLaurel inner src
    return .mkSome <| .not i
  | .implies cond body loc => do
    let src ← nodeSource loc
    let c ← asBool loc <| specExprToLaurel cond src
    let b ← asBool loc <| specExprToLaurel body src
    return .mkSome <| .implies c b
  | .enumMember subject values loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let sStr := s.anyAsString
    return .mkSome <|
      values.foldl (init := .literalBool false) fun acc v =>
        .or acc (.stringEq sStr (.literalString v src))
  | .containsKey container key loc => do
    let src ← nodeSource loc
    match container with
    | .var "kwargs" .. =>
      -- FIXME: Check this.  We may want to move this up
      let keyAny ← asAny loc <| lookupIdentifier key loc src
      return .mkSome <| .not (.anyIsfromNone keyAny)
    | _ =>
      let c ← asAny loc <| specExprToLaurel container src
      return .mkSome <| .dictStrAnyContains (c.anyAsDict) (.literalString key)
  | .regexMatch subject pattern loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let sStr := .anyAsString s
    return .mkSome <| .reSearchBool (.literalString pattern) sStr
  | .forallList _ _ _ loc => do
    reportError .forallListUnsupported loc "forallList quantifier not yet supported in preconditions"
    return default
  | .forallDict _ _ _ _ loc => do
    reportError .forallDictUnsupported loc "forallDict quantifier not yet supported in preconditions"
    return default

private def formatAssertionMessage (msg : Array MessagePart) : String :=
  let parts := msg.map fun
    | .str s => s
    | .expr e => toString e
  String.join parts.toList

/-- Structured PySpec assertion messages. Rendered to string before storing
    in metadata so that rewording is centralized. -/
inductive SpecAssertMsg where
  | requiredParam (param : String)
  | userAssertion (text : String)
  | unnamed (index : Nat)

/-- Render a structured assertion message to a human-readable string. -/
def SpecAssertMsg.render : SpecAssertMsg → String
  | .requiredParam param => s!"'{param}' is required"
  | .userAssertion text  => text
  | .unnamed index       => s!"precondition {index}"

/-- Build a procedure body that asserts preconditions.
    Outputs are already initialized non-deterministically. -/
def buildSpecBody (preconditions : Array Assertion)
    (source : Option FileRange)
    (ctx : SpecExprContext)
    (requiredParams : Array String := #[])
    : ToLaurelM Body := do
  let fileSource ← mkFileSource
  let mut stmts : Array StmtExprMd := #[]
  let mut idx := 0
  -- Assert that required parameters are provided (not None)
  for param in requiredParams do
    let cond : TypedStmtExpr _ := .not (.anyIsfromNone (.identifier param Laurel.tyAny))
    let msg := SpecAssertMsg.requiredParam param |>.render
    let assertStmt ← mkStmtWithLoc (.Assert { condition := cond.stmt, summary := some msg }) default
    stmts := stmts.push assertStmt
    idx := idx + 1
  for assertion in preconditions do
    let formattedMsg := formatAssertionMessage assertion.message
    let msg := if formattedMsg.isEmpty
      then SpecAssertMsg.unnamed idx |>.render
      else SpecAssertMsg.userAssertion formattedMsg |>.render
    let (⟨condType, condExpr⟩, success) ← runChecked <| specExprToLaurel assertion.formula source ctx
    if success then
      if let .TBool := condType then
        let assertStmt ← mkStmtWithLoc (.Assert { condition := condExpr.stmt, summary := some msg }) default
        stmts := stmts.push assertStmt
      else
        reportError .typeError default
          s!"Precondition expression is not Bool in '{ctx.procName}' (skipping): {msg}"
    idx := idx + 1
  let body := {
      val := .Block stmts.toList none,
      source := fileSource
  }
  return .Transparent body

/-! ## Declaration Translation -/

/-- Convert an Arg to a Laurel Parameter. -/
def argToParameter (arg : Arg) : ToLaurelM Parameter := do
  let ty ← specTypeToLaurelType arg.type
  return { name := arg.name, type := ty }

/-- Expand a `**kwargs: Unpack[TypedDict]` into individual `Arg` entries.
    Returns an error if kwargs is present but not a TypedDict. -/
public def expandKwargsArgs (kwargs : Option (String × SpecType))
    : Except String (Array Arg) :=
  match kwargs with
  | none => .ok #[]
  | some (name, specType) =>
    match specType.atoms.find? fun a => match a with | .typedDict .. => true | _ => false with
    | some (.typedDict fields fieldTypes fieldRequired) =>
      .ok <| fields.mapIdx fun i name =>
        { name := name
          type := fieldTypes.getD i default
          default := if fieldRequired.getD i true then none else some .none }
    | _ => .error s!"**{name} has non-TypedDict type; kwargs not expanded"

/-- Convert a function declaration to a Laurel Procedure.
    When `isMethod` is true, the first positional arg (`self`) is stripped. -/
def funcDeclToLaurel (procName : String) (func : FunctionDecl)
    (isMethod : Bool := false) : ToLaurelM Procedure := do
  if isMethod && func.args.args.size == 0 then
    reportError .missingMethodSelf default
      s!"Method '{func.name}' has no arguments (expected 'self' as first parameter)"
  let posArgs := if isMethod then func.args.args.extract 1 func.args.args.size
                 else func.args.args
  let kwargsArgs ← match expandKwargsArgs func.args.kwargs with
    | .ok args => pure args
    | .error msg => do reportError .kwargsExpansionError default msg; pure #[]
  let allArgs := posArgs ++ func.args.kwonly ++ kwargsArgs
  let inputs ← allArgs.mapM argToParameter
  let retType ← specTypeToLaurelType func.returnType
  let outputs : List Parameter :=
    [{ name := "result", type := match retType.val with
      | .TVoid => tyAny
      | _ => retType }]
  if func.postconditions.size > 0 then
    reportError .postconditionUnsupported func.loc "Postconditions not yet supported"
  -- When preconditions exist, use TCore "Any" for all parameters and outputs
  -- to match the Python→Laurel pipeline's Any-wrapping convention.
  let (inputs, outputs, body) ←
    if func.preconditions.size > 0 then do
      let anyTy : HighTypeMd := tyAny
      let anyInputs := inputs.map fun p => { p with type := anyTy }
      let anyOutputs := outputs.map fun p => { p with type := anyTy }
      let argTypes := allArgs.foldl (init := {}) fun m a =>
        m.insert a.name Laurel.tyAny
      let specCtx : SpecExprContext := { procName, argTypes }
      let body ← buildSpecBody func.preconditions none specCtx
        (requiredParams := allArgs.filterMap fun a =>
          if a.default.isNone then some a.name else none)
      pure (anyInputs, anyOutputs, body)
    else
      pure (inputs, outputs, Body.Opaque [] none [])
  let src ← mkSourceWithFileRange func.loc
  return {
    name := { text := procName, source := src }
    inputs := inputs.toList
    outputs := outputs
    preconditions := []
    decreases := none
    isFunctional := false
    body := body
  }

/-- Convert a class definition to Laurel types and procedures. -/
def classDefToLaurel (cls : ClassDef) : ToLaurelM Unit := do
  let prefixedName ← prefixName cls.name
  -- Register alias from unprefixed to prefixed name for type resolution
  if prefixedName != cls.name then
    modify fun s => { s with typeAliases := s.typeAliases.insert cls.name prefixedName }
  if cls.exhaustive then
    modify fun s => { s with exhaustiveClasses := s.exhaustiveClasses.insert prefixedName }
  let laurelFields ← cls.fields.toList.mapM fun f => do
    let ty ← specTypeToLaurelType f.type
    pure { name := f.name, isMutable := true, type := ty : Laurel.Field }
  let prefixedBases ← cls.bases.toList.mapM fun cd => do
    -- Local bases (empty pythonModule) get prefixed; external ones don't
    let baseName ← if cd.pythonModule.isEmpty then prefixName cd.name
                    else pure (toString cd)
    return mkId baseName
  pushType (.Composite {
    name := prefixedName
    extending := prefixedBases
    fields := laurelFields
    instanceProcedures := []
  })
  for method in cls.methods do
    let proc ← funcDeclToLaurel (prefixedName ++ "@" ++ method.name) method (isMethod := true)
    pushProcedure proc
  for sub in cls.subclasses do
    classDefToLaurel sub
decreasing_by
  · cases cls
    decreasing_tactic

/-- Convert a type definition to a Laurel composite type placeholder. -/
def typeDefToLaurel (td : TypeDef) : ToLaurelM Unit := do
  let prefixedName ← prefixName td.name
  pushType (.Composite {
    name := prefixedName
    extending := []
    fields := []
    instanceProcedures := []
  })

/-- Extract an overload dispatch entry from an `@overload` function declaration.
    Looks for a `stringLiteral` in the first argument's type and an `.ident`
    return type, and records them in the dispatch table. -/
def extractOverloadEntry (func : FunctionDecl) : ToLaurelM Unit := do
  let args := func.args.args
  let .isTrue _ := decideProp (args.size > 0)
    | reportError .overloadNoArgs func.loc
        s!"Overloaded function '{func.name}' has no arguments"
      return
  let firstArgType := args[0].type
  let .isTrue _ := decideProp (firstArgType.atoms.size = 1)
    | reportError .overloadArgArity func.loc
        s!"Overloaded function '{func.name}': first argument \
          has {firstArgType.atoms.size} type atoms, expected 1"
      return
  let literalValue ←
        match firstArgType.atoms[0] with
        | .stringLiteral v => pure v
        | _ =>
          reportError .overloadArgNotStringLiteral func.loc
            s!"Overloaded function '{func.name}': first argument \
              type '{specTypeToString firstArgType}' is not a \
              string literal (only string literal dispatch is \
              currently supported)"
          return
  let .isTrue _ := decideProp (func.returnType.atoms.size = 1)
    | reportError .overloadReturnArity func.loc
        s!"Overloaded function '{func.name}': return type \
        has {func.returnType.atoms.size} type atoms, expected 1"
      return
  let retType ←
        match func.returnType.atoms[0] with
        | .ident nm _ => pure nm
        | _ =>
          reportError .overloadReturnNotClass func.loc
            s!"Overloaded function '{func.name}': return type \
              '{specTypeToString func.returnType}' is not a \
              class type"
          return
  -- args[0].name is the formal parameter name from the PySpec (not a call-site argument)
  pushOverloadEntry func.name args[0].name literalValue retType

/-- Convert a single PySpec signature to Laurel declarations. -/
def signatureToLaurel (sig : Signature) : ToLaurelM Unit :=
  match sig with
  | .externTypeDecl .. =>
    -- No Laurel output needed: PySpec fully qualifies imported class names,
    -- so the local-name → PythonIdent mapping is not required here.
    pure ()
  | .typeDef td =>
    typeDefToLaurel td
  | .functionDecl func => do
    if func.isOverload then
      extractOverloadEntry func
    else do
      let procName ← prefixName func.name
      let proc ← funcDeclToLaurel procName func
      pushProcedure proc
  | .classDef cls => classDefToLaurel cls

/-- Result of translating PySpec signatures to Laurel. -/
public structure TranslationResult where
  program : Laurel.Program
  errors : Array SpecError
  overloads : OverloadTable
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}

/-- Run the translation and return a Laurel Program, dispatch table,
    and any errors. -/
public def signaturesToLaurel (filepath : System.FilePath) (sigs : Array Signature)
    (modulePrefix : String)
    : TranslationResult :=
  let ctx : ToLaurelContext := { filepath, modulePrefix }
  let ((), state) := (sigs.forM signatureToLaurel).run ctx |>.run {}
  let pgm : Laurel.Program := {
    staticProcedures := state.procedures.toList
    staticFields := []
    types := state.types.toList
    constants := []
  }
  { program := pgm
    errors := state.errors
    overloads := state.overloads
    typeAliases := state.typeAliases
    exhaustiveClasses := state.exhaustiveClasses }

/-- Extract only the overload dispatch table from PySpec signatures.
    Processes `@overload` function declarations, ignoring classDef,
    typeDef, externTypeDecl, and non-overload functions. -/
public def extractOverloads (filepath : System.FilePath) (sigs : Array Signature)
    : OverloadTable × Array SpecError :=
  let ctx : ToLaurelContext := { filepath, modulePrefix := "" }
  let action := sigs.forM fun sig =>
    match sig with
    | .functionDecl func =>
      if func.isOverload then extractOverloadEntry func
      else pure ()
    | _ => pure ()
  let ((), state) := action.run ctx |>.run {}
  (state.overloads, state.errors)

end Strata.Python.Specs.ToLaurel

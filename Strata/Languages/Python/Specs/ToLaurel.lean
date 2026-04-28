/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
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

/-- Map a PythonIdent directly to its Laurel type-tester predicate name
    (e.g., `builtins.int` → `"Any..isfrom_int"`), or `none` if no tester
    exists for this type. -/
def PythonIdent.toTypeTester? (id : PythonIdent) : Option String :=
  if id == .builtinsInt then some "Any..isfrom_int"
  else if id == .builtinsStr then some "Any..isfrom_str"
  else if id == .builtinsBool then some "Any..isfrom_bool"
  else if id == .builtinsFloat then some "Any..isfrom_float"
  else if id == .noneType then some "Any..isfrom_None"
  else none

/-- Fully qualified Laurel name for a `PythonIdent`: module dots become
    underscores. E.g., `"mylib.sub"` / `"Foo"` → `"mylib_sub_Foo"`. -/
def PythonIdent.toLaurelName (id : PythonIdent) : String :=
  let pfx := "_".intercalate (id.pythonModule.splitOn ".")
  if pfx.isEmpty then id.name else pfx ++ "_" ++ id.name

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

/-! ### Laurel type constants -/

private def tyAny         : HighTypeMd := mkUserDefined "Any"
private def tyDictStrAny  : HighTypeMd := mkUserDefined "DictStrAny"

/-! ## Type Translation -/

public def builtinIdents : Std.HashSet PythonIdent :=
  .ofList [
    .builtinsBool, .builtinsBytearray, .builtinsBytes, .builtinsComplex,
    .builtinsDict, .builtinsException, .builtinsFloat, .builtinsInt,
    .builtinsStr, .noneType, .typingAny, .typingBinaryIO, .typingDict,
    .typingList
  ]

/-- Convert a SpecType to a Laurel HighTypeMd.
    Composites → `UserDefined`, everything else → `Any`. -/
def specTypeToLaurelType (ty : SpecType) : ToLaurelM HighTypeMd := do
  match ty.asIdent with
  | some nm =>
    if nm ∈ builtinIdents then
      return tyAny
    return mkTy (.UserDefined { text := nm.toLaurelName })
  | none => return tyAny

-- FIXME: typeTester? seems buggy It seems like it should build a disjunction
-- over atoms.  This doesn't distinguish between types and could hide errors.
-- I think it should be converted to take specType and value and return
-- ToLaurelM (Option StmtExprMd) with None meaning no assertion needed
-- (e.g., ty is Any or a user-defined type).  If a type exists that is not
-- supported it should raise a warning.


/-- Map a SpecType to its `Any..isfrom_X` tester name, if applicable. -/
private def typeTester? (ty : SpecType) : Option String :=
  match ty.asIdent with
  | some id =>
    if id == .builtinsInt then some "Any..isfrom_int"
    else if id == .builtinsStr then some "Any..isfrom_str"
    else if id == .builtinsBool then some "Any..isfrom_bool"
    else if id == .builtinsFloat then some "Any..isfrom_float"
    else none
  | none => none

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
  | .stringLen subject loc => do
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

/-- Build a Transparent procedure body with havoc, type assertions,
    required-param checks, user preconditions, and return-type assumption. -/
def buildSpecBody (allArgs : Array Arg)
    (preconditions : Array Assertion)
    (postconditions : Array SpecExpr)
    (returnType : SpecType)
    (source : Option FileRange)
    (ctx : SpecExprContext)
    : ToLaurelM Body := do
  let fileSource ← mkFileSource
  let mut stmts : Array StmtExprMd := #[]
  -- 1. Havoc the result: result := Hole(nondet)
  let holeExpr : StmtExprMd := { val := .Hole (deterministic := false), source := none }
  let resultId : StmtExprMd := { val := .Identifier (mkId "result"), source := none }
  let assignStmt ← mkStmtWithLoc (.Assign [resultId] holeExpr) default
  stmts := stmts.push assignStmt
  -- 2. Assert type / required-param preconditions
  for arg in allArgs do
    let paramId : StmtExprMd := { val := .Identifier (mkId arg.name), source := none }
    match typeTester? arg.type with
    | some testerName =>
      let testerCall : StmtExprMd := { val := .StaticCall (mkId testerName) [paramId], source := none }
      if arg.default.isSome then
        let noneCheck : StmtExprMd := { val := .StaticCall (mkId "Any..isfrom_None") [paramId], source := none }
        let orExpr : StmtExprMd := { val := .PrimitiveOp .Or [noneCheck, testerCall], source := none }
        let assertStmt ← mkStmtWithLoc (.Assert { condition := orExpr, summary := none }) default
        stmts := stmts.push assertStmt
      else
        let assertStmt ← mkStmtWithLoc (.Assert { condition := testerCall, summary := none }) default
        stmts := stmts.push assertStmt
    | none =>
      if arg.default.isNone then
        let cond : TypedStmtExpr _ := .not (.anyIsfromNone (.identifier arg.name Laurel.tyAny))
        let msg := SpecAssertMsg.requiredParam arg.name |>.render
        let assertStmt ← mkStmtWithLoc (.Assert { condition := cond.stmt, summary := some msg }) default
        stmts := stmts.push assertStmt
  -- 4. Assert user pyspec preconditions
  let mut idx := 0
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
  -- 5. Assert user pyspec postconditions
  for postExpr in postconditions do
    let (⟨condType, condExpr⟩, success) ← runChecked <| specExprToLaurel postExpr source ctx
    if success then
      if let .TBool := condType then
        let assumeStmt ← mkStmtWithLoc (.Assume condExpr.stmt) default
        stmts := stmts.push assumeStmt
      else
        reportError .typeError default
          s!"Postcondition expression is not Bool in '{ctx.procName}' (skipping)"
  -- 6. Assume return type postcondition
  if let some testerName := typeTester? returnType then
    let resultRef : StmtExprMd := { val := .Identifier (mkId "result"), source := none }
    let testerCall : StmtExprMd := { val := .StaticCall (mkId testerName) [resultRef], source := none }
    let assumeStmt ← mkStmtWithLoc (.Assume testerCall) default
    stmts := stmts.push assumeStmt
  let body := {
      val := .Block stmts.toList none,
      source := fileSource
  }
  return .Transparent body

/-! ## Declaration Translation -/

/-- Expand a `**kwargs: Unpack[TypedDict]` into individual `Arg` entries.
    Returns an error if kwargs is present but not a TypedDict. -/
public def expandKwargsArgs (kwargs : Option (String × SpecType))
    : Except String (Array Arg) :=
  match kwargs with
  | none => .ok #[]
  | some (name, specType) =>
    match specType.asTypedDict with
    | some fields =>
      .ok <| fields.map fun f =>
        { name := f.name
          type := f.type
          default := if f.required then none else some .none }
    | none => .error s!"**{name} has non-TypedDict type; kwargs not expanded"

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
  let inputs ← allArgs.mapM fun a => do
    let ty ← specTypeToLaurelType a.type
    return ({ name := a.name, type := ty } : Parameter)
  let outputs : List Parameter := [{ name := "result", type := tyAny }]
  let argTypes : Std.HashMap String HighType :=
    inputs.foldl (init := ({} : Std.HashMap String HighType).insert "result" Laurel.tyAny) fun m p =>
      m.insert p.name.text p.type.val
  let specCtx : SpecExprContext := { procName, argTypes }
  let body ← buildSpecBody allArgs func.preconditions func.postconditions
    func.returnType none specCtx
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
  let prefixedBases := cls.bases.toList.map fun cd =>
    mkId cd.toLaurelName
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
  let literalValue ←
        match firstArgType.asStringLiteral with
        | some v => pure v
        | none =>
          reportError .overloadArgNotStringLiteral func.loc
            s!"Overloaded function '{func.name}': first argument \
              type '{firstArgType}' is not a \
              string literal (only string literal dispatch is \
              currently supported)"
          return
  let retType ←
        match func.returnType.asIdent with
        | some nm => pure nm
        | none =>
          reportError .overloadReturnNotClass func.loc
            s!"Overloaded function '{func.name}': return type \
              '{func.returnType}' is not a \
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

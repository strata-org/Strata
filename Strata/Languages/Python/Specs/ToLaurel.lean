/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
import Strata.Languages.Python.OverloadTable
public import Strata.Languages.Python.Specs.Decls
public import Strata.Languages.Python.Specs.Error
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

namespace Strata.Python.Specs.ToLaurel

open Strata.Laurel
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
def reportError (loc : SourceRange) (message : String) : ToLaurelM Unit := do
  let e : SpecError := ⟨(←read).filepath, loc, message⟩
  modify fun s => { s with errors := s.errors.push e }

/-- Add a Laurel procedure to the output. -/
def pushProcedure (proc : Procedure) : ToLaurelM Unit :=
  modify fun s => { s with procedures := s.procedures.push proc }

/-- Add a Laurel type definition to the output. -/
def pushType (td : TypeDefinition) : ToLaurelM Unit :=
  modify fun s => { s with types := s.types.push td }

/-- Add an overload dispatch entry for a function. -/
def pushOverloadEntry (funcName : String) (literalValue : String)
    (returnType : PythonIdent) : ToLaurelM Unit :=
  modify fun s =>
    let existing := s.overloads.getD funcName {}
    let updated := existing.insert literalValue returnType
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
  { val := ty, md := default }

/-- Create a TCore wrapped type with default metadata. -/
private def mkCore (s : String) : HighTypeMd :=
  { val := .TCore s, md := default }

/-- Placeholder for types not yet supported in CorePrelude.
    Returns TString so translation can proceed. Callers should
    report a warning via `reportError` so the gap is visible. -/
private def unsupportedType : HighTypeMd :=
  { val := .TString, md := default }

mutual

/-- Convert a SpecAtomType to a string for error messages. -/
partial def atomTypeToString (a : SpecAtomType) : String :=
  match a with
  | .ident nm args =>
    if nm == PythonIdent.noneType && args.isEmpty then "None"
    else if args.isEmpty then toString nm
    else
      let argStrs := args.map specTypeToString
      s!"{nm}[{String.intercalate ", " argStrs.toList}]"
  | .pyClass name args =>
    if args.isEmpty then name
    else
      let argStrs := args.map specTypeToString
      s!"{name}[{String.intercalate ", " argStrs.toList}]"
  | .intLiteral v => s!"Literal[{v}]"
  | .stringLiteral v => s!"Literal[\"{v}\"]"
  | .typedDict _ _ _ => "TypedDict"

/-- Convert a SpecType to a string for error messages. -/
partial def specTypeToString (t : SpecType) : String :=
  if t.atoms.size == 1 then
    atomTypeToString t.atoms[0]!
  else
    let strs := t.atoms.map atomTypeToString
    String.intercalate " | " strs.toList

end

/-- Pretty print a union type. -/
def formatUnionType (atoms : Array SpecAtomType) : String :=
  let strs := atoms.map atomTypeToString
  String.intercalate " | " strs.toList

/-! ## Type Translation -/

/--
Detect if a SpecType is a Union[None, T] pattern and return the appropriate Laurel type.
Handles:
- Union[None, str] → TCore "StrOrNone"
- Union[None, int] → TCore "IntOrNone"
- Union[None, bool] → TCore "BoolOrNone"
- Union[None, Literal["A"], ...] → TCore "StrOrNone"
- Union[None, Literal[1], ...] → TCore "IntOrNone"
- Union[None, TypedDict] → TCore "DictStrAny"
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
    return some (mkCore "StrOrNone")

  -- All non-None int literals → IntOrNone
  if otherAtoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
    return some (mkCore "IntOrNone")

  -- All non-None TypedDicts → DictStrAny
  if otherAtoms.all (fun a => match a with | .typedDict _ _ _ => true | _ => false) then
    return some (mkCore "DictStrAny")

  if otherAtoms.size == 1 then
    match otherAtoms[0]! with
    | .ident nm _ =>
      if nm == PythonIdent.builtinsStr then return some (mkCore "StrOrNone")
      else if nm == PythonIdent.builtinsInt then return some (mkCore "IntOrNone")
      else if nm == PythonIdent.builtinsBool then return some (mkCore "BoolOrNone")
      -- TODO: add CorePrelude types for these Optional patterns
      else if nm == PythonIdent.builtinsFloat then
        return some unsupportedType
      else if nm == PythonIdent.typingList then
        return some unsupportedType
      else if nm == PythonIdent.typingDict then
        return some unsupportedType
      else if nm == PythonIdent.typingAny then
        return some unsupportedType
      else if nm == PythonIdent.builtinsBytes then
        return some unsupportedType
      else return none
    | .typedDict _ _ _ => return some (mkCore "DictStrAny")
    | .intLiteral _ => return some (mkCore "IntOrNone")
    | _ => return none
  else
    return none

/-- Convert a SpecType to a Laurel HighTypeMd. -/
def specTypeToLaurelType (ty : SpecType) : ToLaurelM HighTypeMd := do
  match ty.atoms.size with
  | 0 =>
    reportError default "Empty type (no atoms) encountered in Laurel conversion"
    return mkTy .TString
  | _ =>
    -- Check for union types
    if ty.atoms.size > 1 then
      -- All string literals → TString
      if ty.atoms.all (fun a => match a with | .stringLiteral _ => true | _ => false) then
        return mkTy .TString
      -- All int literals → TInt
      if ty.atoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
        return mkTy .TInt
      -- All TypedDicts → DictStrAny
      if ty.atoms.all (fun a => match a with | .typedDict _ _ _ => true | _ => false) then
        return mkCore "DictStrAny"
      -- Check Union[None, T] patterns
      match ← detectOptionalType ty with
      | some laurelType => return laurelType
      | none =>
        let unionStr := formatUnionType ty.atoms
        reportError default s!"Union type ({unionStr}) not yet supported in Laurel"
        return mkTy .TString
    else
      pure ()
    -- Single atom type
    match ty.atoms[0]! with
    | .ident nm args =>
      if nm == PythonIdent.builtinsInt then return mkTy .TInt
      if nm == PythonIdent.builtinsBool then return mkTy .TBool
      if nm == PythonIdent.builtinsStr then return mkTy .TString
      if nm == PythonIdent.builtinsFloat then return mkTy .TReal
      if nm == PythonIdent.noneType then return mkTy .TVoid
      -- TODO: add proper CorePrelude types for these
      if nm == PythonIdent.typingAny then return unsupportedType
      if nm == PythonIdent.typingList then return mkCore "ListStr"
      if nm == PythonIdent.typingDict then return mkCore "DictStrAny"
      if nm == PythonIdent.builtinsBytes then return unsupportedType
      if args.size > 0 then
        reportError default
          s!"Generic type '{nm}' with type args unsupported"
      reportError default s!"Unknown type '{nm}' mapped to TString"
      return mkTy .TString
    | .pyClass name args =>
      if args.size > 0 then
        reportError default
          s!"Generic class '{name}' with type args unsupported"
      let prefixed ← prefixName name
      return mkTy (.UserDefined { text := prefixed })
    | .intLiteral _ => return mkTy .TInt
    | .stringLiteral _ => return mkTy .TString
    | .typedDict _ _ _ => return mkCore "DictStrAny"

/-! ## SpecExpr to Laurel Translation -/

/-- Wrap a StmtExpr with metadata. -/
private def mkStmt (e : StmtExpr) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  { val := e, md := md }

/-- Create file-level metadata from the current pyspec filepath.
    Uses a default (zero) source range; callers with a specific location
    should use `mkMdWithFileRange` instead. -/
private def mkFileMd : ToLaurelM (Imperative.MetaData Core.Expression) := do
  let ctx ← read
  let fr : FileRange := { file := .file ctx.filepath.toString, range := default }
  return #[⟨Imperative.MetaData.fileRange, .fileRange fr⟩]

/-- Create metadata with a file range from the current pyspec file. -/
private def mkMdWithFileRange (loc : SourceRange) (msg : String := "")
    : ToLaurelM (Imperative.MetaData Core.Expression) := do
  let ctx ← read
  let fr : FileRange := { file := .file ctx.filepath.toString, range := loc }
  let mut md : Imperative.MetaData Core.Expression := #[⟨Imperative.MetaData.fileRange, .fileRange fr⟩]
  if !msg.isEmpty then
    md := md.push ⟨Imperative.MetaData.message, .msg msg⟩
  return md

/-- Wrap a StmtExpr with metadata containing a file range and optional message. -/
private def mkStmtWithLoc (e : StmtExpr) (loc : SourceRange) (msg : String := "")
    : ToLaurelM StmtExprMd := do
  let md ← mkMdWithFileRange loc msg
  return { val := e, md := md }

/-- Translate a SpecExpr to a Laurel StmtExpr.
    All values are assumed to be Any-typed (the Python prelude's universal type).
    Returns `none` for unsupported expressions (placeholders).
    Uses Core prelude function names (Any_len, DictStrAny_contains, etc.)
    which are resolved after the Core prelude is prepended. -/
partial def specExprToLaurel (e : SpecExpr) (md : Imperative.MetaData Core.Expression)
  : ToLaurelM (Option StmtExprMd) :=
  match e with
  | .placeholder => do
    reportError default "Placeholder expression not translatable"
    return none
  | .var name => return some (mkStmt (.Identifier (mkId name)) md)
  | .intLit v => return some (mkStmt (.StaticCall (mkId "from_int")
      [mkStmt (.LiteralInt v) md]) md)
  | .floatLit _ => do
    reportError default "Float literals not yet supported in preconditions"
    return none
  | .getIndex subject field =>
    match subject with
    | .var "kwargs" => return some (mkStmt (.Identifier (mkId field)) md)
    | _ => do
      let s? ← specExprToLaurel subject md
      return s?.map fun s => mkStmt (.FieldSelect s (mkId field)) md
  | .isInstanceOf _ typeName => do
    reportError default s!"isinstance check for '{typeName}' not yet supported in preconditions"
    return none
  | .len subject => do
    -- len(x) where x is Any: Str.Length(Any..as_string!(x)) wrapped as from_int
    let s? ← specExprToLaurel subject md
    return s?.map fun s =>
      let unwrapped := mkStmt (.StaticCall (mkId "Any..as_string!") [s]) md
      mkStmt (.StaticCall (mkId "from_int")
        [mkStmt (.StaticCall (mkId "Str.Length") [unwrapped]) md]) md
  | .intGe subject bound => do
    let s? ← specExprToLaurel subject md; let b? ← specExprToLaurel bound md
    return do
      let s ← s?; let b ← b?
      some (mkStmt (.PrimitiveOp .Geq
        [mkStmt (.StaticCall (mkId "Any..as_int!") [s]) md,
         mkStmt (.StaticCall (mkId "Any..as_int!") [b]) md]) md)
  | .intLe subject bound => do
    let s? ← specExprToLaurel subject md; let b? ← specExprToLaurel bound md
    return do
      let s ← s?; let b ← b?
      some (mkStmt (.PrimitiveOp .Leq
        [mkStmt (.StaticCall (mkId "Any..as_int!") [s]) md,
         mkStmt (.StaticCall (mkId "Any..as_int!") [b]) md]) md)
  | .floatGe subject bound => do
    let s? ← specExprToLaurel subject md; let b? ← specExprToLaurel bound md
    return do
      let s ← s?; let b ← b?
      let sF := mkStmt (.StaticCall (mkId "Any..as_float!") [s]) md
      let bF := mkStmt (.StaticCall (mkId "Any..as_float!") [b]) md
      some (mkStmt (.PrimitiveOp .Geq [sF, bF]) md)
  | .floatLe subject bound => do
    let s? ← specExprToLaurel subject md; let b? ← specExprToLaurel bound md
    return do
      let s ← s?; let b ← b?
      let sF := mkStmt (.StaticCall (mkId "Any..as_float!") [s]) md
      let bF := mkStmt (.StaticCall (mkId "Any..as_float!") [b]) md
      some (mkStmt (.PrimitiveOp .Leq [sF, bF]) md)
  | .not inner => do
    let i? ← specExprToLaurel inner md
    return i?.map fun i => mkStmt (.PrimitiveOp .Not [i]) md
  | .implies cond body => do
    let c? ← specExprToLaurel cond md; let b? ← specExprToLaurel body md
    return do let c ← c?; let b ← b?; some (mkStmt (.PrimitiveOp .Implies [c, b]) md)
  | .enumMember subject values => do
    let s? ← specExprToLaurel subject md
    return s?.map fun s =>
      let sStr := mkStmt (.StaticCall (mkId "Any..as_string!") [s]) md
      let eqs := values.toList.map fun v =>
        mkStmt (.PrimitiveOp .Eq [sStr, mkStmt (.LiteralString v) md]) md
      eqs.foldl (init := mkStmt (.LiteralBool false) md) fun acc eq =>
        mkStmt (.PrimitiveOp .Or [acc, eq]) md
  | .containsKey container key => do
    match container with
    | .var "kwargs" =>
      -- containsKey(kwargs, "key") → parameter was provided (not None)
      return some (mkStmt (.PrimitiveOp .Not
        [mkStmt (.StaticCall (mkId "Any..isfrom_none") [mkStmt (.Identifier (mkId key)) md]) md])
        md)
    | _ =>
      let c? ← specExprToLaurel container md
      return c?.map fun c =>
        let unwrapped := mkStmt (.StaticCall (mkId "Any..as_Dict!") [c]) md
        mkStmt (.StaticCall (mkId "DictStrAny_contains")
          [unwrapped, mkStmt (.LiteralString key) md]) md
  | .regexMatch subject pattern => do
    let s? ← specExprToLaurel subject md
    return s?.map fun s =>
      let sStr := mkStmt (.StaticCall (mkId "Any..as_string!") [s]) md
      mkStmt (.StaticCall (mkId "re_search_bool") [mkStmt (.LiteralString pattern) md, sStr]) md
  | .forallList _ _ _ => do
    reportError default "forallList quantifier not yet supported in preconditions"
    return none
  | .forallDict _ _ _ _ => do
    reportError default "forallDict quantifier not yet supported in preconditions"
    return none

private def formatAssertionMessage (msg : Array MessagePart) : String :=
  let parts := msg.map fun
    | .str s => s
    | .expr _ => "<expr>"
  String.join parts.toList

/-- Build a procedure body that asserts preconditions.
    Outputs are already initialized non-deterministically. -/
def buildSpecBody (preconditions : Array Assertion)
    (md : Imperative.MetaData Core.Expression)
    (requiredParams : Array String := #[])
    : ToLaurelM Body := do
  let fileMd ← mkFileMd
  let mut stmts : List StmtExprMd := []
  -- Assert that required parameters are provided (not None)
  for param in requiredParams do
    let cond := mkStmt (.PrimitiveOp .Not
      [mkStmt (.StaticCall (mkId "Any..isfrom_none")
        [mkStmt (.Identifier (mkId param)) md]) md]) md
    let assertStmt ← mkStmtWithLoc (.Assert cond) default s!"Required parameter '{param}' is missing"
    stmts := assertStmt :: stmts
  for assertion in preconditions do
    let msg := formatAssertionMessage assertion.message
    match ← specExprToLaurel assertion.formula md with
    | some condExpr =>
      let assertStmt ← mkStmtWithLoc (.Assert condExpr) default msg
      stmts := assertStmt :: stmts
    | none =>
      reportError default s!"Untranslatable precondition (emitting nondeterministic assert): {msg}"
      let assertStmt ← mkStmtWithLoc (.Assert (mkStmt .Hole md)) default msg
      stmts := assertStmt :: stmts
  let body := mkStmt (.Block stmts.reverse none) fileMd
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
    reportError default
      s!"Method '{func.name}' has no arguments (expected 'self' as first parameter)"
  let posArgs := if isMethod then func.args.args.extract 1 func.args.args.size
                 else func.args.args
  let kwargsArgs ← match expandKwargsArgs func.args.kwargs with
    | .ok args => pure args
    | .error msg => do reportError default msg; pure #[]
  let allArgs := posArgs ++ func.args.kwonly ++ kwargsArgs
  let inputs ← allArgs.mapM argToParameter
  let retType ← specTypeToLaurelType func.returnType
  let outputs : List Parameter :=
    [{ name := "result", type := match retType.val with
      | .TVoid => mkCore "Any"
      | _ => retType }]
  if func.postconditions.size > 0 then
    reportError func.loc "Postconditions not yet supported"
  -- When preconditions exist, use TCore "Any" for all parameters and outputs
  -- to match the Python→Laurel pipeline's Any-wrapping convention.
  let (inputs, outputs, body) ←
    if func.preconditions.size > 0 then do
      let anyTy : HighTypeMd := mkCore "Any"
      let anyInputs := inputs.map fun p => { p with type := anyTy }
      let anyOutputs := outputs.map fun p => { p with type := anyTy }
      let body ← buildSpecBody func.preconditions .empty
        (requiredParams := allArgs.filterMap fun a =>
          if a.default.isNone then some a.name else none)
      pure (anyInputs, anyOutputs, body)
    else
      pure (inputs, outputs, Body.Opaque [] none [])
  let md ← mkMdWithFileRange func.loc
  return {
    name := procName
    inputs := inputs.toList
    outputs := outputs
    preconditions := []
    determinism := .nondeterministic
    decreases := none
    isFunctional := false
    body := body
    md := md
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
    Looks for a `stringLiteral` in the first argument's type and a class
    return type (either `.pyClass` for locally-defined classes or `.ident`
    for externally imported classes), and records them in the dispatch table. -/
def extractOverloadEntry (func : FunctionDecl) : ToLaurelM Unit := do
  let args := func.args.args
  let .isTrue _ := decideProp (args.size > 0)
    | reportError func.loc
        s!"Overloaded function '{func.name}' has no arguments"
      return
  let firstArgType := args[0].type
  let .isTrue _ := decideProp (firstArgType.atoms.size = 1)
    | reportError func.loc
        s!"Overloaded function '{func.name}': first argument \
          has {firstArgType.atoms.size} type atoms, expected 1"
      return
  let literalValue ←
        match firstArgType.atoms[0] with
        | .stringLiteral v => pure v
        | _ =>
          reportError func.loc
            s!"Overloaded function '{func.name}': first argument \
              type '{specTypeToString firstArgType}' is not a \
              string literal (only string literal dispatch is \
              currently supported)"
          return
  let .isTrue _ := decideProp (func.returnType.atoms.size = 1)
    | reportError func.loc
        s!"Overloaded function '{func.name}': return type \
        has {func.returnType.atoms.size} type atoms, expected 1"
      return
  let retType ←
        match func.returnType.atoms[0] with
        | .pyClass name _ => do
          let ctx ← read
          let prefixed ← prefixName name
          pure (PythonIdent.mk ctx.modulePrefix prefixed)
        | .ident nm _ => pure nm
        | _ =>
          reportError func.loc
            s!"Overloaded function '{func.name}': return type \
              '{specTypeToString func.returnType}' is not a \
              class type"
          return
  pushOverloadEntry func.name literalValue retType

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

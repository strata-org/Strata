/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Python.Specs.Decls
import Strata.Languages.Python.Specs.PySpecM
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

/-! ## Overload Dispatch Table -/

/--
All overloads for a single function name: maps a string literal
argument value to the return type (`PythonIdent`).

N.B. Current limitations: dispatch is always on the first positional argument,
and only string literal values are extracted. -/
abbrev FunctionOverloads := Std.HashMap String PythonIdent

/-- Dispatch table: function name → its overloads. -/
abbrev OverloadTable := Std.HashMap String FunctionOverloads

/-! ## ToLaurelM Monad -/

/-- Context for PySpec to Laurel translation. -/
structure ToLaurelContext where
  filepath : System.FilePath

/-- State for PySpec to Laurel translation. -/
structure ToLaurelState where
  errors : Array SpecError := #[]
  procedures : Array Procedure := #[]
  types : Array TypeDefinition := #[]
  overloads : OverloadTable := {}

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
      if nm == PythonIdent.builtinsFloat then return mkTy .TFloat64
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
      return mkTy (.UserDefined name)
    | .intLiteral _ => return mkTy .TInt
    | .stringLiteral _ => return mkTy .TString
    | .typedDict _ _ _ => return mkCore "DictStrAny"

/-! ## Declaration Translation -/

/-- Convert an Arg to a Laurel Parameter. -/
def argToParameter (arg : Arg) : ToLaurelM Parameter := do
  let ty ← specTypeToLaurelType arg.type
  return { name := arg.name, type := ty }

/-- Convert a function declaration to a Laurel Procedure. -/
def funcDeclToLaurel (procName : String) (func : FunctionDecl)
    : ToLaurelM Procedure := do
  let allArgs := func.args.args ++ func.args.kwonly
  let inputs ← allArgs.mapM argToParameter
  let retType ← specTypeToLaurelType func.returnType
  let outputs : List Parameter :=
    match retType.val with
    | .TVoid => []
    | _ => [{ name := "result", type := retType }]
  if func.preconditions.size > 0 || func.postconditions.size > 0 then
    reportError func.loc "Preconditions/postconditions not yet supported"
  return {
    name := procName
    inputs := inputs.toList
    outputs := outputs
    precondition := ⟨.LiteralBool true, .empty⟩
    determinism := .nondeterministic
    decreases := none
    body := .Opaque [] none []
    md := .empty
  }

/-- Convert a class definition to Laurel types and procedures. -/
def classDefToLaurel (cls : ClassDef) : ToLaurelM Unit := do
  pushType (.Composite {
    name := cls.name
    extending := []
    fields := []
    instanceProcedures := []
  })
  for method in cls.methods do
    let proc ← funcDeclToLaurel (cls.name ++ "_" ++ method.name) method
    pushProcedure proc

/-- Convert a type definition to a Laurel composite type placeholder. -/
def typeDefToLaurel (td : TypeDef) : ToLaurelM Unit :=
  pushType (.Composite {
    name := td.name
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
        | .pyClass name _ => pure (PythonIdent.mk "" name)
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
    else
      let proc ← funcDeclToLaurel func.name func
      pushProcedure proc
  | .classDef cls => classDefToLaurel cls

/-- Result of translating PySpec signatures to Laurel. -/
structure TranslationResult where
  program : Laurel.Program
  errors : Array SpecError
  overloads : OverloadTable

/-- Run the translation and return a Laurel Program, dispatch table,
    and any errors. -/
def signaturesToLaurel (filepath : System.FilePath) (sigs : Array Signature)
    : TranslationResult :=
  let ctx : ToLaurelContext := { filepath }
  let ((), state) := (sigs.forM signatureToLaurel).run ctx |>.run {}
  let pgm : Laurel.Program := {
    staticProcedures := state.procedures.toList
    staticFields := []
    types := state.types.toList
    constants := []
  }
  { program := pgm
    errors := state.errors
    overloads := state.overloads }

/-- Extract only the overload dispatch table from PySpec signatures.
    Processes `@overload` function declarations, ignoring classDef,
    typeDef, externTypeDecl, and non-overload functions. -/
def extractOverloads (filepath : System.FilePath) (sigs : Array Signature)
    : OverloadTable × Array SpecError :=
  let ctx : ToLaurelContext := { filepath }
  let action := sigs.forM fun sig =>
    match sig with
    | .functionDecl func =>
      if func.isOverload then extractOverloadEntry func
      else pure ()
    | _ => pure ()
  let ((), state) := action.run ctx |>.run {}
  (state.overloads, state.errors)

end Strata.Python.Specs.ToLaurel

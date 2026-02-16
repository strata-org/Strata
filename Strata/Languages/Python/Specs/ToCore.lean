/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.CorePrelude
import Strata.Languages.Python.Specs.Decls
import Strata.Languages.Python.Specs.PySpecM

/-!
# PySpec to StrataCore Translation

This module provides translation from PySpec signatures to StrataCore declarations.

PySpec files contain type signatures extracted from Python code. This translator
converts those signatures into StrataCore programs that can be verified.

## Translation Strategy

- `externTypeDecl`: External types become opaque type declarations in Core
- `typeDef`: Type aliases become type declarations in Core
- `functionDecl`: Functions become Core procedures with preconditions/postconditions
- `classDef`: Classes become a type declaration plus methods as procedures
-/

namespace Strata.Python.Specs.ToCore


/-! ## ToCoreM Monad -/

/-- Context for PySpec to Core translation, containing indices of types from CorePrelude. -/
structure ToCoreContext where
  filepath : System.FilePath
  dictStrAnyIndex : Nat
  strOrNoneIndex : Nat
  intOrNoneIndex : Nat
  boolOrNoneIndex : Nat

/-- State for PySpec to Core translation, tracking errors and accumulated commands. -/
structure ToCoreState where
  errors : Array SpecError := #[]
  commands : Array (Strata.CoreDDM.Command SourceRange) := #[]
  classTypeIndices : Std.HashMap String Nat := {}
  nextTypeIndex : Nat  -- Next available type index for new type declarations

/-- Monad for PySpec to Core translation with error tracking and context. -/
abbrev ToCoreM := ReaderT ToCoreContext (StateM ToCoreState)

/-- Report an error during translation. -/
def toCoreError (loc : SourceRange) (message : String) : ToCoreM Unit := do
  let e : SpecError := ⟨(←read).filepath, loc, message⟩
  modify fun s => { s with errors := s.errors.push e }

/-- Add a Core DDM command to the output. -/
def pushCommand (cmd : Strata.CoreDDM.Command SourceRange) : ToCoreM Unit :=
  modify fun s => { s with commands := s.commands.push cmd }

/-- Register a class type with the next available index. Returns the assigned index. -/
def registerClassType (className : String) : ToCoreM Nat := do
  let state ← get
  let idx := state.nextTypeIndex
  modify fun s => {
    s with
      classTypeIndices := s.classTypeIndices.insert className idx
      nextTypeIndex := s.nextTypeIndex + 1
  }
  return idx

instance : PySpecMClass ToCoreM where
  specError loc message := toCoreError loc message
  runChecked act := do
    let cnt := (←get).errors.size
    let r ← act
    let new_cnt := (←get).errors.size
    return (cnt = new_cnt, r)

/-! ## Helper Functions -/

mutual

/-- Convert a SpecType to a string for display in error messages. -/
partial def specTypeToString (t : SpecType) : String :=
  if t.atoms.size == 1 then
    atomTypeToString t.atoms[0]!
  else
    let strs := t.atoms.map atomTypeToString
    String.intercalate " | " strs.toList

/-- Convert a SpecAtomType to a string for display in error messages. -/
partial def atomTypeToString (a : SpecAtomType) : String :=
  match a with
  | .ident nm args =>
    -- Special case: _types.NoneType should display as "None"
    if nm == PythonIdent.noneType && args.isEmpty then
      "None"
    else if args.isEmpty then
      toString nm
    else
      let argStrs := args.map specTypeToString
      s!"{nm}[{String.intercalate ", " argStrs.toList}]"
  | .pyClass name args =>
    if args.isEmpty then
      name
    else
      let argStrs := args.map specTypeToString
      s!"{name}[{String.intercalate ", " argStrs.toList}]"
  | .intLiteral v => s!"Literal[{v}]"
  | .stringLiteral v => s!"Literal[\"{v}\"]"
  | .typedDict _ _ _ => "TypedDict"

end

/-- Pretty print a union type as "type1 | type2 | type3". -/
def formatUnionType (atoms : Array SpecAtomType) : String :=
  let strs := atoms.map atomTypeToString
  let uniqueStrs := strs.toList.eraseDups
  let result := String.intercalate " | " uniqueStrs
  -- Add note if there were duplicates
  if uniqueStrs.length < strs.size then
    s!"{result} (deduplicated from {strs.size} to {uniqueStrs.length} types)"
  else
    result

/-! ## Declaration Translation -/

/-- Helper: Create an Ann wrapping a value with default source range. -/
def mkAnn {α : Type} (val : α) : Ann α SourceRange :=
  { ann := default, val := val }

/-- Helper: Create an Ann wrapping an Option value with default source range. -/
def mkOptAnn {α : Type} (val : Option α) : Ann (Option α) SourceRange :=
  { ann := default, val := val }

/-- Look up a type name in the CorePrelude global context and return its index. -/
def lookupCorePreludeType (name : String) : Option Nat :=
  Python.corePrelude.globalContext.findIndex? name

/--
Detect if a SpecType is a Union[None, T] pattern and return the appropriate Core type.
Handles:
- Union[None, str] → StrOrNone
- Union[None, int] → IntOrNone
- Union[None, bool] → BoolOrNone
- Union[None, float] → string
- Union[None, Literal["A"], Literal["B"], ...] → StrOrNone
- Union[None, Literal[1], Literal[2], ...] → IntOrNone
- Union[None, List[T]] → string
- Union[None, Dict[K,V]] → string
- Union[None, Any] → string
- Union[None, bytes] → string
- Union[None, TypedDict] → DictStrAny
-/
def detectOptionalType (ty : SpecType) : ToCoreM (Option (CoreDDM.CoreType SourceRange)) := do
  -- Helper: check if an atom is NoneType
  let isNoneType (atom : SpecAtomType) : Bool :=
    match atom with
    | .ident nm args => nm == PythonIdent.noneType && args.isEmpty
    | _ => false

  -- Must have at least one NoneType atom
  if !ty.atoms.any isNoneType then
    return none

  let otherAtoms := ty.atoms.filter (fun a => !isNoneType a)

  let ctx ← read

  -- If all non-None atoms are string literals → StrOrNone
  if otherAtoms.all (fun a => match a with | .stringLiteral _ => true | _ => false) then
    return some (.fvar ty.loc ctx.strOrNoneIndex #[])

  -- If all non-None atoms are int literals → IntOrNone
  if otherAtoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
    return some (.fvar ty.loc ctx.intOrNoneIndex #[])

  -- If exactly one non-None atom, match on its type
  if otherAtoms.size == 1 then
    match otherAtoms[0]! with
    | .ident nm _ =>
      if nm == PythonIdent.builtinsStr then
        return some (.fvar ty.loc ctx.strOrNoneIndex #[])
      else if nm == PythonIdent.builtinsInt then
        return some (.fvar ty.loc ctx.intOrNoneIndex #[])
      else if nm == PythonIdent.builtinsBool then
        return some (.fvar ty.loc ctx.boolOrNoneIndex #[])
      else if nm == PythonIdent.typingList then
        return some (.string ty.loc)
      else if nm == PythonIdent.typingDict then
        return some (.string ty.loc)
      else if nm == PythonIdent.typingAny then
        return some (.string ty.loc)
      else if nm == PythonIdent.builtinsBytes then
        return some (.string ty.loc)
      else if nm == PythonIdent.builtinsFloat then
        -- FIXME: Should map to RealOrNone once we add that type to CorePrelude
        specError ty.loc "Union[None, float] mapped to string - needs RealOrNone type"
        return some (.string ty.loc)
      else
        return none
    | .typedDict _ _ _ =>
      return some (.fvar default ctx.dictStrAnyIndex #[])
    | .intLiteral _ =>
      return some (.fvar ty.loc ctx.intOrNoneIndex #[])
    | _ => return none
  else
    return none

/-- Helper: Convert SpecType to CoreDDM.CoreType, reporting errors for unsupported features. -/
def specTypeToCoreType (ty : SpecType) : ToCoreM (CoreDDM.CoreType SourceRange) := do
  match ty.atoms.size with
  | 0 =>
    specError ty.loc "Empty type (no atoms) encountered in CoreDDM conversion"
    return .string ty.loc
  | _ =>
    -- Check for union types
    if ty.atoms.size > 1 then
      -- Check if all atoms are string literals (Literal["A"] | Literal["B"] | ...)
      if ty.atoms.all (fun a => match a with | .stringLiteral _ => true | _ => false) then
        return .string ty.loc
      -- Check if all atoms are int literals (Literal[1] | Literal[2] | ...)
      if ty.atoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
        return .int ty.loc
      -- Check if this is a Union[None, T] pattern we support
      match ← detectOptionalType ty with
      | some coreType =>
        return coreType
      | none =>
        -- Not a supported optional type pattern, report error and return immediately
        let atomsDebug := ty.atoms.map atomTypeToString
        let unionStr := formatUnionType ty.atoms
        specError ty.loc s!"Union type ({unionStr}) not yet supported in CoreDDM [atoms: {atomsDebug}]"
        return .string ty.loc
    else
      pure ()
    -- Take the first atom and convert it
    match ty.atoms[0]! with
    | .ident nm args =>
      -- Check type first, then decide if generic args are supported
      if nm == PythonIdent.builtinsInt then return .int ty.loc
      else if nm == PythonIdent.builtinsBool then return .bool ty.loc
      else if nm == PythonIdent.builtinsStr then return .string ty.loc
      else if nm == PythonIdent.builtinsFloat then return .real ty.loc
      else if nm == PythonIdent.typingAny then
        -- typing.Any maps to a generic polymorphic type - use string for now
        return .string ty.loc
      else if nm == PythonIdent.typingList then
        -- typing.List maps to array/sequence type - use string for now
        -- Generic args not yet supported, but don't report error for known types
        return .string ty.loc
      else if nm == PythonIdent.typingDict then
        -- typing.Dict maps to Map type
        -- Generic args not yet supported, but don't report error for known types
        return .string ty.loc
      else if nm == PythonIdent.builtinsBytes then
        -- bytes type - could map to ByteArray or similar
        return .string ty.loc
      else do
        -- Unknown type - report error for generic args if present
        if args.size > 0 then
          specError ty.loc s!"Generic type '{nm}' with type arguments not yet supported in CoreDDM"
        specError ty.loc s!"Unknown type '{nm}' mapped to string - should generate opaque type declaration"
        return .string ty.loc
    | .pyClass name args =>
      -- Check for generic class type arguments
      if args.size > 0 then
        specError ty.loc s!"Generic class '{name}' with type arguments not yet supported in CoreDDM"
      -- Look up class type in state
      let state ← get
      match state.classTypeIndices[name]? with
      | some idx => return .fvar ty.loc idx #[]  -- Found - use the class type
      | none =>
        -- Not found - fall back to string with warning
        specError ty.loc s!"Class type '{name}' not found - mapped to string"
        return .string ty.loc
    | .intLiteral _ => return .int ty.loc
    | .stringLiteral _ => return .string ty.loc
    | .typedDict _ _ _ =>
      -- TypedDict maps to DictStrAny (from Core prelude)
      return .fvar default (←read).dictStrAnyIndex #[]  -- No type arguments

/-- Convert a type definition to a Core DDM command. -/
def typeDeclToCommand (typeDef : TypeDef) : ToCoreM (CoreDDM.Command SourceRange) := do
  let coreType ← specTypeToCoreType typeDef.definition
  return .command_typesynonym
    typeDef.loc                     -- annotation (use location from TypeDef)
    (mkAnn typeDef.name)            -- type name
    (mkOptAnn none)                 -- bindings (none for simple types)
    (mkOptAnn none)                 -- type args (none for simple types)
    coreType                        -- the type definition

/-- Convert an Arg to a CoreDDM.Binding. -/
def argToBinding (arg : Arg) : ToCoreM (CoreDDM.Binding SourceRange) := do
  let coreType ← specTypeToCoreType arg.type
  let typeP : CoreDDM.TypeP SourceRange := .expr coreType
  return .mkBinding default (mkAnn arg.name) typeP

/-- Convert ArgDecls to CoreDDM.Bindings. -/
def argDeclsToBindings (args : ArgDecls) : ToCoreM (CoreDDM.Bindings SourceRange) := do
  -- Combine regular args and keyword-only args
  let allArgs := args.args ++ args.kwonly
  let bindings ← allArgs.mapM argToBinding
  return .mkBindings default (mkAnn bindings)

/-- Convert a SpecType to a MonoBind for return types. -/
def specTypeToMonoBind (name : String) (ty : SpecType) : ToCoreM (CoreDDM.MonoBind SourceRange) := do
  let coreType ← specTypeToCoreType ty
  return .mono_bind_mk default (mkAnn name) coreType

/-- Build a MonoDeclList from an array of MonoBind. -/
def monoDeclListFromArray (binds : Array (CoreDDM.MonoBind SourceRange)) : Option (CoreDDM.MonoDeclList SourceRange) :=
  match binds.size with
  | 0 => none
  | 1 => some (.monoDeclAtom default binds[0]!)
  | _ =>
    -- Build the list by folding
    let first := binds[0]!
    let rest := binds.extract 1 binds.size
    some (rest.foldl (fun acc b => .monoDeclPush default acc b) (.monoDeclAtom default first))

/-- Convert a function declaration to a Core DDM procedure command with the given name. -/
def funcDeclToCommand (procName : String) (func : FunctionDecl)
    : ToCoreM (CoreDDM.Command SourceRange) := do
  let paramBindings ← argDeclsToBindings func.args
  let returnMonoBind ← specTypeToMonoBind "return" func.returnType
  let returnMonoDecl := monoDeclListFromArray #[returnMonoBind]
  if func.preconditions.size > 0 || func.postconditions.size > 0 then
    specError func.loc "Preconditions/postconditions not yet supported"
  return .command_procedure
    func.loc
    (mkAnn procName)
    (mkOptAnn none)           -- type parameters
    paramBindings
    (mkOptAnn returnMonoDecl)
    (mkOptAnn none)           -- spec
    (mkOptAnn none)           -- body (abstract procedure)

/-- Convert a class definition to Core DDM commands by pushing to state. -/
def classDefToCore (cls : ClassDef) : ToCoreM Unit := do
  -- Create an opaque type for the class
  let typeCmd : CoreDDM.Command SourceRange :=
    .command_typedecl
      cls.loc                  -- annotation (use location from ClassDef)
      (mkAnn cls.name)        -- class name
      (mkOptAnn none)         -- bindings (none for simple class)
  pushCommand typeCmd

  -- Register the class type so it can be referenced by other types
  let _ ← registerClassType cls.name

  -- Convert each method to a procedure command
  for method in cls.methods do
    let cmd ← funcDeclToCommand (cls.name ++ "_" ++ method.name) method
    pushCommand cmd

  return ()

/-- Convert a single PySpec signature to Core DDM commands by pushing to state. -/
def signatureToCore (sig : Signature) : ToCoreM Unit :=
  match sig with
  | .externTypeDecl name source =>
    -- External types are not supported - report error (no location available in Signature)
    specError default s!"External type declaration '{name}' from '{source}' is not yet supported"
  | .typeDef td => do
    -- Type definitions become type synonyms using command_typesynonym
    let cmd ← typeDeclToCommand td
    pushCommand cmd
  | .functionDecl func => do
    -- Functions become procedures using command_procedure
    let cmd ← funcDeclToCommand func.name func
    pushCommand cmd
  | .classDef cls =>
    -- Classes become a type (command_typedecl) plus methods as procedures (command_procedure)
    classDefToCore cls

/-- Run a ToCoreM computation with standard CorePrelude context.
    Returns the result and final state. -/
def runToCoreM (filepath : System.FilePath) (act : ToCoreM α) : α × ToCoreState :=
  let dictStrAnyIdx := match lookupCorePreludeType "DictStrAny" with
    | some idx => idx
    | none => panic! "DictStrAny type not found in CorePrelude"
  let strOrNoneIdx := match lookupCorePreludeType "StrOrNone" with
    | some idx => idx
    | none => panic! "StrOrNone type not found in CorePrelude"
  let intOrNoneIdx := match lookupCorePreludeType "IntOrNone" with
    | some idx => idx
    | none => panic! "IntOrNone type not found in CorePrelude"
  let boolOrNoneIdx := match lookupCorePreludeType "BoolOrNone" with
    | some idx => idx
    | none => panic! "BoolOrNone type not found in CorePrelude"
  let ctx : ToCoreContext := {
    filepath := filepath
    dictStrAnyIndex := dictStrAnyIdx
    strOrNoneIndex := strOrNoneIdx
    intOrNoneIndex := intOrNoneIdx
    boolOrNoneIndex := boolOrNoneIdx
  }
  let preludeTypeCount := Python.corePrelude.globalContext.vars.size
  let initialState : ToCoreState := {
    nextTypeIndex := preludeTypeCount
  }
  (act.run ctx).run initialState

def signaturesToCore (filepath : System.FilePath) (sigs : Array Signature) : Strata.Program × Array SpecError :=
  let ((), state) := runToCoreM filepath (sigs.forM signatureToCore)
  let allCommands := Python.corePrelude.commands ++ (state.commands.map fun c => c.toAst)
  let pgm : Strata.Program := {
    dialects := Strata.Core_map
    dialect := Strata.Core.name
    commands := allCommands
  }
  (pgm, state.errors)

end Strata.Python.Specs.ToCore

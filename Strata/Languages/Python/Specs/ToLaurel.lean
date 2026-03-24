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
      if nm == PythonIdent.typingList then
        -- Validate element type args: composites (UserDefined) cannot be embedded in Any
        for arg in args do
          match arg.atoms[0]? with
          | some (SpecAtomType.pyClass name _) =>
            reportError default
              s!"List[{name}] not supported: composites live on the heap and cannot be embedded in Any"
          | _ => pure ()
        return mkCore "ListAny"
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

/-! ## Declaration Translation -/

/-- Create a StmtExprMd wrapping a StmtExpr with empty metadata. -/
private def mkExpr (e : StmtExpr) : WithMetadata StmtExpr :=
  { val := e, md := default }

/-- Translate a PySpec parameter type directly to its Laurel type and constraints.
    Value-world types (primitives, dicts, lists) become `Core(Any)` with an
    `isfrom_X` precondition.  Heap-world types (user-defined classes) become
    `Composite` with no precondition.  Returns `(laurelType, preconditions)`.

    This function operates on `SpecType` atoms directly — it does NOT
    delegate to `specTypeToLaurelType`, avoiding the intermediate HighType
    that would be immediately discarded. -/
private def specTypeToLaurelActual (paramExpr : WithMetadata StmtExpr) (ty : SpecType)
    : ToLaurelM (HighTypeMd × Array (WithMetadata StmtExpr)) := do
  let anyTy : HighTypeMd := mkCore "Any"
  let compositeTy : HighTypeMd := ⟨.UserDefined "Composite", #[]⟩
  let mkCall (tester : String) := mkExpr (.StaticCall tester [paramExpr])
  let mkOr (a b : WithMetadata StmtExpr) := mkExpr (.PrimitiveOp .Or [a, b])

  let isNoneType (atom : SpecAtomType) : Bool :=
    match atom with
    | .ident nm args => nm == PythonIdent.noneType && args.isEmpty
    | _ => false

  -- Helper: translate a single non-None atom to its constraint.
  -- Returns `none` for unsupported/unrecognized types.
  let atomConstraint (atom : SpecAtomType) : ToLaurelM (Option (WithMetadata StmtExpr)) := do
    match atom with
    | .ident nm args =>
      if nm == PythonIdent.builtinsInt then return some (mkCall "Any..isfrom_int")
      if nm == PythonIdent.builtinsBool then return some (mkCall "Any..isfrom_bool")
      if nm == PythonIdent.builtinsStr then return some (mkCall "Any..isfrom_string")
      if nm == PythonIdent.builtinsFloat then return some (mkCall "Any..isfrom_float")
      if nm == PythonIdent.noneType then return none  -- no constraint
      if nm == PythonIdent.typingAny then return none  -- unconstrained
      if nm == PythonIdent.typingList then
        if args.isEmpty then
          reportError default
            "Bare List without element type not supported: element type may include composites incompatible with Any"
          return none
        -- Validate: reject composite element types
        for arg in args do
          match arg.atoms[0]? with
          | some (SpecAtomType.pyClass name _) =>
            reportError default
              s!"List[{name}] not supported: composites live on the heap and cannot be embedded in Any"
          | _ => pure ()
        return some (mkCall "Any..isfrom_ListAny")
      if nm == PythonIdent.typingDict then
        if args.isEmpty then
          reportError default
            "Bare Dict without type args not supported: value type may include composites incompatible with Any"
          return none
        return some (mkCall "Any..isfrom_Dict")
      if nm == PythonIdent.builtinsBytes then return none  -- unsupported
      reportError default s!"No Any precondition for ident type '{nm}'"
      return none
    | .pyClass .. => return none  -- composites handled at type level, not constraint
    | .intLiteral _ => return some (mkCall "Any..isfrom_int")
    | .stringLiteral _ => return some (mkCall "Any..isfrom_string")
    | .typedDict .. => return some (mkCall "Any..isfrom_Dict")

  -- Helper: translate a single atom to its (type, constraints).
  let atomToActual (atom : SpecAtomType) : ToLaurelM (HighTypeMd × Array (WithMetadata StmtExpr)) := do
    match atom with
    | .pyClass name args =>
      if args.size > 0 then
        reportError default s!"Generic class '{name}' with type args unsupported"
      return (compositeTy, #[])
    | other =>
      match ← atomConstraint other with
      | some c => return (anyTy, #[c])
      | none => return (anyTy, #[])

  -- Empty type
  if ty.atoms.size == 0 then
    reportError default "Empty type (no atoms) encountered"
    return (anyTy, #[])

  -- Single atom — most common case
  if ty.atoms.size == 1 then
    return ← atomToActual ty.atoms[0]!

  -- Multi-atom (union types) — all unions are value-world (Core(Any))

  -- Check for None in the union (Optional pattern)
  let hasNone := ty.atoms.any isNoneType
  let otherAtoms := ty.atoms.filter (fun a => !isNoneType a)

  -- All string literals → isfrom_string (+ isfrom_none if Optional)
  if otherAtoms.all (fun a => match a with | .stringLiteral _ => true | _ => false) then
    let strPre := mkCall "Any..isfrom_string"
    if hasNone then return (anyTy, #[mkOr (mkCall "Any..isfrom_none") strPre])
    return (anyTy, #[strPre])

  -- All int literals → isfrom_int (+ isfrom_none if Optional)
  if otherAtoms.all (fun a => match a with | .intLiteral _ => true | _ => false) then
    let intPre := mkCall "Any..isfrom_int"
    if hasNone then return (anyTy, #[mkOr (mkCall "Any..isfrom_none") intPre])
    return (anyTy, #[intPre])

  -- All TypedDicts → isfrom_Dict (+ isfrom_none if Optional)
  if otherAtoms.all (fun a => match a with | .typedDict .. => true | _ => false) then
    let dictPre := mkCall "Any..isfrom_Dict"
    if hasNone then return (anyTy, #[mkOr (mkCall "Any..isfrom_none") dictPre])
    return (anyTy, #[dictPre])

  -- Union[None, single-atom] — Optional patterns
  if hasNone && otherAtoms.size == 1 then
    -- Pure constraint lookup (no error reporting) for the non-None atom
    let optConstraint? : Option (WithMetadata StmtExpr) := match otherAtoms[0]! with
      | .ident nm args =>
        if nm == PythonIdent.builtinsStr then some (mkCall "Any..isfrom_string")
        else if nm == PythonIdent.builtinsInt then some (mkCall "Any..isfrom_int")
        else if nm == PythonIdent.builtinsBool then some (mkCall "Any..isfrom_bool")
        else if nm == PythonIdent.builtinsFloat then some (mkCall "Any..isfrom_float")
        else if nm == PythonIdent.typingList && !args.isEmpty then some (mkCall "Any..isfrom_ListAny")
        else if nm == PythonIdent.typingDict && !args.isEmpty then some (mkCall "Any..isfrom_Dict")
        else none
      | .intLiteral _ => some (mkCall "Any..isfrom_int")
      | .stringLiteral _ => some (mkCall "Any..isfrom_string")
      | .typedDict .. => some (mkCall "Any..isfrom_Dict")
      | _ => none
    if let some c := optConstraint? then
      return (anyTy, #[mkOr (mkCall "Any..isfrom_none") c])
    -- Known but unconstrained types (Any, bytes, noneType) — no error
    match otherAtoms[0]! with
    | .ident nm _ =>
      if nm == PythonIdent.typingAny || nm == PythonIdent.builtinsBytes
         || nm == PythonIdent.noneType then
        return (anyTy, #[])
    | _ => pure ()
    -- Unknown ident or pyClass in Optional — fall through to unrecognized union error
    pure ()

  -- Unrecognized union
  let unionStr := formatUnionType ty.atoms
  reportError default s!"Union type ({unionStr}) not yet supported"
  return (anyTy, #[])


/-- Map a HighType to the Any constructor name for wrapping typed → Any. -/
private def anyConstructorForType : HighType → Option String
  | .TString => some "from_string"
  | .TInt => some "from_int"
  | .TBool => some "from_bool"
  | .TCore "DictStrAny" => some "from_Dict"
  | .TCore "ListAny" => some "from_ListAny"
  | _ => none

/-- Map a HighType to the Any destructor name for unwrapping Any → typed. -/
private def anyDestructorForType : HighType → Option String
  | .TString => some "Any..as_string!"
  | .TInt => some "Any..as_int!"
  | .TBool => some "Any..as_bool!"
  | .TCore "DictStrAny" => some "Any..as_Dict!"
  | .TCore "ListAny" => some "Any..as_ListAny!"
  | _ => none

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
  let compositeTy : HighTypeMd := ⟨.UserDefined "Composite", #[]⟩
  let mut inputs : Array Parameter := .emptyWithCapacity (allArgs.size + if isMethod then 1 else 0)
  if isMethod then
    inputs := inputs.push { name := "self", type := compositeTy }
  let mut preconditions : Array (WithMetadata StmtExpr) := #[]
  for arg in allArgs do
    let paramExpr := mkExpr (.Identifier arg.name)
    let (laurelTy, constraints) ← specTypeToLaurelActual paramExpr arg.type
    inputs := inputs.push { name := arg.name, type := laurelTy }
    preconditions := preconditions ++ constraints
  -- Return type: check for void (NoneType) directly, otherwise use specTypeToLaurelActual
  let isVoidReturn := func.returnType.atoms.size == 1 &&
    match func.returnType.atoms[0]? with
    | some (SpecAtomType.ident nm #[]) => nm == PythonIdent.noneType
    | _ => false
  let (outputs, postconditions) ←
    if isVoidReturn then
      pure ([], #[])
    else do
      let resultExpr := mkExpr (.Identifier "result")
      let (retTy, retConstraints) ← specTypeToLaurelActual resultExpr func.returnType
      pure ([{ name := "result", type := retTy }], retConstraints)
  if func.preconditions.size > 0 || func.postconditions.size > 0 then
    reportError func.loc "Preconditions/postconditions not yet supported"
  return {
    name := procName
    inputs := inputs.toList
    outputs := outputs
    preconditions := preconditions.toList
    determinism := .nondeterministic
    decreases := none
    isFunctional := false
    body := .Opaque postconditions.toList none []
    md := .empty
  }

/-- Convert a class definition to Laurel types and procedures. -/
def classDefToLaurel (cls : ClassDef) : ToLaurelM Unit := do
  let prefixedName ← prefixName cls.name
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
    let proc ← funcDeclToLaurel (prefixedName ++ "_" ++ method.name) method (isMethod := true)
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

/-- Run the translation and return a Laurel Program, dispatch table,
    and any errors. -/
public def signaturesToLaurel (filepath : System.FilePath) (sigs : Array Signature)
    (modulePrefix : String := "")
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
    overloads := state.overloads }

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

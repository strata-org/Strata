/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.LaurelToCoreTranslator
public import Strata.Languages.Python.PythonToLaurel
import Strata.Languages.Python.ReadPython
import Strata.Languages.Python.PythonLaurelCorePrelude
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import Strata.Languages.Python.Specs.IdentifyOverloads
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Util.DecideProp

/-! ## PySpec Pipeline

Implementation of the Python-to-Core pipeline via PySpec and Laurel.
Reads PySpec Ion files, resolves overloads, builds Laurel declarations,
and translates through to Core for verification.
-/

namespace Strata

open Python (OverloadTable)

/-! ### Types -/

/-- Result of reading PySpec files: combined Laurel declarations and overload table. -/
public structure PySpecLaurelResult where
  laurelProgram : Laurel.Program
  overloads : OverloadTable
  functionSignatures : List Python.PythonFunctionDecl := []
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}

/-! ### Private Helpers -/

/-- Convert a SpecDefault to a Python None expression. -/
private def specDefaultToExpr : Python.Specs.SpecDefault → Python.expr SourceRange
  | .none => .Constant default (.ConNone default) default

/-- Convert a pyspec Arg to a PythonFunctionDecl arg tuple. -/
private def specArgToFuncDeclArg (arg : Python.Specs.Arg): Python.PyArgInfo :=
  {name:= arg.name, md:= default, tys:= ["Any"], default:= arg.default.map specDefaultToExpr}

/-- Build a PythonFunctionDecl from a PySpec FunctionDecl or class method,
    expanding `**kwargs` TypedDict fields into individual parameters. -/
private def funcDeclToFunctionDecl (name : String) (args : Python.Specs.ArgDecls)
    : Except String Python.PythonFunctionDecl := do
  let kwargsArgs ← Python.Specs.ToLaurel.expandKwargsArgs args.kwargs
  let allArgs := args.args ++ args.kwonly ++ kwargsArgs
  pure { name, args := allArgs.toList.map specArgToFuncDeclArg,
         hasKwargs := false, ret := none }

/-- Extract PythonFunctionDecl entries from pyspec signatures.
    Handles both top-level functions and class methods.
    Strips `self` from class methods and expands `**kwargs` TypedDict fields. -/
private def extractFunctionSignatures (sigs : Array Python.Specs.Signature)
    (modulePrefix : String) : Except String (List Python.PythonFunctionDecl) := do
  let prefixName (n : String) := if modulePrefix.isEmpty then n else modulePrefix ++ "_" ++ n
  let mut result : List Python.PythonFunctionDecl := []
  for sig in sigs do
    match sig with
    | .functionDecl func =>
      if !func.isOverload then
        result := result ++ [← funcDeclToFunctionDecl (prefixName func.name) func.args]
    | .classDef cls =>
      let clsName := prefixName cls.name
      for method in cls.methods do
        if method.args.args.size == 0 then
          throw s!"Method '{cls.name}.{method.name}' has no arguments (expected 'self' as first parameter)"
        let posArgs := method.args.args.extract 1 method.args.args.size  -- strip self
        let decl ← funcDeclToFunctionDecl (clsName ++ "@" ++ method.name) { method.args with args := posArgs }
        result := result ++ [decl]
    | _ => pure ()
  return result

/-! ### Building PySpec Laurel Declarations -/

private def mergeOverloads (old new : OverloadTable) : OverloadTable :=
  new.fold (init := old) fun o name n =>
    o.alter name fun s => some <| s.getD {} |>.union n



/-- Read PySpec Ion files and collect their Laurel declarations and overload
    tables into a single combined result. Each Ion file is parsed and translated
    to Laurel via `signaturesToLaurel`. The resulting procedures and types are
    accumulated into one `Laurel.Program`, and overload dispatch entries are
    merged into a single table.

    Each entry is a `(modulePrefix, ionPath)` pair. The `modulePrefix` is used
    to namespace all generated Laurel names (e.g., `"servicelib_Storage"` for
    module `servicelib.Storage`). -/
public def buildPySpecLaurel (pyspecEntries : Array (String × String))
    (overloads : OverloadTable) : EIO String PySpecLaurelResult := do
  let mut combinedProcedures : Array (Laurel.Procedure × String) := #[]
  let mut combinedTypes : Array (Laurel.TypeDefinition × String) := #[]
  let mut allOverloads := overloads
  let mut funcSigs : List Python.PythonFunctionDecl := []
  let mut allTypeAliases : Std.HashMap String String := {}
  for (modulePrefix, ionPath) in pyspecEntries do
    let ionFile : System.FilePath := ionPath
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => throw s!"Could not read {ionFile}: {msg}"
    let { program, errors, overloads, typeAliases } :=
      Python.Specs.ToLaurel.signaturesToLaurel ionPath sigs modulePrefix
    if errors.size > 0 then
      let _ ← IO.eprintln
        s!"{errors.size} PySpec translation warning(s) for {ionPath}:" |>.toBaseIO
      for err in errors do
        let _ ← IO.eprintln s!"  {err.file}: {err.message}" |>.toBaseIO
    allOverloads := mergeOverloads allOverloads overloads
    allTypeAliases := typeAliases.fold (init := allTypeAliases) fun m k v => m.insert k v
    match extractFunctionSignatures sigs modulePrefix with
    | .ok fs => funcSigs := funcSigs ++ fs
    | .error msg => throw msg
    for td in program.types do
      combinedTypes := combinedTypes.push (td, ionPath)
    for proc in program.staticProcedures do
      combinedProcedures := combinedProcedures.push (proc, ionPath)
  -- Reject name collisions across PySpec files
  let mut seenTypes : Std.HashMap String String := {}
  for (td, srcFile) in combinedTypes do
    let name := match td with
      | .Composite ct => ct.name.text
      | .Constrained ct => ct.name.text
      | .Datatype dt => dt.name.text
    match seenTypes.get? name with
    | some prevFile =>
      throw s!"PySpec type name collision: '{name}' defined in both {prevFile} and {srcFile}"
    | none => pure ()
    seenTypes := seenTypes.insert name srcFile
  let mut seenProcs : Std.HashMap String String := {}
  for (proc, srcFile) in combinedProcedures do
    match seenProcs.get? proc.name.text with
    | some prevFile =>
      throw s!"PySpec procedure name collision: '{proc.name.text}' defined in both {prevFile} and {srcFile}"
    | none => pure ()
    seenProcs := seenProcs.insert proc.name.text srcFile

  let combinedLaurel : Laurel.Program := {
    staticProcedures := Strata.Python.pythonRuntimeLaurelPart.staticProcedures ++ combinedProcedures.toList.map Prod.fst
    staticFields := []
    types := Strata.Python.pythonRuntimeLaurelPart.types ++ combinedTypes.toList.map Prod.fst
    constants := []
  }
  return { laurelProgram := combinedLaurel, overloads := allOverloads
           functionSignatures := funcSigs, typeAliases := allTypeAliases }

/-- Read dispatch Ion files and merge their overload tables. -/
public def readDispatchOverloads
    (dispatchPaths : Array String)
    : EIO String OverloadTable := do
  let mut tbl : OverloadTable := {}
  for dispatchPath in dispatchPaths do
    let ionFile : System.FilePath := dispatchPath
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => throw s!"Could not read dispatch file {ionFile}: {msg}"
    let (overloads, errors) :=
      Python.Specs.ToLaurel.extractOverloads dispatchPath sigs
    if errors.size > 0 then
      let _ ← IO.eprintln
        s!"{errors.size} dispatch warning(s) for {ionFile}:" |>.toBaseIO
      for err in errors do
        let _ ← IO.eprintln s!"  {err.file}: {err.message}" |>.toBaseIO
    for (funcName, fnOverloads) in overloads do
      let existing := tbl.getD funcName {}
      tbl := tbl.insert funcName
        (fnOverloads.fold (init := existing)
          fun acc k v => acc.insert k v)
  return tbl

/-- Resolve a module name to a `(modulePrefix, ionPath)` pair for
    `buildPySpecLaurel`.  Returns `none` if the pyspec file is not found. -/
private def resolveModuleEntry (modName : String) (specDir : System.FilePath)
    : EIO String (Option (String × String)) := do
  match Python.Specs.ModuleName.ofString modName with
  | .error _ =>
    let _ ← IO.eprintln
      s!"warning: invalid module name '{modName}', skipping" |>.toBaseIO
    return none
  | .ok mod =>
    match ← mod.specIonPath specDir with
    | some specPath =>
      let pfx := "_".intercalate mod.components.toList
      return some (pfx, specPath.toString)
    | none => return none

/-- Build dispatch overload table, auto-resolve pyspec files
    from the program AST, and return combined Laurel declarations
    and overload table.

    `dispatchModules` and `pyspecModules` are dotted module names
    (e.g., `"servicelib"`, `"servicelib.Storage"`) resolved against
    `specDir`.  Auto-resolved pyspec files that are missing on disk
    are skipped with a warning. -/
public def resolveAndBuildLaurelPrelude
    (dispatchModules : Array String)
    (pyspecModules : Array String)
    (stmts : Array (Python.stmt SourceRange))
    (specDir : System.FilePath := ".")
    : EIO String PySpecLaurelResult := do
  -- Resolve dispatch module names to Ion paths
  let mut dispatchPaths : Array String := #[]
  for modName in dispatchModules do
    match ← resolveModuleEntry modName specDir with
    | some (_, path) => dispatchPaths := dispatchPaths.push path
    | none => throw s!"Dispatch module '{modName}' not found in {specDir}"
  let dispatchOverloads ← readDispatchOverloads dispatchPaths
  let resolveState :=
    Python.Specs.IdentifyOverloads.resolveOverloads dispatchOverloads stmts
  for w in resolveState.warnings do
    let _ ← IO.eprintln s!"warning: {w}" |>.toBaseIO
  -- Auto-resolve pyspec modules from overload table
  let mut autoSpecEntries : Array (String × String) := #[]
  if dispatchModules.size > 0 then
    let resolvedMods := resolveState.modules.toArray.qsort (· < ·)
    for modName in resolvedMods do
      match ← resolveModuleEntry modName specDir with
      | some entry => autoSpecEntries := autoSpecEntries.push entry
      | none =>
        let _ ← IO.eprintln
          s!"warning: auto-resolved pyspec not found for module '{modName}'" |>.toBaseIO
  -- Resolve explicit pyspec module names
  let mut explicitEntries : Array (String × String) := #[]
  for modName in pyspecModules do
    match ← resolveModuleEntry modName specDir with
    | some entry => explicitEntries := explicitEntries.push entry
    | none => throw s!"PySpec module '{modName}' not found in {specDir}"
  let allSpecEntries := autoSpecEntries ++ explicitEntries
  buildPySpecLaurel allSpecEntries dispatchOverloads

/-! ### Pipeline Steps -/

/-- Build PreludeInfo by merging the base Core prelude with PySpec
    Laurel-level declarations and extracted function signatures. -/
public def buildPreludeInfo (result : PySpecLaurelResult) : Python.PreludeInfo :=
  let baseInfo := Python.PreludeInfo.ofCoreProgram { decls := Python.coreOnlyFromRuntimeCorePart }
  let merged := baseInfo.merge
    (Python.PreludeInfo.ofLaurelProgram result.laurelProgram)
  -- Build importedSymbols from merged info + type aliases
  -- Register composite types under their Laurel names
  let symbols : Std.HashMap String Python.ImportedSymbol :=
    merged.compositeTypes.fold (init := {}) fun m name =>
      m.insert name (.compositeType name)
  -- Register procedures under their Laurel names
  let symbols := merged.procedures.fold (init := symbols) fun m name sig =>
    let inlinable := merged.inlinableProcedures.contains name
    m.insert name (.procedure name sig inlinable)
  -- Register functions under their Laurel names
  let symbols := merged.functions.foldl (init := symbols) fun m name =>
    m.insert name (.function name)
  -- Add unprefixed aliases from typeAliases
  let symbols := result.typeAliases.fold (init := symbols)
    fun syms unprefixed prefixed =>
      -- Composite type alias: Storage → dispatch_test_Storage_Storage
      let syms := if merged.compositeTypes.contains prefixed then
        syms.insert unprefixed (.compositeType prefixed) else syms
      -- Procedure aliases: Storage@put_item → ...
      let syms := merged.procedures.fold (init := syms) fun s name sig =>
        if name.startsWith (prefixed ++ "@") then
          let unprefixedName := unprefixed ++ name.drop prefixed.length
          let inlinable := merged.inlinableProcedures.contains name
          s.insert unprefixedName (.procedure name sig inlinable)
        else s
      -- Function aliases
      merged.functions.foldl (init := syms) fun s name =>
        if name.startsWith (prefixed ++ "@") then
          s.insert (unprefixed ++ name.drop prefixed.length) (.function name)
        else s
  { merged with
    functionSignatures :=
      result.functionSignatures ++ merged.functionSignatures
    importedSymbols := symbols }

/-- Combine PySpec and user Laurel programs into a single program,
    prepending External stubs so the Laurel `resolve` pass can see
    prelude names (e.g. `print`, `from_string`). -/
public def combinePySpecLaurel (info : Python.PreludeInfo)
    (pySpec user : Laurel.Program) : Laurel.Program :=
  let stubs := Python.preludeStubs info
  let pySpecNames : Std.HashSet String := pySpec.staticProcedures.foldl (init := {})
    fun s p => if !p.body.isExternal then s.insert p.name.text else s
  let filteredStubs := stubs.filter fun p => !pySpecNames.contains p.name.text
  { staticProcedures := filteredStubs ++ pySpec.staticProcedures ++ user.staticProcedures
    staticFields := pySpec.staticFields ++ user.staticFields
    types := pySpec.types ++ user.types
    constants := pySpec.constants ++ user.constants
  }

/-- Prepend the full Python runtime Core prelude (datatype definitions,
    procedure bodies, etc.) to the Core program produced by Laurel
    translation. -/
private def prependPrelude (coreFromLaurel : Core.Program) : Core.Program :=
  let (preludeDecls, userDecls) := coreFromLaurel.decls.span (fun d => toString d.name != "FIRST_END_MARKER")
  -- The Core-only prelude has proper signatures for functions that the
  -- Laurel→Core translator may have produced as empty-signature stubs.
  -- Filter stubs from preludeDecls when a proper declaration exists.
  let coreOnly := Python.coreOnlyFromRuntimeCorePart
  let coreOnlyNames : Std.HashSet String := coreOnly.foldl (init := {})
    fun s d => s.insert (toString d.name)
  let filteredPrelude := preludeDecls.filter
    fun d => !coreOnlyNames.contains (toString d.name)
  { decls := filteredPrelude ++ coreOnly ++ userDecls }

/-- Split procedure names in a Core program into prelude names
    (before `FIRST_END_MARKER`) and user names (after it).
    If `FIRST_END_MARKER` is absent, nothing is considered prelude. -/
public def splitProcNames (prog : Core.Program)
    : Std.HashSet String × List String :=
  let (before, rest) := prog.decls.span (fun d => toString d.name != "FIRST_END_MARKER")
  let (preludeDecls, userDecls) := match rest with
    | _ :: tl => (before, tl)  -- marker found: before is prelude, after is user
    | [] => ([], before)       -- no marker: everything is user
  let preludeNames := preludeDecls.foldl (init := ({} : Std.HashSet String)) fun s d =>
    match d.getProc? with
    | some p => s.insert (Core.CoreIdent.toPretty p.header.name)
    | none => s
  let userProcNames := userDecls.filterMap fun d =>
    d.getProc?.map (Core.CoreIdent.toPretty ·.header.name)
  (preludeNames, userProcNames)

/-- Translate a combined Laurel program to Core and prepend the full
    runtime prelude.  Resolution errors are suppressed because PySpec
    Laurel procedures reference names defined in the Core prelude
    (`from_none`, `from_string`, `NoError`, etc.) which the Laurel
    resolver cannot see — they are merged after translation. Once the
    Python Core prelude is ported to Laurel, this suppression can be
    removed. -/
public def translateCombinedLaurel (combined : Laurel.Program)
    : (Option Core.Program × List DiagnosticModel) :=
  let (coreOption, errors) := Laurel.translate { emitResolutionErrors := false } combined
  (coreOption.map prependPrelude, errors)

/-- Like `translateCombinedLaurel` but also returns the lowered Laurel program
    (after all Laurel-to-Laurel passes, before translation to Core). -/
public def translateCombinedLaurelWithLowered (combined : Laurel.Program)
    : (Option Core.Program × List DiagnosticModel × Laurel.Program) :=
  let (coreOption, errors, lowered) := Laurel.translateWithLaurel { emitResolutionErrors := false } combined
  (coreOption.map prependPrelude, errors, lowered)

/-- Errors from the pyAnalyzeLaurel pipeline. -/
public inductive PipelineError where
  /-- The Python source contains invalid code (bad method name, wrong arguments, etc.). -/
  | userCode (range : SourceRange := .none) (msg : String)
  /-- The pipeline encountered a Python construct it intentionally does not yet support. -/
  | knownLimitation (msg : String)
  /-- An unexpected failure — likely a bug in the tool itself. -/
  | internal (msg : String)

public instance : ToString PipelineError where
  toString
    | .userCode _ msg => s!"User code error: {msg}"
    | .knownLimitation msg => s!"Known limitation: {msg}"
    | .internal msg => msg

/-- Run the pyAnalyzeLaurel pipeline: read a Python Ion program,
    resolve overloads from dispatch files, load PySpec declarations,
    translate Python to Laurel, and combine with PySpec Laurel.
    Returns the combined Laurel program ready for
    `translateCombinedLaurel`.

    `dispatchModules` and `pyspecModules` are dotted module names
    resolved against `specDir`.

    The optional `sourcePath` overrides the file path embedded in
    Laurel metadata (useful when the Ion file was generated from a
    `.py` source and you want line numbers to refer to the original). -/
public def pyAnalyzeLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (sourcePath : Option String := none)
    (specDir : System.FilePath := ".")
    : EIO PipelineError Laurel.Program := do
  let stmts ←
    match ← Python.readPythonStrata pythonIonPath |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw (.internal msg)

  let result ←
    match ← resolveAndBuildLaurelPrelude dispatchModules pyspecModules stmts specDir |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw (.internal msg)
  let preludeInfo := buildPreludeInfo result

  let metadataPath := sourcePath.getD pythonIonPath
  let (laurelProgram, _ctx) ←
    match Python.pythonToLaurel' preludeInfo stmts none metadataPath result.overloads with
    | .error (.userPythonError range msg) => throw (.userCode range msg)
    | .error (.unsupportedConstruct msg ast) =>
        throw (.knownLimitation s!"Unsupported construct: {msg}\nAST: {ast}")
    | .error e => throw (.internal s!"Python to Laurel translation failed: {e}")
    | .ok result => pure result

  return combinePySpecLaurel preludeInfo result.laurelProgram laurelProgram

end Strata

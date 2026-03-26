/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.OverloadTable
public import Strata.Languages.Python.PythonDialect

import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Python.PythonToLaurel
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
structure PySpecLaurelResult where
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
private def specArgToFuncDeclArg (arg : Python.Specs.Arg)
    : String × String × Option (Python.expr SourceRange) :=
  (arg.name, "Any", arg.default.map specDefaultToExpr)

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
        let decl ← funcDeclToFunctionDecl (clsName ++ "_" ++ method.name) { method.args with args := posArgs }
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
def buildPySpecLaurel (pyspecEntries : Array (String × String))
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
def resolveAndBuildLaurelPrelude
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
def buildPreludeInfo (result : PySpecLaurelResult) : Python.PreludeInfo :=
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
      -- Procedure aliases: Storage_put_item → ...
      let syms := merged.procedures.fold (init := syms) fun s name sig =>
        if name.startsWith (prefixed ++ "_") then
          let unprefixedName := unprefixed ++ name.drop prefixed.length
          let inlinable := merged.inlinableProcedures.contains name
          s.insert unprefixedName (.procedure name sig inlinable)
        else s
      -- Function aliases
      merged.functions.foldl (init := syms) fun s name =>
        if name.startsWith (prefixed ++ "_") then
          s.insert (unprefixed ++ name.drop prefixed.length) (.function name)
        else s
  { merged with
    functionSignatures :=
      result.functionSignatures ++ merged.functionSignatures
    importedSymbols := symbols }

/-- Combine PySpec and user Laurel programs into a single program,
    prepending External stubs so the Laurel `resolve` pass can see
    prelude names (e.g. `print`, `from_string`). -/
def combinePySpecLaurel (info : Python.PreludeInfo)
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

/-! ### Warning and Discovery Helpers -/

open Strata.Python.Specs (ModuleName)

/-- Controls how translation warnings are reported. -/
public inductive WarningOutput where
  /-- Suppress all warning output. -/
  | none
  /-- Print only a count summary (e.g., "3 warning(s)"). -/
  | summary
  /-- Print each warning followed by a count summary. -/
  | detail
deriving Inhabited, BEq

/-- Recursively discover all Python modules under a directory.
    Returns `(moduleName, filePath)` pairs. The `components` array
    accumulates directory names as we recurse, forming the dotted
    module name prefix. -/
private partial def discoverModules (sourceDir : System.FilePath)
    : IO (Array (ModuleName × System.FilePath)) := do
  let rec go (dir : System.FilePath) (components : Array String)
      : IO (Array (ModuleName × System.FilePath)) := do
    let mut acc := #[]
    let entries ← dir.readDir
    for entry in entries do
      if ← entry.path.isDir then
        acc := acc ++ (← go entry.path (components.push entry.fileName))
      else if entry.fileName.endsWith ".py" then
        let parts :=
          if entry.fileName == "__init__.py" then
            components
          else
            components.push (entry.fileName.takeWhile (· != '.') |>.toString)
        if parts.isEmpty then continue
        let dotted := ".".intercalate parts.toList
        match ModuleName.ofString dotted with
        | .ok mod => acc := acc.push (mod, entry.path)
        | .error msg =>
          let _ ← IO.eprintln s!"warning: skipping {entry.path}: {msg}" |>.toBaseIO
    return acc
  go sourceDir #[]

/-- Derive the output path for a Python file by mirroring the source directory
    structure and replacing `.py` with `.pyspec.st.ion`. -/
public def pySpecOutputPath (sourceDir strataDir pythonFile : System.FilePath)
    : Option System.FilePath :=
  let sourceDirStr := sourceDir.toString
  let srcPrefix := if sourceDirStr.endsWith "/" then sourceDirStr else sourceDirStr ++ "/"
  let fileStr := pythonFile.toString
  let relStr := (fileStr.dropPrefix srcPrefix).toString
  if relStr == fileStr then
    none  -- pythonFile not under sourceDir
  else
    let outName := if relStr.endsWith ".py"
      then (relStr.take (relStr.length - 3)).toString ++ ".pyspec.st.ion"
      else relStr ++ ".pyspec.st.ion"
    some (strataDir / outName)

/-- Translate all (or selected) Python modules in a directory to PySpec Ion format.
    If `modules` is empty, discovers and translates all `.py` files under `sourceDir`.
    If `modules` is non-empty, translates only the named modules.  -/
public def pySpecsDir (sourceDir strataDir dialectFile : System.FilePath)
    (modules : Array String := #[])
    (events : Std.HashSet String := {})
    (skipNames : Array String := #[])
    (warningOutput : WarningOutput := .detail)
    : EIO String Unit := do
  -- Create output dir
  match ← IO.FS.createDirAll strataDir |>.toBaseIO with
  | .ok () => pure ()
  | .error e => throw s!"Could not create {strataDir}: {e}"

  -- Build skip identifiers
  let skipIdents := skipNames.foldl (init := {}) fun acc s =>
    match Python.PythonIdent.ofString s with
    | some id => acc.insert id
    | none => acc  -- Unqualified skip names can't be resolved without a module context

  -- Determine which modules to process
  let modulesToProcess : Array (ModuleName × System.FilePath) ←
    if modules.isEmpty then
      match ← discoverModules sourceDir |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"Could not discover modules: {e}"
    else
      let mut result := #[]
      for m in modules do
        let mod ← match ModuleName.ofString m with
          | .ok r => pure r
          | .error e => throw s!"Invalid module name '{m}': {e}"
        let (path, _) ←
          match ← ModuleName.findInPath mod sourceDir |>.toBaseIO with
          | .ok r => pure r
          | .error e => throw s!"Module '{m}' not found in {sourceDir}: {e}"
        result := result.push (mod, path)
      pure result

  -- Translate each module
  let mut failures : Array (String × String) := #[]
  for (mod, pythonFile) in modulesToProcess do
    -- Derive output path
    let some outPath := pySpecOutputPath sourceDir strataDir pythonFile
      | do failures := failures.push (toString mod, s!"Could not derive output path for {pythonFile}")
           continue

    let .ok pythonMd ← pythonFile.metadata |>.toBaseIO
      | do failures := failures.push (toString mod, s!"Could not find {pythonFile}")
           continue

    -- Timestamp check: skip if output is newer than source
    if ← Python.Specs.isNewer outPath pythonMd then
      Python.Specs.baseLogEvent events "import" s!"Skipping {mod} (up to date)"
      continue

    -- Ensure output subdirectory exists
    if let some parent := outPath.parent then
      match ← IO.FS.createDirAll parent |>.toBaseIO with
      | .ok () => pure ()
      | .error e =>
        failures := failures.push (toString mod, s!"Could not create directory: {e}")
        continue

    -- Translate
    Python.Specs.baseLogEvent events "import" s!"Translating {mod}"
    match ← Strata.Python.Specs.translateFile
        dialectFile strataDir pythonFile sourceDir
        (events := events) (skipNames := skipIdents)
        (moduleName := mod) |>.toBaseIO with
    | .error msg =>
      Python.Specs.baseLogEvent events "import" s!"Failed {mod}: {msg}"
      failures := failures.push (toString mod, msg)
    | .ok (sigs, warnings) =>
      -- Write output
      match ← Strata.Python.Specs.writeDDM outPath sigs |>.toBaseIO with
      | .ok () => pure ()
      | .error e =>
        failures := failures.push (toString mod, s!"Could not write {outPath}: {e}")
        continue
      -- Report warnings per module
      if warnings.size > 0 then
        match warningOutput with
        | .none => pure ()
        | .summary =>
          let _ ← IO.eprintln s!"{toString mod}: {warnings.size} warning(s)" |>.toBaseIO
        | .detail =>
          for w in warnings do
            let _ ← IO.eprintln s!"{toString mod}: warning: {w}" |>.toBaseIO

  -- Report failures
  if failures.size > 0 then
    let mut msg := s!"{failures.size} module(s) failed to translate:\n"
    for (modName, err) in failures do
      msg := msg ++ s!"  {modName}: {err}\n"
    throw msg

/-! ### Python-to-Core via Laurel pipeline -/

/-- Translate a Python Ion file all the way to Core.  Composes
    `pyAnalyzeLaurel` (Python → combined Laurel) and
    `translateCombinedLaurel` (Laurel → Core with prelude). -/
public def pyTranslateLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (specDir : System.FilePath := ".")
    : EIO String (Core.Program × List DiagnosticModel) := do
  let laurel ←
    match ← pyAnalyzeLaurel pythonIonPath dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
    | .ok r => pure r
    | .error err => throw (toString err)
  let (coreOption, laurelTranslateErrors) := translateCombinedLaurel laurel
  match coreOption with
  | none => throw s!"Laurel to Core translation failed: {laurelTranslateErrors}"
  | some core => pure (core, laurelTranslateErrors)

end Strata

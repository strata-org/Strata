/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Laurel.Laurel

import Strata.Languages.Python.PythonLaurelCorePrelude
import Strata.Languages.Python.PythonToLaurel
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Languages.Python.ReadPython
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import Strata.Languages.Python.Specs.IdentifyOverloads
import Strata.Languages.Python.Specs.ToLaurel

import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Util.DecideProp

/-! ## SimpleAPI Python

Wraps all the Python-specific parts of the Simple Strata API: PySpec
translation, the Python-to-Laurel-to-Core pipeline, overload resolution,
and helpers for parsing Python source files.

This module is the single import needed for Python functionality.
Internal modules (`PythonToCore`, `PythonToLaurel`, `ReadPython`, etc.)
are private; only the API surface defined here is exported.
-/

namespace Strata

open Python (OverloadTable)

/-! ### PySpec Pipeline Types -/

/-- Result of reading PySpec files: combined Laurel declarations and overload table. -/
public structure PySpecLaurelResult where
  private laurelProgram : Laurel.Program
  private overloads : OverloadTable
  private functionSignatures : List Python.PythonFunctionDecl := []

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

def mergeOverloads (old new : OverloadTable) : OverloadTable :=
  new.fold (init := old) fun o name n =>
    o.alter name fun s => some <| s.getD {} |>.union n

/-- Read PySpec Ion files and collect their Laurel declarations and overload
    tables into a single combined result. Each Ion file is parsed and translated
    to Laurel via `signaturesToLaurel`. The resulting procedures and types are
    accumulated into one `Laurel.Program`, and overload dispatch entries are
    merged into a single table. -/
def buildPySpecLaurel (specRoot : System.FilePath)
    (pyspecModules : Array Python.Specs.ModuleName)
    (overloads : OverloadTable) : EIO String PySpecLaurelResult := do
  let mut combinedProcedures : Array (Laurel.Procedure × String) := #[]
  let mut combinedTypes : Array (Laurel.TypeDefinition × String) := #[]
  let mut allOverloads := overloads
  let mut funcSigs : List Python.PythonFunctionDecl := []
  for mod in pyspecModules do
    let ionFile := mod.ionPath specRoot
    let ionPath := ionFile.toString
    let modulePrefix := toString mod
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => throw s!"Could not read {ionFile}: {msg}"
    let { program, errors, overloads } :=
      Python.Specs.ToLaurel.signaturesToLaurel ionPath sigs modulePrefix
    if errors.size > 0 then
      let _ ← IO.eprintln
        s!"{errors.size} PySpec translation warning(s) for {ionPath}:" |>.toBaseIO
      for err in errors do
        let _ ← IO.eprintln s!"  {err.file}: {err.message}" |>.toBaseIO
    allOverloads := mergeOverloads allOverloads overloads
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
  return {
    laurelProgram := combinedLaurel,
    overloads := allOverloads
    functionSignatures := funcSigs
  }

/-- Read dispatch Ion files and merge their overload tables. -/
def readDispatchOverloads (specRoot : System.FilePath)
    (dispatchModules : Array Python.Specs.ModuleName)
    : EIO String OverloadTable := do
  let mut tbl : OverloadTable := {}
  for mod in dispatchModules do
    let ionFile := mod.ionPath specRoot
    let ionPath := ionFile.toString
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => throw s!"Could not read dispatch file {ionFile}: {msg}"
    let (overloads, errors) :=
      Python.Specs.ToLaurel.extractOverloads ionPath sigs
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

/-- Build dispatch overload table, auto-resolve pyspec modules
    from the program AST, and return combined Laurel declarations
    and overload table.

    Auto-resolved pyspec modules whose Ion files are missing on disk
    are skipped with a warning.  Explicitly provided `pyspecModules`
    still produce a hard error when unreadable. -/
def resolveAndBuildLaurelPrelude
    (specRoot : System.FilePath)
    (dispatchModules : Array Python.Specs.ModuleName)
    (pyspecModules : Array Python.Specs.ModuleName)
    (stmts : Array (Python.stmt SourceRange))
    : EIO String PySpecLaurelResult := do
  if dispatchModules.size > 0 then
    let dispatchOverloads ← readDispatchOverloads specRoot dispatchModules
    let resolveState :=
      Python.Specs.IdentifyOverloads.resolveOverloads dispatchOverloads stmts
    for w in resolveState.warnings do
      let _ ← IO.eprintln s!"warning: {w}" |>.toBaseIO
    let mut autoSpecModules : Array Python.Specs.ModuleName := #[]
    let resolvedMods := resolveState.modules.toArray.qsort (· < ·)
    for modName in resolvedMods do
      match Python.Specs.ModuleName.ofString modName with
      | .error _ =>
        let _ ← IO.eprintln
          s!"warning: invalid module name '{modName}', skipping" |>.toBaseIO
      | .ok mod =>
        let specPath := mod.ionPath specRoot
        if ← specPath.pathExists then
          autoSpecModules := autoSpecModules.push mod
        else
          let _ ← IO.eprintln
            s!"warning: auto-resolved pyspec not found: {specPath}" |>.toBaseIO
    buildPySpecLaurel specRoot (autoSpecModules ++ pyspecModules) dispatchOverloads
  else
    buildPySpecLaurel specRoot pyspecModules {}

/-! ### Pipeline Steps -/

/-- Build PreludeInfo by merging the base Core prelude with PySpec
    Laurel-level declarations and extracted function signatures. -/
def buildPreludeInfo (result : PySpecLaurelResult) : Python.PreludeInfo :=
  let baseInfo := Python.PreludeInfo.ofCoreProgram { decls := Python.coreOnlyFromRuntimeCorePart }
  let merged := baseInfo.merge
    (Python.PreludeInfo.ofLaurelProgram result.laurelProgram)
  { merged with
    functionSignatures :=
      result.functionSignatures ++ merged.functionSignatures }

/-- Combine PySpec and user Laurel programs into a single program,
    prepending External stubs so the Laurel `resolve` pass can see
    prelude names (e.g. `print`, `from_string`). -/
def combinePySpecLaurel (info : Python.PreludeInfo)
    (pySpec user : Laurel.Program) : Laurel.Program :=
  let stubs := Python.preludeStubs info
  { staticProcedures := stubs ++ pySpec.staticProcedures ++ user.staticProcedures
    staticFields := pySpec.staticFields ++ user.staticFields
    types := pySpec.types ++ user.types
    constants := pySpec.constants ++ user.constants
  }

/-- Errors from the pyAnalyzeLaurel pipeline, distinguishing user code
    errors (detected bugs in Python source) from internal tool errors. -/
public inductive PipelineError where
  | userCode (range : SourceRange) (msg : String)
  | internal (msg : String)

public instance : ToString PipelineError where
  toString
    | .userCode _ msg => s!"User code error: {msg}"
    | .internal msg => msg

/--
Python AST statements
-/
public structure PythonStmts where
  private stmts : Array (Python.stmt SourceRange)

/-- Read a Python Ion program and return the single module command.
    Throws if the file is not Ion or does not contain exactly one module. -/
public def readPythonIonModule (strataPath : String) (bytes : ByteArray) : Except String PythonStmts := do
  if !Ion.isIonFile bytes then
    throw s!"{strataPath} is not an Ion file"
  let pgm ←
    match Program.fromIon Python.Python_map Python.Python.name bytes with
    | .ok pgm => pure pgm
    | .error msg => throw s!"Error parsing {strataPath}: {msg}"
  let .isTrue _ := decideProp (pgm.commands.size = 1)
    | throw s!"Expected 1 module in {strataPath}, got {pgm.commands.size}"
  match Python.Command.ofAst pgm.commands[0] with
  | .error e =>
    throw s!"Failed to translate to Python.Command: {e}"
  | .ok cmd =>
    match cmd with
    | Python.Command.Module _ ⟨_, body⟩ _ =>
      pure ⟨body⟩
    | _ =>
      throw "Expected module"

/-- Parse a Python source file (`.py`) into an array of Python AST statements.
    Internally creates a temporary dialect file, runs the Python-to-Strata
    converter, and returns the parsed statements. -/
public def pyParsePythonFile (dialectFile pythonFile : System.FilePath)
    (pythonCmd : String := "python")
    : EIO String PythonStmts := do
  let stmts ← Python.pythonToStrata dialectFile pythonFile (pythonCmd := pythonCmd)
  pure ⟨stmts⟩

/-- Run the pyAnalyzeLaurel pipeline: read a Python Ion program,
    resolve overloads from dispatch modules, load PySpec declarations,
    translate Python to Laurel, and combine with PySpec Laurel.
    Returns the combined Laurel program ready for
    `translateCombinedLaurel`.

    The optional `sourcePath` overrides the file path embedded in
    Laurel metadata (useful when the Ion file was generated from a
    `.py` source and you want line numbers to refer to the original). -/
def pyAnalyzeLaurel
    (pythonIonPath : String)
    (specRoot : System.FilePath)
    (dispatchModules : Array Python.Specs.ModuleName)
    (pyspecModules : Array Python.Specs.ModuleName)
    (sourcePath : Option String := none)
    : EIO PipelineError Laurel.Program := do
  let bytes ←
    match ← IO.FS.readBinFile pythonIonPath |>.toBaseIO with
    | .ok b => pure b
    | .error msg => throw <| .internal s!"Error reading {pythonIonPath}: {msg}"
  let pyStmts ←
    match readPythonIonModule pythonIonPath bytes with
    | .ok r => pure r
    | .error msg => throw (.internal msg)

  let result ←
    match ← resolveAndBuildLaurelPrelude specRoot dispatchModules pyspecModules pyStmts.stmts |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw (.internal msg)
  let preludeInfo := buildPreludeInfo result

  let metadataPath := sourcePath.getD pythonIonPath
  let (laurelProgram, _ctx) ←
    match Python.pythonToLaurel' preludeInfo pyStmts.stmts none metadataPath result.overloads with
    | .error (.userPythonError range msg) => throw (.userCode range msg)
    | .error e => throw (.internal s!"Python to Laurel translation failed: {e}")
    | .ok result => pure result

  return combinePySpecLaurel preludeInfo result.laurelProgram laurelProgram

/-! ### SimpleAPI Python Wrappers -/

/-- Controls how translation warnings are reported. -/
public inductive WarningOutput where
  /-- Suppress all warning output. -/
  | none
  /-- Print only a count summary (e.g., "3 warning(s)"). -/
  | summary
  /-- Print each warning followed by a count summary. -/
  | detail
deriving Inhabited, BEq

/--
Translate a Python source file into PySpec signatures and write the result as a
DDM Ion file under `strataDir`. The output filename is derived from the Python
module name (e.g., `foo.bar` → `foo.bar.pyspec.st.ion`).

The `dialectFile` path points to a serialized Python dialect used during
translation. Optional `events` controls logging (e.g., `"import"` for
import progress).

Each entry in `skipNames` is either a qualified `"module.name"` string
(split on the last dot) or an unqualified `"name"` string (the module is
inferred from the Python file stem). Matching top-level definitions are
omitted from the output, except overloaded variants which are always kept.

The `warningOutput` parameter controls how translation warnings are reported
to stderr: `.none` suppresses them, `.summary` prints only a count, and
`.detail` prints each warning followed by a count.
-/
public def pySpecs (pythonFile strataDir dialectFile : System.FilePath)
    (events : Std.HashSet String := {})
    (skipNames : Array String := #[])
    (warningOutput : WarningOutput := .detail)
    : EIO String Unit := do
  -- Validate source file
  match ← pythonFile.metadata |>.toBaseIO with
  | .ok md =>
    if md.type != .file then
      throw s!"Expected {pythonFile} to be a regular file"
  | .error e => throw s!"Cannot access {pythonFile}: {e}"

  -- Derive module name and search root from the Python file path
  let (mod, _searchRoot) ← match Strata.Python.Specs.ModuleName.ofFile pythonFile with
    | .ok r => pure r
    | .error e => throw e

  let modName := toString mod

  -- Parse skip names into PythonIdents
  let skipIdents := skipNames.foldl (init := {}) fun acc s =>
    match Strata.Python.PythonIdent.ofString s with
    | some id => acc.insert id
    | none => acc.insert { pythonModule := modName, name := s }

  -- Create directory if it doesn't exist
  match ← strataDir.metadata |>.toBaseIO with
  | .ok md =>
    if md.type != .dir then
      throw s!"Expected {strataDir} to be a directory"
  | .error _ =>
    match ← IO.FS.createDirAll strataDir |>.toBaseIO with
    | .ok () => pure ()
    | .error e => throw s!"Could not create {strataDir}: {e}"

  let (sigs, warnings) ← Strata.Python.Specs.translateFile
    dialectFile strataDir pythonFile
    (events := events) (skipNames := skipIdents)

  let strataFile := strataDir / mod.strataFileName
  match ← Strata.Python.Specs.writeDDM strataFile sigs |>.toBaseIO with
  | .ok () => pure ()
  | .error e => throw s!"Could not write {strataFile}: {e}"

  -- Report warnings
  if warnings.size > 0 then
    match warningOutput with
    | .none => pure ()
    | .summary =>
      let _ ← IO.eprintln s!"{warnings.size} warning(s)" |>.toBaseIO
    | .detail =>
      for w in warnings do
        let _ ← IO.eprintln s!"warning: {w}" |>.toBaseIO
      let _ ← IO.eprintln s!"{warnings.size} warning(s)" |>.toBaseIO

/-- Create a temporary file containing the serialized Python dialect,
    pass its path to `action`, and clean up afterwards. -/
public def withPythonDialect {α} (action : System.FilePath → EIO String α)
    : EIO String α := do
  let (_handle, dialectFile) ←
    match ← IO.FS.createTempFile |>.toBaseIO with
    | .ok p => pure p
    | .error msg => throw s!"Cannot create temporary file: {msg}"
  try
    match ← IO.FS.writeBinFile dialectFile Python.Python.toIon |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => throw s!"Cannot write dialect file: {msg}"
    action dialectFile
  finally
    let _ ← IO.FS.removeFile dialectFile |>.toBaseIO

/-- Error type for the pyAnalyzeLaurel pipeline, distinguishing user code
    errors (detected bugs in Python source) from internal tool errors. -/
public inductive PyAnalyzeError where
  | userCode (range : SourceRange) (msg : String)
  | internal (msg : String)

instance : ToString PyAnalyzeError where
  toString
    | .userCode _ msg => s!"User code error: {msg}"
    | .internal msg => msg

private def PyAnalyzeError.ofPipelineError : PipelineError → PyAnalyzeError
  | .userCode range msg => .userCode range msg
  | .internal msg => .internal msg

/-- Resolve an array of `.pyspec.st.ion` file paths into a common spec root
    directory and an array of module names. The root is derived from the first
    file's parent directory; all subsequent files must reside in the same
    directory. Returns `(".", #[])` when the input is empty. -/
def resolveIonPaths (paths : Array String)
    : Except String (System.FilePath × Array Python.Specs.ModuleName) := do
  if h : paths.size > 0 then
    let (firstMod, root) ← Python.Specs.ModuleName.ofIonFile paths[0]
    let mut modules : Array Python.Specs.ModuleName := #[firstMod]
    for path in paths[1:] do
      let (mod, modRoot) ← Python.Specs.ModuleName.ofIonFile path
      if modRoot.toString != root.toString then
        .error s!"Ion file {path} is in {modRoot}, expected {root}"
      modules := modules.push mod
    pure (root, modules)
  else
    pure (".", #[])

/-- File-path wrapper for `pyAnalyzeLaurel`.  Accepts arrays of
    `.pyspec.st.ion` file paths (as provided by CLI `--dispatch` and
    `--pyspec` flags), derives the common spec root and module names,
    then delegates to the module-name-based pipeline. -/
public def pyAnalyzeLaurelFromPaths
    (pythonIonPath : String)
    (dispatchPaths : Array String := #[])
    (pyspecPaths : Array String := #[])
    (sourcePath : Option String := none)
    : EIO PyAnalyzeError Laurel.Program := do
  let allPaths := dispatchPaths ++ pyspecPaths
  let (specRoot, allModules) ← match resolveIonPaths allPaths with
    | .ok r => pure r
    | .error msg => throw (.internal msg)
  let dispatchModules := allModules[:dispatchPaths.size].toArray
  let pyspecModules := allModules[dispatchPaths.size:].toArray
  match ← pyAnalyzeLaurel pythonIonPath specRoot dispatchModules pyspecModules sourcePath |>.toBaseIO with
  | .ok r => pure r
  | .error e => throw (PyAnalyzeError.ofPipelineError e)


/-- Prepend the full Python runtime Core prelude (datatype definitions,
    procedure bodies, etc.) to the Core program produced by Laurel
    translation. -/
private def prependPrelude (coreFromLaurel : Core.Program) : Core.Program :=
  let (preludeDecls, userDecls) := coreFromLaurel.decls.span (fun d => toString d.name != "FIRST_END_MARKER")
  { decls := preludeDecls ++ Python.coreOnlyFromRuntimeCorePart ++ userDecls }

/-- Translate a combined Laurel program (from `pyAnalyzeLaurelFromPaths`)
    to Core, prepending the Python runtime prelude. -/
public def pyTranslateCombinedLaurel (combined : Laurel.Program)
    : (Option Core.Program × List DiagnosticModel) :=
  let (coreOption, errors) := Laurel.translate { emitResolutionErrors := false } combined
  (coreOption.map prependPrelude, errors)

/-- Translate a Python Ion file all the way to Core.  Composes
    `pyAnalyzeLaurelFromPaths` (Python → combined Laurel) and
    `pyTranslateCombinedLaurel` (Laurel → Core with prelude). -/
public def pyTranslateLaurel
    (pythonIonPath : String)
    (dispatchPaths : Array String := #[])
    (pyspecPaths : Array String := #[])
    : EIO String (Core.Program × List DiagnosticModel) := do
  let laurel ←
    match ← pyAnalyzeLaurelFromPaths pythonIonPath dispatchPaths pyspecPaths |>.toBaseIO with
    | .ok r => pure r
    | .error err => throw (toString err)
  let (coreOption, laurelTranslateErrors) := pyTranslateCombinedLaurel laurel
  match coreOption with
  | none => throw s!"Laurel to Core translation failed: {laurelTranslateErrors}"
  | some core => pure (core, laurelTranslateErrors)

/-- Result of overload resolution: the set of resolved module names
    and any warnings produced during the walk. -/
public structure ResolveOverloadsResult where
  modules  : Array String
  warnings : Array String

/-- Identify which overloaded service modules a Python program uses.
    Reads the dispatch Ion file(s), builds the overload table, walks
    the provided Python AST to find dispatched calls, and returns the
    resolved module names (sorted) and any warnings. -/
public def pyResolveOverloads
    (dispatchPaths : Array String)
    (stmts : PythonStmts)
    : EIO String ResolveOverloadsResult := do
  let (specRoot, dispatchModules) ←
    match resolveIonPaths dispatchPaths with
    | .ok r => pure r
    | .error msg => throw msg
  let overloads ← readDispatchOverloads specRoot dispatchModules
  let state :=
    Python.Specs.IdentifyOverloads.resolveOverloads overloads stmts.stmts
  return {
    modules := state.modules.toArray.qsort (· < ·)
    warnings := state.warnings
  }

end Strata

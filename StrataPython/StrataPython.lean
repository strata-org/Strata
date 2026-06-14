/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core
public import StrataPython.PythonDialect
public import StrataPython.PythonIdent
public import StrataDDM.Util.SourceRange
import StrataPython.Specs
import StrataPython.Specs.DDM
import StrataPython.CorePrelude
import StrataPython.PythonToCore
import StrataPython.ReadPython
public import StrataPython.PySpecPipeline
public import StrataDDM.Util.IO

open StrataDDM (SourceRange)
open StrataPython (ModuleName)
open Strata.Pipeline (PipelineContext)

/-! ## Strata Python API

Reading Python sources, translating them to Core or Laurel, and managing
PySpec directories.
-/

public section

namespace StrataPython


/-! ### Python direct-to-Core pipeline -/

/--
Read Python statements from a Strata Ion file.
-/
def readPythonIon (path : String)
    : IO (Array (StrataPython.stmt SourceRange)) := do
  let bytes ← StrataDDM.Util.readBinInputSource path
  match StrataPython.readPythonStrataBytes path bytes with
  | .ok stmts => pure stmts
  | .error msg => throw (IO.userError msg)

/--
Translate a Python Ion file directly to a Core program (bypassing
Laurel). Includes the standard Python Core prelude. An optional
`filePath` can be provided for source location metadata.
-/
def pythonDirectToCore (pythonIonPath : String)
    (filePath : String := "")
    : IO Core.Program := do
  let stmts ← readPythonIon pythonIonPath
  let preludePgm := StrataPython.Core.prelude
  let bpgm := StrataPython.pythonToCore
    StrataPython.coreSignatures stmts preludePgm filePath
  pure { decls := preludePgm.decls ++ bpgm.decls }

/-- Recursively discover all Python modules under a directory.
    Returns `(moduleName, filePath)` pairs. -/
private partial def discoverModules (sourceDir : System.FilePath)
    : IO (Array (ModuleName × System.FilePath)) := do
  let rec go (dir : System.FilePath) (relPrefix : System.FilePath)
      : IO (Array (ModuleName × System.FilePath)) := do
    let mut acc := #[]
    let entries ← dir.readDir
    for entry in entries do
      let relChild : System.FilePath :=
            if relPrefix.toString.isEmpty then
              entry.fileName
            else
              relPrefix / entry.fileName
      if ← entry.path.isDir then
        acc := acc ++ (← go entry.path relChild)
      else if entry.fileName.endsWith ".py" then
        match ModuleName.ofRelativePath relChild with
        | .ok info => acc := acc.push (info.moduleName, entry.path)
        | .error msg =>
          let _ ← IO.eprintln s!"warning: skipping {entry.path}: {msg}" |>.toBaseIO
          continue
    return acc
  go sourceDir ⟨""⟩

/-- Derive the output path for a Python file by mirroring the source directory
    structure and replacing `.py` with `.pyspec.st.ion`. -/
def pySpecOutputPath (sourceDir strataDir pythonFile : System.FilePath)
    : Option System.FilePath := Id.run do
  let sourceDirStr := sourceDir.toString
  let fileStr := pythonFile.toString

  let some relStr := fileStr.dropPrefix? sourceDirStr
    | return none
  if !relStr.startsWith "/" then
    return none
  let relStr := relStr.drop 1
  if relStr.startsWith "/" then
    return none -- Should never occur
  if !relStr.endsWith ".py" then
    return none
  let relStr := relStr.dropEnd 3
  some <| strataDir / ⟨relStr.toString ++ ".pyspec.st.ion"⟩

/-- Controls how translation warnings are reported. -/
inductive WarningOutput where
  /-- Suppress all warning output. -/
  | none
  /-- Print only a count summary (e.g., "3 warning(s)"). -/
  | summary
  /-- Print each warning followed by a count summary. -/
  | detail
deriving Inhabited, BEq

/-- Translate all (or selected) Python modules in a directory to PySpec Ion format.
    If `modules` is empty, discovers and translates all `.py` files under `sourceDir`.
    If `modules` is non-empty, translates only the named modules.  -/
def pySpecsDir (sourceDir strataDir dialectFile : System.FilePath)
    (modules : Array String := #[])
    (events : Std.HashSet String := {})
    (skipNames : Array String := #[])
    (warningOutput : WarningOutput := .detail)
    (pythonCmd : String := "python")
    : EIO String Unit := do
  -- Create output dir
  match ← IO.FS.createDirAll strataDir |>.toBaseIO with
  | .ok () => pure ()
  | .error e => throw s!"Could not create {strataDir}: {e}"

  -- Build skip identifiers
  let skipIdents := skipNames.foldl (init := {}) fun acc s =>
    match PythonIdent.ofString s with
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
        let mod ← match ModuleName.ofString? m with
          | some r => pure r
          | none => throw s!"Invalid module name '{m}'"
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
      | throw s!"Internal error: Could not derive output path for {pythonFile}"

    let .ok pythonMd ← pythonFile.metadata |>.toBaseIO
      | throw s!"Internal error: Could not find {pythonFile}"

    -- Timestamp check: skip if output is newer than source
    if ← Specs.isNewer outPath pythonMd then
      Specs.baseLogEvent events "import" s!"Skipping {mod} (up to date)"
      continue

    -- Ensure output subdirectory exists
    let some parent := outPath.parent
      | throw s!"Internal error: Could not discover parent directory"
    if let .error e ← IO.FS.createDirAll parent |>.toBaseIO then
      throw s!"Internal error: Could not create directory {parent}: {e}"

    -- Translate
    Specs.baseLogEvent events "import" s!"Translating {mod}"
    match ← StrataPython.Specs.translateFile
        dialectFile strataDir pythonFile sourceDir mod
        (events := events) (skipNames := skipIdents)
        (pythonCmd := pythonCmd) |>.toBaseIO with
    | .error msg =>
      Specs.baseLogEvent events "import" s!"Failed {mod}: {msg}"
      failures := failures.push (toString mod, msg)
    | .ok (sigs, warnings) =>
      -- Write output
      match ← StrataPython.Specs.writeDDM outPath sigs |>.toBaseIO with
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
    `pythonAndSpecToLaurel` (Python → combined Laurel) and
    `translateCombinedLaurel` (Laurel → Core with prelude). -/
def pyTranslateLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (specDir : System.FilePath := ".")
    : EIO String (Core.Program × List Strata.DiagnosticModel) := do
  let pctx ← PipelineContext.create (outputMode := .quiet)
  let (laurel, gradualConfig) ←
    match ← (pythonAndSpecToLaurel pythonIonPath dispatchModules pyspecModules (specDir := specDir)).run pctx |>.toBaseIO with
    | .ok r => pure r
    | .error () =>
      let msgs ← pctx.getMessages
      let detail := match msgs.back? with
        | some m => m.message
        | none => "Pipeline aborted"
      throw detail
  let (coreOption, laurelTranslateErrors) ←
    IO.toEIO (fun e => s!"{e}") (translateCombinedLaurel laurel (gradualConfig := some gradualConfig))
  match coreOption with
  | none => throw s!"Laurel to Core translation failed: {laurelTranslateErrors}"
  | some core => pure (core, laurelTranslateErrors)

end StrataPython

end -- public section

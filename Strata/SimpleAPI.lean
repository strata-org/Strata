/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.IO

public import Strata.Transform.CoreTransform
import Strata.Transform.CallElim
import Strata.Transform.LoopElim
public import Strata.Transform.ProcedureInlining
import Strata.Transform.FilterProcedures
import Strata.Transform.IrrelevantAxioms

public import Strata.Languages.Core.Options
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.Manifest
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import Strata.Languages.Python.CorePrelude
import Strata.Languages.Python.PythonToCore
import Strata.Languages.Python.ReadPython

/-! ## Simple Strata API

A simple API for reading, writing, transforming, and analyzing Strata programs.

This API allows clients of Strata to perform its basic operations as directly as
possible. It is intended for use cases that are essentially equivalent to more
fine-grained or more structured equivalents of what the `strata` CLI can
currently do.

It involves several key types:

* `Strata.Dialect`: The formal description of a Strata dialect. Used only to
  describe which dialects are available when reading or writing files.

* `Strata.Program`: The generic AST for a Strata program in any dialect.
   Generally used just as an interim representation before serializing or after
   deserializing a program. Before using a `Strata.Program`, it will usually
   make sense to translate it into the custom AST for a specific dialect.

* `Laurel.Program`: A dialect-specific AST for a program in the Laurel dialect.

* `Core.Program`: A dialect-specific AST for a program in the Core dialect.

* `Core.VCResults`: The results of attempting to prove each verification condition
  that arises from deductive verification of a Core program.

**Note:** Several functions in this API are currently unimplemented due to
functionality that remains to be implemented in the DDM. These functions are
declared using `noncomputable opaque` to define the intended API surface and
should not be invoked yet.
-/

public section

namespace Strata

open Strata.Python.Specs (ModuleName)

/-! ### File I/O -/

/--
Parse a Strata dialect or program in textual format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
def readStrataText :
  Strata.DialectFileMap →
  System.FilePath →
  ByteArray →
  IO Strata.Util.DialectOrProgram :=
  Strata.Util.readStrataText

/--
Parse a Strata dialect or program in Ion format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
def readStrataIon :
  Strata.DialectFileMap →
  System.FilePath →
  ByteArray →
  IO Strata.Util.DialectOrProgram :=
  Strata.Util.readStrataIon

/--
Parse a Strata dialect or program in either textual or Ion format, possibly
loading other dialects as needed along the way. The `DialectFileMap` indicates
where to find the definitions of other dialects. The `FilePath` indicates the
name of the file to be loaded.
-/
def readStrataFile :
  Strata.DialectFileMap →
  System.FilePath →
  IO Strata.Util.DialectOrProgram :=
  Strata.Util.readFile

/--
Serialize a Strata program in textual format. Returns a byte array rather than
writing directly to a file.
-/
def writeStrataText : Strata.Program → ByteArray
| pgm => String.toByteArray pgm.toString

/--
Serialize a Strata program in Ion format. Returns a byte array rather than
writing directly to a file.
-/
def writeStrataIon : Strata.Program → ByteArray
| pgm => pgm.toIon

/--
Read a Laurel source file in textual format and parse it into
a `Laurel.Program`. Handles dialect loading, parsing, and
AST translation in one step.
-/
def parseLaurelText (path : System.FilePath) (content : String)
    : IO Laurel.Program := do
  let input := Strata.Parser.stringInputContext path content
  let dialects :=
    Strata.Elab.LoadedDialects.ofDialects!
      #[Strata.initDialect, Strata.Laurel.Laurel]
  let strataProgram ←
    Strata.Elab.parseStrataProgramFromDialect
      dialects Strata.Laurel.Laurel.name input
  let uri := Strata.Uri.file path.toString
  match Strata.Laurel.TransM.run uri
      (Strata.Laurel.parseProgram strataProgram) with
  | .ok program => pure program
  | .error errors =>
    throw (IO.userError s!"Laurel translation errors: {errors}")

def readLaurelTextFile (path : System.FilePath)
    : IO Laurel.Program := do
  let content ← IO.FS.readFile path
  parseLaurelText path content

/--
Deserialize Laurel Ion bytes (possibly containing multiple files)
into a list of `StrataFile`s. Useful for per-file operations like
printing.
-/
def readLaurelIonFiles (bytes : ByteArray)
    : IO (List Strata.StrataFile) := do
  match Strata.Program.filesFromIon Strata.Laurel.Laurel_map bytes with
  | .ok files => pure files
  | .error msg => throw (IO.userError msg)

/--
Deserialize Laurel Ion bytes and parse all files into a single
combined `Laurel.Program`.
-/
def readLaurelIonProgram (bytes : ByteArray)
    : IO Laurel.Program := do
  let files ← readLaurelIonFiles bytes
  let mut combined : Laurel.Program := {
    staticProcedures := []
    staticFields := []
    types := []
  }
  for file in files do
    match Strata.Laurel.TransM.run
        (Strata.Uri.file file.filePath)
        (Strata.Laurel.parseProgram file.program) with
    | .ok pgm =>
      combined := {
        staticProcedures :=
          combined.staticProcedures ++ pgm.staticProcedures
        staticFields :=
          combined.staticFields ++ pgm.staticFields
        types := combined.types ++ pgm.types
      }
    | .error errors =>
      throw (IO.userError
        s!"Translation errors in {file.filePath}: {errors}")
  pure combined

/-! ### Transformation between generic and dialect-specific representation -/

/--
Translate a program in the dialect-specific AST for Core into the generic Strata
AST. Usually useful as a step before serialization. TODO: we can't yet implement
this, but will be able to once we use DDM-generated translation between the
generic and Strata-specific ASTs.
-/
noncomputable opaque coreToGeneric : Core.Program → Strata.Program

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Core. This can fail with an error message if the input is not a
well-structured instance of the Core dialect.
-/
def genericToCore (p : Strata.Program) : Except String Core.Program :=
  let (program, errors) := Core.getProgram p
  if errors.isEmpty then
    .ok program
  else
    .error s!"Core DDM translation errors:\n{String.intercalate "\n" errors.toList}"

/--
Translate a program in the dialect-specific AST for Laurel into the generic Strata
AST. Usually useful as a step before serialization.
-/
def laurelToGeneric (p : Laurel.Program) : Strata.Program :=
  Laurel.programToStrata p

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Laurel. This can fail with an error message if the input is not a
well-structured instance of the Laurel dialect.

TODO: possibly add an input context argument
-/
def genericToLaurel (p : Strata.Program) : Except String Laurel.Program :=
  Laurel.TransM.run .none (Laurel.parseProgram p)

/-! ### Transformation between dialects -/

/--
Translate a program represented in the dialect-specific AST for the Laurel
dialect into the dialect-specific AST for the Core dialect. This can fail with
an error message if the input program contains constructs that are not yet
supported.
-/
def laurelToCore (p : Laurel.Program) : IO (Except String Core.Program) := do
  let (coreOpt, diags) ← Laurel.translate { emitResolutionErrors := true } p
  match coreOpt with
  | some core => return .ok core
  | none => return .error s!"Laurel to Core translation failed: {diags.map (·.message)}"

/-! ### Transformation of Core programs -/

/-- A single named transform pass with its arguments. -/
inductive Core.TransformPass where
  | inlineProcedures (opts : Core.InlineTransformOptions := {})
  | loopElim
  | callElim
  | filterProcedures (procs : List String)
  | removeIrrelevantAxioms (funcs : List String)

/-- Apply a single pass inside a running `CoreTransformM` context. -/
private def Core.applyPass (program : Core.Program) (pass : Core.TransformPass)
    : Core.Transform.CoreTransformM Core.Program := do
  match pass with
  | .inlineProcedures opts =>
    let (_, prog) ← (Core.procedureInliningPipelinePhase opts).transform program
    return prog
  | .loopElim =>
    pure (Core.loopElim program).fst
  | .callElim =>
    let (_, prog) ← Core.Transform.runProgram coreCallElimCmd program
    return prog
  | .filterProcedures procs =>
    Core.FilterProcedures.run program procs
  | .removeIrrelevantAxioms funcs =>
    Core.IrrelevantAxioms.run program funcs

/-- Run a chain of transform passes on a Core program.  All passes share a
    single `CoreTransformState`, so fresh variable counters accumulate across
    passes and cached analyses (e.g., call graphs) can be reused. -/
def Core.runTransforms (p : Core.Program) (passes : List Core.TransformPass)
    : Except Core.Transform.Err Core.Program :=
  Core.Transform.run p (fun prog => do
    let mut program := prog
    for pass in passes do
      program ← Core.applyPass program pass
    return program)

/--
Transform a Core program to inline some or all procedure calls.
-/
def Core.inlineProcedures (p : Core.Program) (opts : Core.InlineTransformOptions)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.inlineProcedures opts]

/--
Transform a Core program to replace each loop with assertions and assumptions about
its invariants.
-/
def Core.loopElimUsingContract (p : Core.Program) : Core.Program :=
  (Core.loopElim p).fst

/--
Transform a Core program to replace each procedure call with assertions and
assumptions about its contract.
-/
def Core.callElimUsingContract (p : Core.Program) : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.callElim]

/--
Transform a Core program to keep only the named procedures and their
transitive callees, removing everything else.
-/
def Core.filterProcedures (p : Core.Program) (targetProcs : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.filterProcedures targetProcs]

/--
Transform a Core program to remove axiom declarations that are irrelevant
to the named functions (based on call graph analysis).
-/
def Core.removeIrrelevantAxioms (p : Core.Program) (functions : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.removeIrrelevantAxioms functions]

/-! ### Analysis of Core programs -/

/--
Verify a Core program, including any external solver invocation
that is necessary.
-/
def Core.verifyProgram
    (program : Core.Program)
    (options : Core.VerifyOptions)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (proceduresToVerify : Option (List String) := none)
    (externalPhases : List Core.AbstractedPhase := [])
    (prefixPhases : List Core.PipelinePhase := [])
    (keepAllFilesPrefix : Option String := none)
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults := do
    -- Install manifest-emitting callbacks when --no-solve is used so the
    -- split-solve-reconcile workflow works for all verify entry points.
    let mut callbacks : Core.VerifyCallbacks := .empty
    let mut manifestRef? : Option (IO.Ref (Array Core.ManifestObligation)) := none
    if options.skipSolver then
      let ref ← IO.mkRef (#[] : Array Core.ManifestObligation)
      callbacks := Core.manifestEmittingCallbacks ref
      manifestRef? := some ref
    let results ← EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify program tempDir proceduresToVerify options moreFns externalPhases prefixPhases
        (keepAllFilesPrefix := keepAllFilesPrefix)
        (callbacks := callbacks))
    if let some ref := manifestRef? then
      let entries ← ref.get
      Core.emitManifest tempDir options entries
    pure results
  let ioAction := match options.vcDirectory with
    | .some vcDir => IO.FS.createDirAll vcDir *> runVerification vcDir
    | .none => IO.FS.withTempDir runVerification
  IO.toEIO (fun e => s!"{e}") ioAction

/-! ### Analysis of Laurel programs -/

/--
Analyze a Laurel program by translating to Core and running
verification. Returns VC results (if translation succeeded)
and any translation diagnostics.
-/
def Laurel.verifyProgram
    (program : Laurel.Program)
    (options : Core.VerifyOptions := .default)
    : IO (Option Core.VCResults × List DiagnosticModel) :=
  Strata.Laurel.verifyToVcResults program { verifyOptions := options }

/--
Analyze a Laurel program and return structured diagnostic models
(combining translation errors and verification results).
-/
def Laurel.analyzeToDiagnosticModels
    (program : Laurel.Program)
    (options : Core.VerifyOptions := .default)
    : IO (Array DiagnosticModel) :=
  Strata.Laurel.verifyToDiagnosticModels program { verifyOptions := options }

/-! ### Python direct-to-Core pipeline -/

/--
Read Python statements from a Strata Ion file.
-/
def readPythonIon (path : String)
    : IO (Array (Strata.Python.stmt SourceRange)) := do
  let bytes ← Strata.Util.readBinInputSource path
  match Strata.Python.readPythonStrataBytes path bytes with
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
  let preludePgm := Strata.Python.Core.prelude
  let bpgm := Strata.pythonToCore
    Strata.Python.coreSignatures stmts preludePgm filePath
  pure { decls := preludePgm.decls ++ bpgm.decls }

/-- Controls how translation warnings are reported. -/
inductive WarningOutput where
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
      | throw s!"Internal error: Could not derive output path for {pythonFile}"

    let .ok pythonMd ← pythonFile.metadata |>.toBaseIO
      | throw s!"Internal error: Could not find {pythonFile}"

    -- Timestamp check: skip if output is newer than source
    if ← Python.Specs.isNewer outPath pythonMd then
      Python.Specs.baseLogEvent events "import" s!"Skipping {mod} (up to date)"
      continue

    -- Ensure output subdirectory exists
    let some parent := outPath.parent
      | throw s!"Internal error: Could not discover parent directory"
    if let .error e ← IO.FS.createDirAll parent |>.toBaseIO then
      throw s!"Internal error: Could not create directory {parent}: {e}"

    -- Translate
    Python.Specs.baseLogEvent events "import" s!"Translating {mod}"
    match ← Strata.Python.Specs.translateFile
        dialectFile strataDir pythonFile sourceDir
        (events := events) (skipNames := skipIdents)
        (moduleName := mod) (pythonCmd := pythonCmd) |>.toBaseIO with
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
    `pythonAndSpecToLaurel` (Python → combined Laurel) and
    `translateCombinedLaurel` (Laurel → Core with prelude). -/
def pyTranslateLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (specDir : System.FilePath := ".")
    : EIO String (Core.Program × List DiagnosticModel) := do
  let laurel ←
    match ← pythonAndSpecToLaurel pythonIonPath dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
    | .ok r => pure r
    | .error err => throw (toString err)
  let (coreOption, laurelTranslateErrors) ← IO.toEIO (fun e => s!"{e}") (translateCombinedLaurel laurel)
  match coreOption with
  | none => throw s!"Laurel to Core translation failed: {laurelTranslateErrors}"
  | some core => pure (core, laurelTranslateErrors)

end Strata

end -- public section

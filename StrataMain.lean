/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable with utilities for working with Strata files.
import Strata.DDM.Integration.Java.Gen
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SarifOutput
import Strata.Languages.C_Simp.Verify
import Strata.Languages.B3.Verifier.Program
import Strata.Util.IO
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Python.Python
import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import Strata.Languages.Python.Specs.IdentifyOverloads
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Python.CorePrelude
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Languages.Python.PythonLaurelCorePrelude
import Strata.Backends.CBMC.CollectSymbols
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline

import Strata.SimpleAPI
import Strata.Util.Profile

open Strata

open Core (VerifyOptions VerboseMode VerificationMode CheckLevel)

/-! ## Exit codes

All `strata` subcommands use a common exit code scheme:

| Code | Category           | Meaning                                                   |
|------|--------------------|-----------------------------------------------------------|
| 0    | Success            | Analysis passed, inconclusive, or `--no-solve` completed.  |
| 1    | User error         | Bad input: invalid arguments, malformed source, etc.      |
| 2    | Failures found     | Analysis completed and found failures.                    |
| 3    | Internal error     | Tool bug, unexpected solver result, or translation crash. |
| 4    | Known limitation   | Intentionally unsupported language construct.             |

Codes 1–2 are **user-actionable** (fix the input or the code under analysis).
Codes 3–4 are **tool-side** (report as a bug or wait for support). -/

namespace ExitCode
  def userError        : UInt8 := 1
  def failuresFound    : UInt8 := 2
  def internalError    : UInt8 := 3
  def knownLimitation  : UInt8 := 4
end ExitCode

def exitFailure {α} (message : String) (hint : String := "strata --help") : IO α := do
  IO.eprintln s!"Exception: {message}\n\nRun {hint} for additional help."
  IO.Process.exit ExitCode.userError

/-- Exit with code 1 for user errors (bad input, malformed source, etc.). -/
def exitUserError {α} (message : String) : IO α := do
  IO.eprintln s!"❌ {message}"
  IO.Process.exit ExitCode.userError

/-- Exit with code 2 for analysis failures found. -/
def exitFailuresFound {α} (message : String) : IO α := do
  IO.eprintln s!"Failures found: {message}"
  IO.Process.exit ExitCode.failuresFound

/-- Exit with code 3 for internal errors (tool limitations or crashes). -/
def exitInternalError {α} (message : String) : IO α := do
  IO.eprintln s!"Exception: {message}"
  IO.Process.exit ExitCode.internalError

/-- Exit with code 4 for known limitations (unsupported constructs). -/
def exitKnownLimitation {α} (message : String) : IO α := do
  IO.eprintln s!"Known limitation: {message}"
  IO.Process.exit ExitCode.knownLimitation

/-- Like `exitFailure` but tailors the help hint to a specific subcommand. -/
def exitCmdFailure {α} (cmdName : String) (message : String) : IO α :=
  exitFailure message (hint := s!"strata {cmdName} --help")

/-- How a flag consumes arguments. -/
inductive FlagArg where
  | none              -- boolean flag, e.g. --verbose
  | arg (name : String)    -- takes one value, e.g. --output <file>
  | repeat (name : String) -- takes one value, may appear multiple times, e.g. --include <path>

/-- A flag that a command accepts. -/
structure Flag where
  name : String         -- flag name without "--", used as lookup key
  help : String
  takesArg : FlagArg := .none

/-- Parsed flags from the command line. -/
structure ParsedFlags where
  flags : Std.HashMap String (Option String) := {}
  repeated : Std.HashMap String (Array String) := {}

namespace ParsedFlags

def getBool (pf : ParsedFlags) (name : String) : Bool :=
  pf.flags.contains name

def getString (pf : ParsedFlags) (name : String) : Option String :=
  match pf.flags[name]? with
  | some (some v) => some v
  | _ => Option.none

def getRepeated (pf : ParsedFlags) (name : String) : Array String :=
  pf.repeated[name]?.getD #[]

def insertFlag (pf : ParsedFlags) (name : String) (value : Option String) : ParsedFlags :=
  { pf with flags := pf.flags.insert name value }

def insertRepeated (pf : ParsedFlags) (name : String) (value : String) : ParsedFlags :=
  let arr := pf.repeated[name]?.getD #[]
  { pf with repeated := pf.repeated.insert name (arr.push value) }

def buildDialectFileMap (pflags : ParsedFlags) : IO Strata.DialectFileMap := do
  let preloaded := Strata.Elab.LoadedDialects.builtin
    |>.addDialect! Strata.Python.Python
    |>.addDialect! Strata.Python.Specs.DDM.PythonSpecs
    |>.addDialect! Strata.Core
    |>.addDialect! Strata.Laurel.Laurel
    |>.addDialect! Strata.smtReservedKeywordsDialect
    |>.addDialect! Strata.SMTCore
    |>.addDialect! Strata.SMT
    |>.addDialect! Strata.SMTResponse
  let mut sp ← Strata.DialectFileMap.new preloaded
  for path in pflags.getRepeated "include" do
    match ← sp.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok sp' => sp := sp'
  return sp

end ParsedFlags

def parseCheckMode (pflags : ParsedFlags) : IO VerificationMode :=
  match pflags.getString "check-mode" with
  | .none => pure .deductive
  | .some s => match VerificationMode.ofString? s with
    | .some m => pure m
    | .none => exitFailure s!"Invalid check mode: '{s}'. Must be {VerificationMode.options}."

def parseCheckLevel (pflags : ParsedFlags) : IO CheckLevel :=
  match pflags.getString "check-level" with
  | .none => pure .minimal
  | .some s => match CheckLevel.ofString? s with
    | .some l => pure l
    | .none => exitFailure s!"Invalid check level: '{s}'. Must be {CheckLevel.options}."

def checkModeFlag : Flag :=
  { name := "check-mode",
    help := s!"Check mode: {VerificationMode.options}. Default: 'deductive'.",
    takesArg := .arg "mode" }

def checkLevelFlag : Flag :=
  { name := "check-level",
    help := s!"Check level: {CheckLevel.options}. Default: 'minimal'.",
    takesArg := .arg "level" }

structure Command where
  name : String
  args : List String
  flags : List Flag := []
  help : String
  callback : Vector String args.length → ParsedFlags → IO Unit

def includeFlag : Flag :=
  { name := "include", help := "Add a dialect search path.", takesArg := .repeat "path" }

def checkCommand : Command where
  name := "check"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Parse and validate a Strata file (text or Ion). Reports errors and exits."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let _ ← Strata.readStrataFile fm v[0]

def toIonCommand : Command where
  name := "toIon"
  args := [ "input", "output" ]
  flags := [includeFlag]
  help := "Convert a Strata text file to Ion binary format."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap
    let pd ← Strata.readStrataFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.FS.writeBinFile v[1] d.toIon
    | .program pgm =>
      IO.FS.writeBinFile v[1] pgm.toIon

def printCommand : Command where
  name := "print"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Pretty-print a Strata file (text or Ion) to stdout."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap
    -- Special case for already loaded dialects.
    let ld ← searchPath.getLoaded
    if mem : v[0] ∈ ld.dialects then
      IO.print <| ld.dialects.format v[0] mem
      return
    let pd ← Strata.readStrataFile searchPath v[0]
    match pd with
    | .dialect d =>
      let ld ← searchPath.getLoaded
      let .isTrue mem := inferInstanceAs (Decidable (d.name ∈ ld.dialects))
        | exitInternalError "Internal error reading file."
      IO.print <| ld.dialects.format d.name mem
    | .program pgm =>
      IO.print <| toString pgm

def diffCommand : Command where
  name := "diff"
  args := [ "file1", "file2" ]
  flags := [includeFlag]
  help := "Compare two program files for syntactic equality. Reports the first difference found."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let p1 ← Strata.readStrataFile fm v[0]
    let p2 ← Strata.readStrataFile fm v[1]
    match p1, p2 with
    | .program p1, .program p2 =>
      if p1.dialect != p2.dialect then
        exitFailure s!"Dialects differ: {p1.dialect} and {p2.dialect}"
        let Decidable.isTrue eq := inferInstanceAs (Decidable (p1.commands.size = p2.commands.size))
          | exitFailure s!"Number of commands differ {p1.commands.size} and {p2.commands.size}"
        for (c1, c2) in Array.zip p1.commands p2.commands do
          if c1 != c2 then
            exitFailure s!"Commands differ: {repr c1} and {repr c2}"
    | _, _ =>
      exitFailure "Cannot compare dialect def with another dialect/program."

def readPythonStrata (strataPath : String) : IO (Array (Strata.Python.stmt SourceRange)) := do
  let bytes ← Strata.Util.readBinInputSource strataPath
  match Strata.Python.readPythonStrataBytes strataPath bytes with
  | .ok stmts => pure stmts
  | .error msg => exitFailure msg

def pySpecsCommand : Command where
  name := "pySpecs"
  args := [ "source_dir", "output_dir" ]
  flags := [
    { name := "quiet", help := "Suppress default logging." },
    { name := "log", help := "Enable logging for an event type.",
      takesArg := .repeat "event" },
    { name := "skip",
      help := "Skip a top-level definition (module.name). Overloads are kept.",
      takesArg := .repeat "name" },
    { name := "module",
      help := "Translate only the named module (dot-separated). May be repeated.",
      takesArg := .repeat "module" }
  ]
  help := "Translate Python specification files in a directory into Strata DDM Ion format. If --module is given, translates only those modules; otherwise translates all .py files. Creates subdirectories as needed. (Experimental)"
  callback := fun v pflags => do
    let quiet := pflags.getBool "quiet"
    let mut events : Std.HashSet String := {}
    if !quiet then
      events := events.insert "import"
    for e in pflags.getRepeated "log" do
      events := events.insert e
    let skipNames := pflags.getRepeated "skip"
    let modules := pflags.getRepeated "module"
    let warningOutput : Strata.WarningOutput :=
      if quiet then .none else .detail
    -- Serialize embedded dialect for Python subprocess
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
      let r ← Strata.pySpecsDir (events := events)
                (skipNames := skipNames)
                (modules := modules)
                (warningOutput := warningOutput)
                v[0] v[1] dialectFile |>.toBaseIO
      match r with
      | .ok () => pure ()
      | .error msg => exitFailure msg

def pyTranslateCommand : Command where
  name := "pyTranslate"
  args := [ "file" ]
  help := "Translate a Python Ion program to Core and print the result to stdout."
  callback := fun v _ => do
    let stmts ← readPythonStrata v[0]
    let preludePgm := Strata.Python.Core.prelude
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures stmts preludePgm
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    IO.print newPgm

/-- Derive Python source file path from Ion file path.
    E.g., "tests/test_foo.python.st.ion" -> "tests/test_foo.py" -/
def ionPathToPythonPath (ionPath : String) : Option String :=
  if ionPath.endsWith ".python.st.ion" then
    let basePath := ionPath.dropEnd ".python.st.ion".length |>.toString
    some (basePath ++ ".py")
  else if ionPath.endsWith ".py.ion" then
    some (ionPath.dropEnd ".ion".length |>.toString)
  else
    none

/-- Try to read Python source file for source location reconstruction -/
def tryReadPythonSource (ionPath : String) : IO (Option (String × String)) := do
  match ionPathToPythonPath ionPath with
  | none => return none
  | some pyPath =>
    try
      let content ← IO.FS.readFile pyPath
      return some (pyPath, content)
    catch _ =>
      return none

/-- Format related position strings from metadata, if present. -/
def formatRelatedPositions (md : Imperative.MetaData Core.Expression)
    (mfm : Option (String × Lean.FileMap)) : String :=
  let ranges := Imperative.getRelatedFileRanges md
  if ranges.isEmpty then "" else
  match mfm with
  | none => ""
  | some (_, fm) =>
    let lines := ranges.filterMap fun fr =>
      if fr.range.isNone then none else
      match fr.file with
      | .file "" => some "\n  Related location: in prelude file"
      | .file _ =>
        let pos := fm.toPosition fr.range.start
        some s!"\n  Related location: line {pos.line}, col {pos.column}"
    String.join lines.toList

def pyAnalyzeCommand : Command where
  name := "pyAnalyze"
  args := [ "file" ]
  flags := [{ name := "verbose", help := "Enable verbose output." },
            { name := "sarif", help := "Write results as SARIF to <file>.sarif." },
            { name := "unique-bound-names", help := "Use globally unique names for quantifier-bound variables." },
            { name := "vc-directory",
              help := "Store VCs in SMT-Lib format in <dir>.",
              takesArg := .arg "dir" }]
  help := "Verify a Python Ion program. Translates to Core, inlines procedures, and runs SMT verification."
  callback := fun v pflags => do
    let verbose := pflags.getBool "verbose"
    let outputSarif := pflags.getBool "sarif"
    let uniqueBoundNames := pflags.getBool "unique-bound-names"
    let filePath := v[0]
    let stmts ← readPythonStrata filePath
    -- Try to read the Python source for line number conversion
    let pySourceOpt ← tryReadPythonSource filePath
    let preludePgm := Strata.Python.Core.prelude
    -- Use the Python source path if available, otherwise fall back to Ion path
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures stmts preludePgm sourcePathForMetadata
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    if verbose then
      IO.print newPgm
    match (Core.inlineProcedures newPgm ⟨ .some (λ name _ => name ≠ "main") ⟩) with
    | .error e => exitInternalError e
    | .ok newPgm =>
      if verbose then
        IO.println "Inlined: "
        IO.print newPgm
      let solverName : String := "Strata/Languages/Python/z3_parallel.py"
      let verboseMode := VerboseMode.ofBool verbose
      let vcDir : Option System.FilePath := pflags.getString "vc-directory" |>.map (⟨·⟩)
      let options :=
              { VerifyOptions.default with
                stopOnFirstError := false,
                verbose := verboseMode,
                removeIrrelevantAxioms := .Precise,
                solver := solverName,
                uniqueBoundNames := uniqueBoundNames,
                vcDirectory := vcDir }
      let runVerification tempDir :=
          EIO.toIO
            (fun f => IO.Error.userError (toString f))
            (Core.verify newPgm tempDir .none options
                                      (moreFns := Strata.Python.ReFactory))
      let vcResults ← match options.vcDirectory with
                      | .none => IO.FS.withTempDir runVerification
                      | .some tempDir => runVerification tempDir
      let mfm : Option (String × Lean.FileMap) := match pySourceOpt with
        | some (pyPath, srcText) => some (pyPath, .ofString srcText)
        | none => none
      let mut s := ""
      for vcResult in vcResults do
        -- Build location string based on available metadata
        let (locationPrefix, locationSuffix) := match Imperative.getFileRange vcResult.obligation.metadata with
          | some fr =>
            if fr.range.isNone then ("", "")
            else
              match mfm with
              | some (pyPath, fm) =>
                -- Check if this metadata is from the Python source (not CorePrelude)
                match fr.file with
                | .file path =>
                  if path == pyPath then
                    let pos := fm.toPosition fr.range.start
                    -- For failures, show at beginning; for passes, show at end
                    if vcResult.isFailure then
                      (s!"Assertion failed at line {pos.line}, col {pos.column}: ", "")
                    else
                      ("", s!" (at line {pos.line}, col {pos.column})")
                  else
                    -- From CorePrelude or other source, show byte offsets
                    if vcResult.isFailure then
                      (s!"Assertion failed for prelude: ", "")
                    else
                      ("", s!" (in prelude)")
              | none =>
                if vcResult.isFailure then
                  (s!"Assertion failed at byte offset: ", "")
                else
                  ("", s!" (at byte offset)")
          | none => ("", "")
        let outcomeStr := vcResult.formatOutcome
        let relatedStr := formatRelatedPositions vcResult.obligation.metadata mfm
        s := s ++ s!"\n{locationPrefix}{vcResult.obligation.label}: \
                      {outcomeStr}{locationSuffix}{relatedStr}\n"
      IO.println s
      -- Output in SARIF format if requested
      if outputSarif then
        let files := match mfm with
          | some (pyPath, fm) => Map.empty.insert (Strata.Uri.file pyPath) fm
          | none => Map.empty
        Core.Sarif.writeSarifOutput .deductive files vcResults (filePath ++ ".sarif")

/-! ### pyAnalyzeLaurel result helpers

The `pyAnalyzeLaurel` command emits two structured lines on stdout:
- `RESULT: <category>` — machine-readable category, always the last line.
- `DETAIL: <detail>`   — human-readable context (error message or VC counts).

Exit codes follow the common scheme (see `ExitCode` above).
A successful run exits 0 with `RESULT: Analysis success` or `RESULT: Inconclusive`. -/

/-- Determines which VC results count as successes and which count as failures
    for the purposes of the `pyAnalyzeLaurel` summary and exit code.
    Implementation-error results are partitioned out first; the classifier then
    partitions the rest into success / failure / inconclusive.
    Narrowing `isFailure` (e.g. to only `alwaysFalseAndReachable`) automatically
    widens inconclusive.
    Future: may be extended with `isWarning` for non-fatal diagnostic categories. -/
structure ResultClassifier where
  isSuccess : Core.VCResult → Bool := (·.isSuccess)
  isFailure : Core.VCResult → Bool := (·.isFailure)

private def printPyAnalyzeResult (category : String) (detail : String) : IO Unit := do
  IO.println s!"DETAIL: {detail}"
  IO.println s!"RESULT: {category}"

private def exitPyAnalyzeUserError {α} (message : String) : IO α := do
  printPyAnalyzeResult "User error" message
  IO.Process.exit ExitCode.userError

private def exitPyAnalyzeFailuresFound {α} (detail : String) : IO α := do
  printPyAnalyzeResult "Failures found" detail
  IO.Process.exit ExitCode.failuresFound

private def exitPyAnalyzeInternalError {α} (message : String) : IO α := do
  printPyAnalyzeResult "Internal error" message
  IO.Process.exit ExitCode.internalError

private def exitPyAnalyzeKnownLimitation {α} (message : String) : IO α := do
  printPyAnalyzeResult "Known limitation" message
  IO.Process.exit ExitCode.knownLimitation

/-- Print the final RESULT/DETAIL lines based on solver outcomes.
    Always called on successful pipeline completion (as opposed to the
    exit helpers above, which are called on early pipeline failure).
    Classification uses successive partitioning: implementation errors are
    removed first, then the classifier partitions the rest into
    success / failure / inconclusive (guaranteeing disjointness).
    Unreachable count is reported as supplementary info. -/
private def printPyAnalyzeSummary (vcResults : Array Core.VCResult)
    (checkMode : VerificationMode := .deductive) : IO Unit := do
  let classifier : ResultClassifier :=
    match checkMode with
    | .bugFinding | .bugFindingAssumingCompleteSpec =>
      { isFailure := fun r => match r.outcome with
          | .ok o => o.alwaysFalseAndReachable
          | _     => false }
    | _ => {}
  -- 1. Partition out implementation errors (broken results, not classifiable).
  let (implError, classifiable) :=
    vcResults.partition (fun r => r.isImplementationError || r.hasSMTError)
  -- 2. Successive partitioning via the classifier: success → failure → inconclusive.
  let (success, rest)          := classifiable.partition classifier.isSuccess
  let (failure, inconclusive)  := rest.partition classifier.isFailure
  -- 3. Unreachable is informational (not a separate partition).
  let nUnreachable  := vcResults.filter (·.isUnreachable) |>.size
  let nImplError    := implError.size
  let nSuccess      := success.size
  let nFailure      := failure.size
  let nInconclusive := inconclusive.size
  let unreachableStr := if nUnreachable > 0 then s!", {nUnreachable} unreachable" else ""
  let implErrorStr   := if nImplError > 0   then s!", {nImplError} implementation errors" else ""
  let counts := s!"{nSuccess} passed, {nFailure} failed, {nInconclusive} inconclusive{unreachableStr}{implErrorStr}"
  if nImplError > 0 then
    exitPyAnalyzeInternalError s!"An unexpected result was produced. {counts}"
  else if nFailure > 0 then
    exitPyAnalyzeFailuresFound counts
  else
    printPyAnalyzeResult (if nInconclusive > 0 then "Inconclusive" else "Analysis success") counts

private def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  let suffixes := [".python.st.ion", ".py.ion", ".st.ion", ".st"]
  match suffixes.find? (name.endsWith ·) with
  | some sfx => (name.dropEnd sfx.length).toString
  | none     => name

def pyAnalyzeLaurelCommand : Command where
  name := "pyAnalyzeLaurel"
  args := [ "file" ]
  flags := [{ name := "verbose", help := "Enable verbose output." },
            { name := "no-solve", help := "Generate SMT-Lib files but do not invoke the solver." },
            { name := "profile", help := "Print elapsed time for each pipeline step." },
            { name := "quiet", help := "Suppress warnings on stderr." },
            checkModeFlag, checkLevelFlag,
            { name := "spec-dir",
              help := "Directory containing compiled PySpec Ion files.",
              takesArg := .arg "dir" },
            { name := "dispatch",
              help := "Dispatch module name (e.g., servicelib).",
              takesArg := .repeat "module" },
            { name := "pyspec",
              help := "PySpec module name (e.g., servicelib.Storage).",
              takesArg := .repeat "module" },
            { name := "sarif", help := "Write results as SARIF to <file>.sarif." },
            { name := "vc-directory",
              help := "Store VCs in SMT-Lib format in <dir>.",
              takesArg := .arg "dir" },
            { name := "unique-bound-names", help := "Use globally unique names for quantifier-bound variables." },
            { name := "keep-all-files",
              help := "Store intermediate Laurel and Core programs in <dir>.",
              takesArg := .arg "dir" }]
  help := "Verify a Python Ion program via the Laurel pipeline. Translates Python to Laurel to Core, then runs SMT verification."
  callback := fun v pflags => do
    let verbose := pflags.getBool "verbose"
    let profile := pflags.getBool "profile"
    let quiet := pflags.getBool "quiet"
    let outputSarif := pflags.getBool "sarif"
    let filePath := v[0]
    let pySourceOpt ← tryReadPythonSource filePath
    let keepDir := pflags.getString "keep-all-files"
    let baseName := deriveBaseName filePath
    if let some dir := keepDir then
      IO.FS.createDirAll dir

    let dispatchModules := pflags.getRepeated "dispatch"
    let pyspecModules := pflags.getRepeated "pyspec"
    let specDir := pflags.getString "spec-dir" |>.getD "."
    unless ← System.FilePath.isDir specDir do
      exitFailure s!"spec-dir '{specDir}' does not exist or is not a directory"
    let sourcePath := pySourceOpt.map (·.1)
    -- Build FileMap for source position resolution.
    let mfm : Option (String × Lean.FileMap) := match pySourceOpt with
      | some (pyPath, srcText) => some (pyPath, .ofString srcText)
      | none => none
    let combinedLaurel ←
      match ← Strata.pyAnalyzeLaurel filePath dispatchModules pyspecModules sourcePath
                (specDir := specDir) (profile := profile)
                (quiet := quiet) |>.toBaseIO with
      | .ok r => pure r
      | .error (.userCode range msg) =>
        let location := if range.isNone then "" else
          match mfm with
          | some (_, fm) =>
            let pos := fm.toPosition range.start
            s!" at line {pos.line}, col {pos.column}"
          | none => ""
        -- Emit structured set-info metadata before DETAIL/RESULT lines.
        -- Also write the set-info metadata to user_errors.txt.
        let filePath' := sourcePath.getD filePath
        let mut lines := #[
          s!"(set-info :file {Strata.escapeSMTStringLit filePath'})"
        ]
        unless range.isNone do
          lines := lines.push s!"(set-info :start {range.start})"
          lines := lines.push s!"(set-info :stop {range.stop})"
        lines := lines.push s!"(set-info :error-message {Strata.escapeSMTStringLit msg})"
        for line in lines do
          IO.println line
        IO.FS.writeFile "user_errors.txt" (String.intercalate "\n" lines.toList ++ "\n")
        exitPyAnalyzeUserError s!"{msg}{location}"
      | .error (.knownLimitation msg) =>
        exitPyAnalyzeKnownLimitation msg
      | .error (.internal msg) =>
        exitPyAnalyzeInternalError msg

    if verbose then
      IO.println "\n==== Laurel Program ===="
      IO.println f!"{combinedLaurel}"

    if let some dir := keepDir then
      let path := s!"{dir}/{baseName}.laurel"
      IO.FS.writeFile path (toString (Std.Format.pretty f!"{combinedLaurel}") ++ "\n")

    let (coreProgramOption, laurelTranslateErrors, loweredLaurel) ←
      profileStep profile "Laurel to Core translation" do
        pure (Strata.translateCombinedLaurelWithLowered combinedLaurel)

    if let some dir := keepDir then
      let path := s!"{dir}/{baseName}.lowered.laurel"
      IO.FS.writeFile path (toString (Std.Format.pretty f!"{loweredLaurel}") ++ "\n")

    let coreProgram ←
      match coreProgramOption with
      | none =>
        exitPyAnalyzeInternalError s!"Laurel to Core translation failed: {laurelTranslateErrors}"
      | some core => pure core

    if verbose then
      IO.println "\n==== Core Program ===="
      IO.print coreProgram

    -- Split prelude / user procedure names.
    -- Only procedures whose file range matches the user source are targets.
    let userSourcePath := sourcePath.getD filePath
    let (preludeNames, userProcNames) :=
      Strata.splitProcNames coreProgram [userSourcePath]

    if let some dir := keepDir then
      let path := s!"{dir}/{baseName}.core"
      IO.FS.writeFile path (toString coreProgram)

    -- Inline pyspec procedures so their precondition assertions are checked
    -- at call sites with concrete arguments.
    let pyspecFiles := pflags.getRepeated "pyspec"
    let coreProgram ← profileStep profile "Inline PySpec procedures" do
      if pyspecFiles.size > 0 then
        match Core.inlineProcedures coreProgram
              ⟨.some (fun name _ => name ≠ "__main__" && !preludeNames.contains name)⟩ with
        | .error e => exitPyAnalyzeInternalError s!"Inlining failed: {e}"
        | .ok inlined => do
          if verbose then
            IO.println "\n==== Core Program (after inlining) ===="
            IO.print inlined
          if let some dir := keepDir then
            let path := s!"{dir}/{baseName}.inlined.core"
            IO.FS.writeFile path (toString inlined)
          pure inlined
      else pure coreProgram

    -- Verify using Core verifier
    let checkMode ← parseCheckMode pflags
    let checkLevel ← parseCheckLevel pflags
    let noSolve := pflags.getBool "no-solve"
    if noSolve && (pflags.getString "vc-directory").isNone && keepDir.isNone then
      exitCmdFailure "pyAnalyzeLaurel"
        "--no-solve requires --vc-directory or \
         --keep-all-files to specify where SMT \
         files are stored."
    let uniqueBoundNames := pflags.getBool "unique-bound-names"
    let baseOptions : VerifyOptions :=
      { VerifyOptions.default with
        stopOnFirstError := false, verbose := .quiet, solver := Core.defaultSolver,
        removeIrrelevantAxioms := .Precise,
        checkMode := checkMode, checkLevel := checkLevel,
        skipSolver := noSolve,
        alwaysGenerateSMT := noSolve,
        uniqueBoundNames := uniqueBoundNames,
        profile := profile }
    let options : VerifyOptions := match pflags.getString "vc-directory" with
      | .some dir => { baseOptions with vcDirectory := some (dir : System.FilePath) }
      | .none => match keepDir with
        | some dir => { baseOptions with vcDirectory := some (s!"{dir}/{baseName}" : System.FilePath) }
        | none => baseOptions
    let vcResults ← profileStep profile "SMT verification" do
      match ← Core.verifyProgram coreProgram options
                (moreFns := Strata.Python.ReFactory)
                (proceduresToVerify := some userProcNames) |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitPyAnalyzeInternalError msg

    -- Print translation errors (always on stderr)
    if !laurelTranslateErrors.isEmpty then
      IO.eprintln "\n==== Errors ===="
      for err in laurelTranslateErrors do
        IO.eprintln err

    -- Print per-VC results by default, unless SARIF mode is used
    if !outputSarif then
      let mut s := ""
      for vcResult in vcResults do
        let fileMap := mfm.map (·.2)
        let location := match Imperative.getFileRange vcResult.obligation.metadata with
          | some fr =>
            if fr.range.isNone then ""
            else s!"{fr.format fileMap (includeEnd? := false)}"
          | none => ""
        let messageSuffix := match vcResult.obligation.metadata.getPropertySummary with
          | some msg => s!" - {msg}"
          | none => s!" - {vcResult.obligation.label}"
        let outcomeStr := vcResult.formatOutcome
        let loc := if !location.isEmpty then s!"{location}: " else "unknown location: "
        s := s ++ s!"{loc}{outcomeStr}{messageSuffix}\n"
      IO.print s
    -- Output in SARIF format if requested
    if outputSarif then
      let files := match mfm with
        | some (pyPath, fm) => Map.empty.insert (Strata.Uri.file pyPath) fm
        | none => Map.empty
      Core.Sarif.writeSarifOutput checkMode files vcResults (filePath ++ ".sarif")
    printPyAnalyzeSummary vcResults checkMode

def pyAnalyzeToGotoCommand : Command where
  name := "pyAnalyzeToGoto"
  args := [ "file" ]
  help := "Translate a Strata Python Ion file to CProver GOTO JSON files."
  callback := fun v _ => do
    let filePath := v[0]
    let stmts ← readPythonStrata filePath
    let pySourceOpt ← tryReadPythonSource filePath
    let preludePgm := Strata.Python.Core.prelude
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures stmts preludePgm sourcePathForMetadata
    let sourceText := pySourceOpt.map (·.2)
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    match Core.inlineProcedures newPgm ⟨.some (fun name _ => name ≠ "main")⟩ with
    | .error e => exitInternalError e
    | .ok newPgm =>
      -- Type-check the full program (registers Python types like ExceptOrNone)
      let Ctx := { Lambda.LContext.default with functions := Strata.Python.PythonFactory, knownTypes := Core.KnownTypes }
      let Env := Lambda.TEnv.default
      let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env newPgm with
        | .ok r => pure r
        | .error e => exitInternalError s!"{e.format none}"
      -- Find the main procedure
      let some mainDecl := tcPgm.decls.find? fun d =>
          match d with
          | .proc p _ => Core.CoreIdent.toPretty p.header.name == "main"
          | _ => false
        | exitInternalError "No main procedure found"
      let some p := mainDecl.getProc?
        | exitInternalError "main is not a procedure"
      -- Translate procedure to GOTO (mirrors CoreToGOTO.transformToGoto post-typecheck logic)
      let baseName := deriveBaseName filePath
      let procName := Core.CoreIdent.toPretty p.header.name
      let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
      let distincts := tcPgm.decls.filterMap fun d => match d with
        | .distinct name es _ => some (name, es) | _ => none
      match procedureToGotoCtx Env p sourceText (axioms := axioms) (distincts := distincts)
            (varTypes := tcPgm.getVarTy?) with
      | .error e => exitInternalError s!"{e}"
      | .ok (ctx, liftedFuncs) =>
        let extraSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure (Lean.toJson s)
          | .error e => exitInternalError s!"{e}"
        let (symtab, goto) ← emitProcWithLifted Env procName ctx liftedFuncs extraSyms
              (moduleName := baseName)
        let symTabFile := s!"{baseName}.symtab.json"
        let gotoFile := s!"{baseName}.goto.json"
        IO.FS.writeFile symTabFile symtab.pretty
        IO.FS.writeFile gotoFile goto.pretty
        IO.println s!"Written {symTabFile} and {gotoFile}"

def pyTranslateLaurelCommand : Command where
  name := "pyTranslateLaurel"
  args := [ "file" ]
  flags := [{ name := "pyspec",
              help := "PySpec module name (e.g., servicelib.Storage).",
              takesArg := .repeat "module" },
            { name := "dispatch",
              help := "Dispatch module name (e.g., servicelib).",
              takesArg := .repeat "module" },
            { name := "spec-dir",
              help := "Directory containing compiled PySpec Ion files.",
              takesArg := .arg "dir" }]
  help := "Translate a Strata Python Ion file through Laurel to Strata Core. Write results to stdout."
  callback := fun v pflags => do
    let dispatchModules := pflags.getRepeated "dispatch"
    let pyspecModules := pflags.getRepeated "pyspec"
    let specDir := pflags.getString "spec-dir" |>.getD "."
    unless ← System.FilePath.isDir specDir do
      exitFailure s!"spec-dir '{specDir}' does not exist or is not a directory"
    let coreProgram ←
      match ← Strata.pyTranslateLaurel v[0] dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    IO.print coreProgram

def pyAnalyzeLaurelToGotoCommand : Command where
  name := "pyAnalyzeLaurelToGoto"
  args := [ "file" ]
  flags := [{ name := "pyspec",
              help := "PySpec module name (e.g., servicelib.Storage).",
              takesArg := .repeat "module" },
            { name := "dispatch",
              help := "Dispatch module name (e.g., servicelib).",
              takesArg := .repeat "module" },
            { name := "spec-dir",
              help := "Directory containing compiled PySpec Ion files.",
              takesArg := .arg "dir" }]
  help := "Translate a Strata Python Ion file through Laurel to CProver GOTO JSON files."
  callback := fun v pflags => do
    let filePath := v[0]
    let dispatchModules := pflags.getRepeated "dispatch"
    let pyspecModules := pflags.getRepeated "pyspec"
    let specDir := pflags.getString "spec-dir" |>.getD "."
    unless ← System.FilePath.isDir specDir do
      exitFailure s!"spec-dir '{specDir}' does not exist or is not a directory"
    let (coreProgram, laurelTranslateErrors) ←
      match ← Strata.pyTranslateLaurel filePath dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    let sourceText := (← tryReadPythonSource filePath).map (·.2)
    let baseName := deriveBaseName filePath
    match ← Strata.inlineCoreToGotoFiles coreProgram baseName sourceText
              (factory := Strata.Python.PythonFactory) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => exitFailure msg

def javaGenCommand : Command where
  name := "javaGen"
  args := [ "dialect", "package", "output-dir" ]
  flags := [includeFlag]
  help := "Generate Java source files from a DDM dialect definition. Accepts a dialect name (e.g. Laurel) or a dialect file path."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let ld ← fm.getLoaded
    let d ← if mem : v[0] ∈ ld.dialects then
      pure ld.dialects[v[0]]
    else
      match ← Strata.readStrataFile fm v[0] with
      | .dialect d => pure d
      | .program _ => exitFailure "Expected a dialect file, not a program file."
    match Strata.Java.generateDialect d v[1] with
    | .ok files =>
      Strata.Java.writeJavaFiles v[2] v[1] files
      IO.println s!"Generated Java files for {d.name} in {v[2]}/{Strata.Java.packageToPath v[1]}"
    | .error msg =>
      exitFailure s!"Error generating Java: {msg}"

def laurelVerifyOptions : VerifyOptions := { VerifyOptions.default with solver := "z3" }

def deserializeIonToLaurelFiles (bytes : ByteArray) : IO (List Strata.StrataFile) := do
  match Strata.Program.filesFromIon Strata.Laurel.Laurel_map bytes with
  | .ok files => pure files
  | .error msg => exitFailure msg

def laurelAnalyzeBinaryCommand : Command where
  name := "laurelAnalyzeBinary"
  args := []
  help := "Verify Laurel Ion programs read from stdin and print diagnostics. Combines multiple input files."
  callback := fun _ _ => do
    -- Read bytes from stdin
    let stdinBytes ← (← IO.getStdin).readBinToEnd

    let strataFiles ← deserializeIonToLaurelFiles stdinBytes

    let mut combinedProgram : Strata.Laurel.Program := {
      staticProcedures := []
      staticFields := []
      types := []
    }

    for strataFile in strataFiles do

      let transResult := Strata.Laurel.TransM.run (Strata.Uri.file strataFile.filePath) (Strata.Laurel.parseProgram strataFile.program)
      match transResult with
      | .error transErrors => exitFailure s!"Translation errors in {strataFile.filePath}: {transErrors}"
      | .ok laurelProgram =>

        combinedProgram := {
          staticProcedures := combinedProgram.staticProcedures ++ laurelProgram.staticProcedures
          staticFields := combinedProgram.staticFields ++ laurelProgram.staticFields
          types := combinedProgram.types ++ laurelProgram.types
        }

    let diagnostics ← Strata.Laurel.verifyToDiagnosticModels combinedProgram laurelVerifyOptions

    IO.println s!"==== DIAGNOSTICS ===="
    for diag in diagnostics do
      IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"

def pySpecToLaurelCommand : Command where
  name := "pySpecToLaurel"
  args := [ "python_path", "strata_path" ]
  help := "Translate a PySpec Ion file to Laurel declarations. The Ion file must already exist."
  callback := fun v _ => do
    let pythonFile : System.FilePath := v[0]
    let strataDir : System.FilePath := v[1]
    let some mod := pythonFile.fileStem
      | exitFailure s!"No stem {pythonFile}"
    let .ok mod := Strata.Python.Specs.ModuleName.ofString mod
      | exitFailure s!"Invalid module {mod}"
    let ionFile := strataDir / mod.strataFileName
    let sigs ←
      match ← Strata.Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => exitFailure s!"Could not read {ionFile}: {msg}"
    let result := Strata.Python.Specs.ToLaurel.signaturesToLaurel pythonFile sigs ""
    if result.errors.size > 0 then
      IO.eprintln s!"{result.errors.size} translation warning(s):"
      for err in result.errors do
        IO.eprintln s!"  {err.file}: {err.message}"
    let pgm := result.program
    IO.println s!"Laurel: {pgm.staticProcedures.length} procedure(s), {pgm.types.length} type(s)"
    IO.println s!"Overloads: {result.overloads.size} function(s)"
    for td in pgm.types do
      IO.println s!"  {Strata.Laurel.formatTypeDefinition td}"
    for proc in pgm.staticProcedures do
      IO.println s!"  {Strata.Laurel.formatProcedure proc}"

def pyResolveOverloadsCommand : Command where
  name := "pyResolveOverloads"
  args := [ "python_path", "dispatch_ion" ]
  help := "Identify which overloaded service modules a \
    Python program uses. Prints one module name per \
    line to stdout."
  callback := fun v _ => do
    let pythonFile : System.FilePath := v[0]
    let dispatchPath := v[1]
    -- Read dispatch overload table
    let overloads ←
      match ← readDispatchOverloads #[dispatchPath] |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    -- Convert .py to Python AST
    let stmts ←
      IO.FS.withTempFile fun _handle dialectFile => do
        IO.FS.writeBinFile dialectFile
          Strata.Python.Python.toIon
        match ← Strata.Python.pythonToStrata dialectFile pythonFile |>.toBaseIO with
        | .ok s => pure s
        | .error msg => exitFailure msg
    -- Walk AST and collect modules
    let state :=
      Strata.Python.Specs.IdentifyOverloads.resolveOverloads
        overloads stmts
    for w in state.warnings do
      IO.eprintln s!"warning: {w}"
    let sorted := state.modules.toArray.qsort (· < ·)
    for m in sorted do
      IO.println m

def laurelParseCommand : Command where
  name := "laurelParse"
  args := [ "file" ]
  help := "Parse a Laurel source file (no verification)."
  callback := fun v _ => do
    let path : System.FilePath := v[0]
    let content ← IO.FS.readFile path
    let input := Strata.Parser.stringInputContext path content
    let dialects := Strata.Elab.LoadedDialects.ofDialects! #[Strata.initDialect, Strata.Laurel.Laurel]
    let strataProgram ← Strata.Elab.parseStrataProgramFromDialect dialects Strata.Laurel.Laurel.name input

    let uri := Strata.Uri.file path.toString
    let transResult := Strata.Laurel.TransM.run uri (Strata.Laurel.parseProgram strataProgram)
    match transResult with
    | .error transErrors => exitFailure s!"Translation errors: {transErrors}"
    | .ok _ => IO.println "Parse successful"

def laurelAnalyzeCommand : Command where
  name := "laurelAnalyze"
  args := [ "file" ]
  help := "Analyze a Laurel source file. Write diagnostics to stdout."
  callback := fun v _ => do
    let path : System.FilePath := v[0]
    let content ← IO.FS.readFile path
    let input := Strata.Parser.stringInputContext path content
    let dialects := Strata.Elab.LoadedDialects.ofDialects! #[Strata.initDialect, Strata.Laurel.Laurel]
    let strataProgram ← Strata.Elab.parseStrataProgramFromDialect dialects Strata.Laurel.Laurel.name input

    let uri := Strata.Uri.file path.toString
    let transResult := Strata.Laurel.TransM.run uri (Strata.Laurel.parseProgram strataProgram)
    match transResult with
    | .error transErrors => exitFailure s!"Translation errors: {transErrors}"
    | .ok laurelProgram =>
      let (vcResultsOption, errors) ← Strata.Laurel.verifyToVcResults laurelProgram { VerifyOptions.default with solver := "z3" }
      if !errors.isEmpty then
        IO.println s!"==== ERRORS ===="
      for err in errors do
        IO.println s!"{err.message}"
      match vcResultsOption with
      | none => return
      | some vcResults =>
        IO.println s!"==== RESULTS ===="
        for vc in vcResults do
          IO.println s!"{vc.obligation.label}: {match vc.outcome with | .ok o => repr o | .error e => e}"

def laurelAnalyzeToGotoCommand : Command where
  name := "laurelAnalyzeToGoto"
  args := [ "file" ]
  help := "Translate a Laurel source file to CProver GOTO JSON files."
  callback := fun v _ => do
    let path : System.FilePath := v[0]
    let content ← IO.FS.readFile path
    let input := Strata.Parser.stringInputContext path content
    let dialects := Strata.Elab.LoadedDialects.ofDialects! #[Strata.initDialect, Strata.Laurel.Laurel]
    let strataProgram ← Strata.Elab.parseStrataProgramFromDialect dialects Strata.Laurel.Laurel.name input

    let uri := Strata.Uri.file path.toString
    let transResult := Strata.Laurel.TransM.run uri (Strata.Laurel.parseProgram strataProgram)
    match transResult with
    | .error transErrors => exitFailure s!"Translation errors: {transErrors}"
    | .ok laurelProgram =>
      match Strata.Laurel.translate {} laurelProgram with
      | (none, diags) => exitFailure s!"Core translation errors: {diags.map (·.message)}"
      | (some coreProgram, errors) =>
        let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
        let Env := Lambda.TEnv.default
        let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env coreProgram with
          | .ok r => pure r
          | .error e => exitInternalError s!"{e.format none}"
        let procs := tcPgm.decls.filterMap fun d => d.getProc?
        let funcs := tcPgm.decls.filterMap fun d =>
          match d.getFunc? with
          | some f =>
            let name := Core.CoreIdent.toPretty f.name
            if f.body.isSome && f.typeArgs.isEmpty
              && name != "Int.DivT" && name != "Int.ModT"
            then some f else none
          | none => none
        if procs.isEmpty && funcs.isEmpty then exitInternalError "No procedures or functions found"
        let baseName := deriveBaseName path.toString
        let typeSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure s
          | .error e => exitInternalError s!"{e}"
        let typeSymsJson := Lean.toJson typeSyms
        let sourceText := some content
        let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
        let distincts := tcPgm.decls.filterMap fun d => match d with
          | .distinct name es _ => some (name, es) | _ => none
        let mut symtabPairs : List (String × Lean.Json) := []
        let mut gotoFns : Array Lean.Json := #[]
        let mut allLiftedFuncs : List Core.Function := []
        for p in procs do
          let procName := Core.CoreIdent.toPretty p.header.name
          match procedureToGotoCtx Env p (sourceText := sourceText) (axioms := axioms) (distincts := distincts)
                (varTypes := tcPgm.getVarTy?) with
          | .error e => exitInternalError s!"{e}"
          | .ok (ctx, liftedFuncs) =>
            allLiftedFuncs := allLiftedFuncs ++ liftedFuncs
            let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson procName ctx)
            match json.symtab with
            | .obj m => symtabPairs := symtabPairs ++ m.toList
            | _ => pure ()
            match json.goto with
            | .obj m =>
              match m.toList.find? (·.1 == "functions") with
              | some (_, .arr fns) => gotoFns := gotoFns ++ fns
              | _ => pure ()
            | _ => pure ()
        for f in funcs ++ allLiftedFuncs do
          let funcName := Core.CoreIdent.toPretty f.name
          match functionToGotoCtx Env f with
          | .error e => exitInternalError s!"{e}"
          | .ok ctx =>
            let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson funcName ctx)
            match json.symtab with
            | .obj m => symtabPairs := symtabPairs ++ m.toList
            | _ => pure ()
            match json.goto with
            | .obj m =>
              match m.toList.find? (·.1 == "functions") with
              | some (_, .arr fns) => gotoFns := gotoFns ++ fns
              | _ => pure ()
            | _ => pure ()
        match typeSymsJson with
        | .obj m => symtabPairs := symtabPairs ++ m.toList
        | _ => pure ()
        -- Deduplicate: keep first occurrence of each symbol name (proper function
        -- symbols come before basic symbol references from callers)
        let mut seen : Std.HashSet String := {}
        let mut dedupPairs : List (String × Lean.Json) := []
        for (k, v) in symtabPairs do
          if !seen.contains k then
            seen := seen.insert k
            dedupPairs := dedupPairs ++ [(k, v)]
        -- Add CBMC default symbols (architecture constants, builtins)
        -- and wrap in {"symbolTable": ...} for symtab2gb
        let symtabObj := dedupPairs.foldl
          (fun (acc : Std.TreeMap.Raw String Lean.Json) (k, v) => acc.insert k v)
          .empty
        let symtab := CProverGOTO.wrapSymtab symtabObj (moduleName := baseName)
        let goto := Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)]
        let symTabFile := s!"{baseName}.symtab.json"
        let gotoFile := s!"{baseName}.goto.json"
        IO.FS.writeFile symTabFile symtab.pretty
        IO.FS.writeFile gotoFile goto.pretty
        IO.println s!"Written {symTabFile} and {gotoFile}"

def laurelPrintCommand : Command where
  name := "laurelPrint"
  args := []
  help := "Read Laurel Ion from stdin and print in concrete syntax to stdout."
  callback := fun _ _ => do
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let strataFiles ← deserializeIonToLaurelFiles stdinBytes
    for strataFile in strataFiles do
      IO.println s!"// File: {strataFile.filePath}"
      let p := strataFile.program
      let c := p.formatContext {}
      let s := p.formatState
      let fmt := p.commands.foldl (init := f!"") fun f cmd =>
        f ++ (Strata.mformat cmd c s).format
      IO.println (fmt.pretty 100)
      IO.println ""

def prettyPrintCore (p : Core.Program) : String :=
  let decls := p.decls.map fun d =>
    let s := toString (Std.format d)
    -- Add newlines after major sections in procedures
    s.replace "preconditions:" "\n  preconditions:"
     |>.replace "postconditions:" "\n  postconditions:"
     |>.replace "body:" "\n  body:\n    "
     |>.replace "assert [" "\n    assert ["
     |>.replace "init (" "\n    init ("
     |>.replace "while (" "\n    while ("
     |>.replace "if (" "\n      if ("
     |>.replace "call [" "\n    call ["
     |>.replace "else{" "\n      else {"
     |>.replace "}}" "}\n    }"
  String.intercalate "\n" decls

def laurelToCoreCommand : Command where
  name := "laurelToCore"
  args := [ "file" ]
  help := "Translate a Laurel source file to Core and print to stdout."
  callback := fun v _ => do
    let path : System.FilePath := v[0]
    let content ← IO.FS.readFile path
    let input := Strata.Parser.stringInputContext path content
    let dialects := Strata.Elab.LoadedDialects.ofDialects! #[Strata.initDialect, Strata.Laurel.Laurel]
    let strataProgram ← Strata.Elab.parseStrataProgramFromDialect dialects Strata.Laurel.Laurel.name input

    let uri := Strata.Uri.file path.toString
    let transResult := Strata.Laurel.TransM.run uri (Strata.Laurel.parseProgram strataProgram)
    match transResult with
    | .error transErrors => exitFailure s!"Translation errors: {transErrors}"
    | .ok laurelProgram =>
      let (coreProgramOption, errors) := Strata.Laurel.translate {} laurelProgram
      if !errors.isEmpty then
        IO.println s!"Core translation errors: {errors.map (·.message)}"
      match coreProgramOption with
      | none => return
      | some coreProgram => IO.println (prettyPrintCore coreProgram)

/-- Print a string word-wrapped to `width` columns with `indent` spaces of indentation. -/
private def printIndented (indent : Nat) (s : String) (width : Nat := 80) : IO Unit := do
  let pad := "".pushn ' ' indent
  let words := s.splitOn " " |>.filter (!·.isEmpty)
  let mut line := pad
  let mut first := true
  for word in words do
    if first then
      line := line ++ word
      first := false
    else if line.length + 1 + word.length > width then
      IO.println line
      line := pad ++ word
    else
      line := line ++ " " ++ word
  unless line.length ≤ indent do
    IO.println line

structure CommandGroup where
  name : String
  commands : List Command
  commonFlags : List Flag := []

def verifyCommand : Command where
  name := "verify"
  args := [ "file" ]
  flags := [
    { name := "verbose", help := "Print extra information during analysis." },
    { name := "check", help := "Process up until SMT generation, but don't solve." },
    { name := "type-check", help := "Exit after semantic dialect's type inference/checking." },
    { name := "parse-only", help := "Exit after DDM parsing and type checking." },
    { name := "stop-on-first-error", help := "Exit after the first verification error." },
    { name := "unique-bound-names", help := "Use globally unique names for quantifier-bound variables." },
    { name := "sarif", help := "Output results in SARIF format to <file>.sarif." },
    { name := "output-format", help := "Output format (only 'sarif' supported).", takesArg := .arg "format" },
    { name := "vc-directory", help := "Store VCs in SMT-Lib format in <dir>.", takesArg := .arg "dir" },
    { name := "procedures", help := "Verify only the specified procedures (comma-separated).", takesArg := .arg "procs" },
    { name := "solver", help := s!"SMT solver executable to use (default: {Core.defaultSolver}).", takesArg := .arg "name" },
    { name := "solver-timeout", help := "Solver timeout in seconds.", takesArg := .arg "seconds" },
    checkModeFlag, checkLevelFlag ]
  help := "Verify a Strata program file (.core.st, .csimp.st, or .b3.st)."
  callback := fun v pflags => do
    let file := v[0]
    let verbose := pflags.getBool "verbose"
    let checkOnly := pflags.getBool "check"
    let typeCheckOnly := pflags.getBool "type-check"
    let parseOnly := pflags.getBool "parse-only"
    let stopOnFirstError := pflags.getBool "stop-on-first-error"
    let uniqueBoundNames := pflags.getBool "unique-bound-names"
    let outputSarif := pflags.getBool "sarif" || pflags.getString "output-format" == some "sarif"
    let checkMode ← parseCheckMode pflags
    let checkLevel ← parseCheckLevel pflags
    let solverTimeout ← match pflags.getString "solver-timeout" with
      | .none => pure VerifyOptions.default.solverTimeout
      | .some s => match s.toNat? with
        | .some n => pure n
        | .none => exitCmdFailure "verify" s!"Invalid number of seconds: {s}"
    let proceduresToVerify := pflags.getString "procedures" |>.map (·.splitToList (· == ','))
    let opts : VerifyOptions :=
      { VerifyOptions.default with
        verbose := if verbose then .normal else .quiet,
        checkOnly, typeCheckOnly, parseOnly, stopOnFirstError, uniqueBoundNames,
        outputSarif, checkMode, checkLevel, solverTimeout,
        vcDirectory := pflags.getString "vc-directory",
        solver := pflags.getString "solver" |>.getD Core.defaultSolver }
    let text ← Strata.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Core
    let dctx := dctx.addDialect! C_Simp
    let dctx := dctx.addDialect! B3CST
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      println! s!"Successfully parsed."
      if opts.parseOnly then return
      if opts.typeCheckOnly then
        let ans := if file.endsWith ".csimp.st" then
                     C_Simp.typeCheck pgm opts
                   else
                     typeCheck inputCtx pgm opts
        match ans with
        | .error e =>
          println! f!"{e.formatRange (some inputCtx.fileMap) true} {e.message}"
          IO.Process.exit 1
        | .ok _ =>
          println! f!"Program typechecked."
          return
      -- Full verification
      let vcResults ← try
        if file.endsWith ".csimp.st" then
          C_Simp.verify pgm opts
        else if file.endsWith ".b3.st" || file.endsWith ".b3cst.st" then
          let ast ← match B3.Verifier.programToB3AST pgm with
            | Except.error msg => throw (IO.userError s!"Failed to convert to B3 AST: {msg}")
            | Except.ok ast => pure ast
          let solver ← B3.Verifier.createInteractiveSolver opts.solver
          let reports ← B3.Verifier.programToSMT ast solver
          for report in reports do
            IO.println s!"\nProcedure: {report.procedureName}"
            for (result, _) in report.results do
              let marker := if result.result.isError then "✗" else "✓"
              let desc := match result.result with
                | .error .counterexample => "counterexample found"
                | .error .unknown => "unknown"
                | .error .refuted => "refuted"
                | .success .verified => "verified"
                | .success .reachable => "reachable"
                | .success .reachabilityUnknown => "reachability unknown"
              IO.println s!"  {marker} {desc}"
          pure #[]
        else
          verify pgm inputCtx proceduresToVerify opts
      catch e =>
        println! f!"{e}"
        IO.Process.exit 1
      if opts.outputSarif then
        if file.endsWith ".csimp.st" then
          println! "SARIF output is not supported for C_Simp files (.csimp.st) because location metadata is not preserved during translation to Core."
        else
          let uri := Strata.Uri.file file
          let files := Map.empty.insert uri inputCtx.fileMap
          Core.Sarif.writeSarifOutput opts.checkMode files vcResults (file ++ ".sarif")
      for vcResult in vcResults do
        let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some inputCtx.fileMap)
        println! f!"{posStr} [{vcResult.obligation.label}]: \
                      {vcResult.formatOutcome}"
      let success := vcResults.all Core.VCResult.isSuccess
      if success && !opts.checkOnly then
        println! f!"All {vcResults.size} goals passed."
      else if success && opts.checkOnly then
        println! f!"Skipping verification."
      else
        let provedGoalCount := (vcResults.filter Core.VCResult.isSuccess).size
        let failedGoalCount := (vcResults.filter Core.VCResult.isNotSuccess).size
        println! f!"Finished with {provedGoalCount} goals passed, {failedGoalCount} failed."
        IO.Process.exit 1
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
      println! f!"Finished with {errors.size} errors."
      IO.Process.exit 1

def commandGroups : List CommandGroup := [
  { name := "Core"
    commands := [verifyCommand, checkCommand, toIonCommand, printCommand, diffCommand]
    commonFlags := [includeFlag] },
  { name := "Code Generation"
    commands := [javaGenCommand] },
  { name := "Python"
    commands := [pyAnalyzeCommand, pyAnalyzeLaurelCommand,
                 pyResolveOverloadsCommand,
                 pySpecsCommand, pySpecToLaurelCommand,
                 pyAnalyzeLaurelToGotoCommand,
                 pyAnalyzeToGotoCommand,
                 pyTranslateCommand,
                 pyTranslateLaurelCommand] },
  { name := "Laurel"
    commands := [laurelAnalyzeCommand, laurelAnalyzeBinaryCommand,
                 laurelAnalyzeToGotoCommand, laurelParseCommand,
                 laurelPrintCommand, laurelToCoreCommand] },
]

def commandList : List Command :=
  commandGroups.foldl (init := []) fun acc g => acc ++ g.commands

def commandMap : Std.HashMap String Command :=
  commandList.foldl (init := {}) fun m c => m.insert c.name c

/-- Print a single flag's name and help text at the given indentation. -/
private def printFlag (indent : Nat) (flag : Flag) : IO Unit := do
  let pad := "".pushn ' ' indent
  match flag.takesArg with
  | .arg argName | .repeat argName =>
    IO.println s!"{pad}--{flag.name} <{argName}>  {flag.help}"
  | .none =>
    IO.println s!"{pad}--{flag.name}  {flag.help}"

/-- Print help for all command groups. -/
private def printGlobalHelp : IO Unit := do
  IO.println "Usage: strata <command> [flags]...\n"
  IO.println "Command-line utilities for working with Strata.\n"
  for group in commandGroups do
    IO.println s!"{group.name}:"
    for cmd in group.commands do
      let cmdLine := cmd.args.foldl (init := cmd.name) fun s a => s!"{s} <{a}>"
      IO.println s!"  {cmdLine}"
      printIndented 4 cmd.help
      let perCmdFlags := cmd.flags.filter fun f =>
        !group.commonFlags.any fun cf => cf.name == f.name
      if !perCmdFlags.isEmpty then
        IO.println ""
        IO.println "    Flags:"
        for flag in perCmdFlags do
          printFlag 6 flag
      IO.println ""
    if !group.commonFlags.isEmpty then
      IO.println "  Common flags:"
      for flag in group.commonFlags do
        printFlag 4 flag
      IO.println ""

/-- Print help for a single command. -/
private def printCommandHelp (cmd : Command) : IO Unit := do
  let cmdLine := cmd.args.foldl (init := s!"strata {cmd.name}") fun s a => s!"{s} <{a}>"
  let flagSummary := cmd.flags.foldl (init := "") fun s f =>
    match f.takesArg with
    | .arg argName | .repeat argName => s!"{s} [--{f.name} <{argName}>]"
    | .none => s!"{s} [--{f.name}]"
  IO.println s!"Usage: {cmdLine}{flagSummary}\n"
  printIndented 0 cmd.help
  if !cmd.flags.isEmpty then
    IO.println "\nFlags:"
    for flag in cmd.flags do
      printFlag 2 flag

/-- Parse interleaved flags and positional arguments. Returns the collected
    positional arguments and parsed flags. -/
private def parseArgs (cmdName : String)
    (flagMap : Std.HashMap String Flag)
    (acc : Array String) (pflags : ParsedFlags)
    (cmdArgs : List String) : IO (Array String × ParsedFlags) := do
  match cmdArgs with
  | arg :: cmdArgs =>
    if arg.startsWith "--" then
      let raw := (arg.drop 2).toString
      -- Support --flag=value syntax by splitting on first '='
      let (flagName, inlineValue) ← match raw.splitOn "=" with
        | name :: value :: rest =>
          if !rest.isEmpty then
            exitCmdFailure cmdName s!"Invalid option format: {arg}. Values must not contain '='."
          pure (name, some value)
        | _ => pure (raw, none)
      match flagMap[flagName]? with
      | some flag =>
        match flag.takesArg with
        | .none =>
          parseArgs cmdName flagMap acc (pflags.insertFlag flagName Option.none) cmdArgs
        | .arg _ =>
          match inlineValue with
          | some value =>
            parseArgs cmdName flagMap acc (pflags.insertFlag flagName (some value)) cmdArgs
          | none =>
            let value :: cmdArgs := cmdArgs
              | exitCmdFailure cmdName s!"Expected value after {arg}."
            parseArgs cmdName flagMap acc (pflags.insertFlag flagName (some value)) cmdArgs
        | .repeat _ =>
          match inlineValue with
          | some value =>
            parseArgs cmdName flagMap acc (pflags.insertRepeated flagName value) cmdArgs
          | none =>
            let value :: cmdArgs := cmdArgs
              | exitCmdFailure cmdName s!"Expected value after {arg}."
            parseArgs cmdName flagMap acc (pflags.insertRepeated flagName value) cmdArgs
      | none =>
        exitCmdFailure cmdName s!"Unknown option {arg}."
    else
      parseArgs cmdName flagMap (acc.push arg) pflags cmdArgs
  | [] =>
    pure (acc, pflags)

def main (args : List String) : IO Unit := do
  try do
    match args with
    | ["--help"] => printGlobalHelp
    | cmd :: args =>
      match commandMap[cmd]? with
      | none => exitFailure s!"Expected subcommand, got {cmd}."
      | some cmd =>
        -- Handle per-command help before parsing flags.
        if args.contains "--help" then
          printCommandHelp cmd
          return
        -- Index the command's flags by name for O(1) lookup during parsing.
        let flagMap : Std.HashMap String Flag :=
          cmd.flags.foldl (init := {}) fun m f => m.insert f.name f
        -- Split raw args into positional arguments and parsed flags.
        let (args, pflags) ← parseArgs cmd.name flagMap #[] {} args
        if p : args.size = cmd.args.length then
          cmd.callback ⟨args, p⟩ pflags
        else
          exitCmdFailure cmd.name s!"{cmd.name} expects {cmd.args.length} argument(s)."
    | [] => do
      exitFailure "Expected subcommand."
  catch e =>
    exitFailure e.toString

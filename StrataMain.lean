/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Executable with utilities for working with Strata files.
import Strata.Backends.CBMC.CollectSymbols
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.DDM.Integration.Java.Gen
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SarifOutput
import Strata.Languages.Core.ProgramEval
import Strata.Languages.Core.StatementEval
import Strata.Languages.C_Simp.Verify
import Strata.Languages.B3.Verifier.Program
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Boole.Boole
import Strata.Languages.Boole.Verify
import Strata.Languages.Python.Python
import Strata.Languages.Python.Specs.IdentifyOverloads
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Core.EntryPoint
import Strata.Transform.ProcedureInlining
import Strata.Util.IO

import Strata.SimpleAPI
import Strata.Util.Profile
import Strata.Util.Json
import Strata.DDM.BuiltinDialects
import Strata.DDM.Util.String
import Strata.Languages.Python.PyFactory
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import Strata.Languages.Python.ReadPython

open Strata

open Core (VerifyOptions VerboseMode VerificationMode CheckLevel EntryPoint)
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

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

/-- Parsed flags from the command line.  Stored as an ordered array so that
    command-line position is preserved (needed by `transform` to bind
    `--procedures`/`--functions` to the preceding `--pass`).
    For `.arg` flags that appear more than once, `getString` returns the
    **last** occurrence (last-writer-wins). -/
structure ParsedFlags where
  entries : Array (String × Option String) := #[]

namespace ParsedFlags

def getBool (pf : ParsedFlags) (name : String) : Bool :=
  pf.entries.any (·.1 == name)

def getString (pf : ParsedFlags) (name : String) : Option String :=
  -- Scan from the end so last occurrence wins.
  match pf.entries.findRev? (·.1 == name) with
  | some (_, some v) => some v
  | _ => Option.none

def getRepeated (pf : ParsedFlags) (name : String) : Array String :=
  pf.entries.foldl (init := #[]) fun acc (n, v) =>
    if n == name then match v with | some s => acc.push s | none => acc else acc

def insert (pf : ParsedFlags) (name : String) (value : Option String) : ParsedFlags :=
  { pf with entries := pf.entries.push (name, value) }

def buildDialectFileMap (pflags : ParsedFlags) : IO Strata.DialectFileMap := do
  let preloaded := Strata.Elab.LoadedDialects.builtin
    |>.addDialect! Strata.Python.Python
    |>.addDialect! Strata.Python.Specs.DDM.PythonSpecs
    |>.addDialect! Strata.Core
    |>.addDialect! Strata.Boole
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

def parseCheckMode (pflags : ParsedFlags)
    (default : VerificationMode := .deductive) : IO VerificationMode :=
  match pflags.getString "check-mode" with
  | .none => pure default
  | .some s => match VerificationMode.ofString? s with
    | .some m => pure m
    | .none => exitFailure s!"Invalid check mode: '{s}'. Must be {VerificationMode.options}."

def parseCheckLevel (pflags : ParsedFlags)
    (default : CheckLevel := .minimal) : IO CheckLevel :=
  match pflags.getString "check-level" with
  | .none => pure default
  | .some s => match CheckLevel.ofString? s with
    | .some l => pure l
    | .none => exitFailure s!"Invalid check level: '{s}'. Must be {CheckLevel.options}."

/-- Common CLI flags for VerifyOptions fields.
    Commands can append these to their own flags list.
    Note: `parseOnly`, `typeCheckOnly`, and `checkOnly` are omitted here
    because they are specific to the `verify` command. -/
def verifyOptionsFlags : List Flag := [
  { name := "check-mode",
    help := s!"Check mode: {VerificationMode.options}. Default: 'deductive'.",
    takesArg := .arg "mode" },
  { name := "check-level",
    help := s!"Check level: {CheckLevel.options}. Default: 'minimal'.",
    takesArg := .arg "level" },
  { name := "verbose", help := "Enable verbose output." },
  { name := "quiet", help := "Suppress warnings on stderr." },
  { name := "profile", help := "Print elapsed time for each pipeline step." },
  { name := "sarif", help := "Write results as SARIF to <file>.sarif." },
  { name := "solver",
    help := s!"SMT solver executable (default: {Core.defaultSolver}).",
    takesArg := .arg "name" },
  { name := "solver-timeout",
    help := "Solver timeout in seconds (default: 10).",
    takesArg := .arg "seconds" },
  { name := "vc-directory",
    help := "Store VCs in SMT-Lib format in <dir>.",
    takesArg := .arg "dir" },
  { name := "no-solve",
    help := "Generate SMT-Lib files but do not invoke the solver." },
  { name := "stop-on-first-error",
    help := "Exit after the first verification error." },
  { name := "unique-bound-names",
    help := "Use globally unique names for quantifier-bound variables." },
  { name := "use-array-theory",
    help := "Use SMT-LIB Array theory instead of axiomatized maps." },
  { name := "remove-irrelevant-axioms",
    help := "Prune irrelevant axioms: 'off', 'aggressive', or 'precise'.",
    takesArg := .arg "mode" },
  { name := "overflow-checks",
    help := "Comma-separated overflow checks to enable (signed,unsigned,float64,all,none).",
    takesArg := .arg "checks" },
  { name := "path-cap",
    help := "Maximum continuing paths between statements. 'none' (default) disables; N merges paths when count exceeds N.",
    takesArg := .arg "N|none" }
]

/-- Build a VerifyOptions from parsed CLI flags, starting from a base config.
    Fields not present in the flags keep their base values.
    Note: boolean flags can only enable a setting; a `true` in the base
    cannot be turned off from the CLI (there is no `--no-X` syntax). -/
def parseVerifyOptions (pflags : ParsedFlags)
    (base : VerifyOptions := VerifyOptions.default) : IO VerifyOptions := do
  let checkMode ← parseCheckMode pflags base.checkMode
  let checkLevel ← parseCheckLevel pflags base.checkLevel
  let solverTimeout ← match pflags.getString "solver-timeout" with
    | .none => pure base.solverTimeout
    | .some s => match s.toNat? with
      | .some n => pure n
      | .none => exitFailure s!"Invalid solver timeout: '{s}'"
  let noSolve := pflags.getBool "no-solve"
  let removeIrrelevantAxioms ← match pflags.getString "remove-irrelevant-axioms" with
    | .none => pure base.removeIrrelevantAxioms
    | .some "off" => pure .Off
    | .some "aggressive" => pure .Aggressive
    | .some "precise" => pure .Precise
    | .some s => exitFailure s!"Invalid remove-irrelevant-axioms mode: '{s}'. Must be 'off', 'aggressive', or 'precise'."
  let overflowChecks := match pflags.getString "overflow-checks" with
    | .none => base.overflowChecks
    | .some s => s.splitOn "," |>.foldl (fun acc c =>
        match c.trimAscii.toString with
        | "signed"   => { acc with signedBV := true }
        | "unsigned" => { acc with unsignedBV := true }
        | "float64"  => { acc with float64 := true }
        | "none"     => { signedBV := false, unsignedBV := false, float64 := false }
        | "all"      => { signedBV := true, unsignedBV := true, float64 := true }
        | _          => acc) { signedBV := false, unsignedBV := false, float64 := false }
  let pathCap ← match pflags.getString "path-cap" with
    | .none => pure base.pathCap
    | .some "none" => pure .none
    | .some s => match s.toNat? with
      | .some n => if n == 0 then exitFailure "--path-cap must be at least 1 or 'none'."
                   else pure (.some n)
      | .none => exitFailure s!"Invalid path-cap: '{s}'. Must be a positive number or 'none'."
  let vcDirectory := (pflags.getString "vc-directory" |>.map (⟨·⟩ : String → System.FilePath)).orElse (fun _ => base.vcDirectory)
  let skipSolver := noSolve || base.skipSolver
  if skipSolver && vcDirectory.isNone then
    exitFailure "--no-solve requires --vc-directory to specify where SMT files are stored."
  pure { base with
    verbose := if pflags.getBool "verbose" then .normal
              else if pflags.getBool "quiet" then .quiet
              else base.verbose,
    solver := pflags.getString "solver" |>.getD base.solver,
    solverTimeout,
    checkMode, checkLevel,
    stopOnFirstError := pflags.getBool "stop-on-first-error" || base.stopOnFirstError,
    uniqueBoundNames := pflags.getBool "unique-bound-names" || base.uniqueBoundNames,
    useArrayTheory := pflags.getBool "use-array-theory" || base.useArrayTheory,
    removeIrrelevantAxioms,
    outputSarif := pflags.getBool "sarif" || base.outputSarif,
    profile := pflags.getBool "profile" || base.profile,
    skipSolver,
    alwaysGenerateSMT := noSolve || base.alwaysGenerateSMT,
    overflowChecks,
    vcDirectory,
    pathCap
  }

/-- Additional CLI flags for `LaurelVerifyOptions` fields that are not already
    covered by `verifyOptionsFlags`. -/
def laurelTranslateFlags : List Flag := [
  { name := "keep-all-files",
    help := "Store intermediate Laurel and Core programs in <dir>.",
    takesArg := .arg "dir" }
]

/-- All CLI flags accepted by Laurel verify commands. -/
def laurelVerifyOptionsFlags : List Flag := verifyOptionsFlags ++ laurelTranslateFlags

/-- Build a `LaurelVerifyOptions` from parsed CLI flags. -/
def parseLaurelVerifyOptions (pflags : ParsedFlags)
    (base : LaurelVerifyOptions := default) : IO LaurelVerifyOptions := do
  let verifyOptions ← parseVerifyOptions pflags base.verifyOptions
  let keepAllFilesPrefix := (pflags.getString "keep-all-files").orElse
    (fun _ => base.translateOptions.keepAllFilesPrefix)
  let translateOptions : LaurelTranslateOptions :=
    { base.translateOptions with
      keepAllFilesPrefix
      overflowChecks := verifyOptions.overflowChecks
      profile := verifyOptions.profile }
  return { translateOptions, verifyOptions }

/-- Read and parse a Strata program file, loading the Core, C_Simp, and B3CST
    dialects. Returns the parsed program and the input context (for source
    location resolution), or an array of error messages on failure. -/
private def readStrataProgram (file : String)
    : IO (Except (Array Lean.Message) (Strata.Program × Lean.Parser.InputContext)) := do
  let text ← Strata.Util.readInputSource file
  let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
  let dctx := Elab.LoadedDialects.builtin
  let dctx := dctx.addDialect! Core
  let dctx := dctx.addDialect! Boole
  let dctx := dctx.addDialect! C_Simp
  let dctx := dctx.addDialect! B3CST
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Strata.Elab.elabProgram dctx leanEnv inputCtx with
  | .ok pgm => pure (.ok (pgm, inputCtx))
  | .error msgs => pure (.error msgs)

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
      let .isTrue mem := (inferInstance : Decidable (d.name ∈ ld.dialects))
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
        let Decidable.isTrue eq := (inferInstance : Decidable (p1.commands.size = p2.commands.size))
          | exitFailure s!"Number of commands differ {p1.commands.size} and {p2.commands.size}"
        for (c1, c2) in Array.zip p1.commands p2.commands do
          if c1 != c2 then
            exitFailure s!"Commands differ: {repr c1} and {repr c2}"
    | _, _ =>
      exitFailure "Cannot compare dialect def with another dialect/program."

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
      { isSuccess := (·.isBugFindingSuccess)
        isFailure := (·.isBugFindingFailure) }
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
  flags := verifyOptionsFlags ++ [
            { name := "spec-dir",
              help := "Directory containing compiled PySpec Ion files.",
              takesArg := .arg "dir" },
            { name := "dispatch",
              help := "Dispatch module name (e.g., servicelib).",
              takesArg := .repeat "module" },
            { name := "pyspec",
              help := "PySpec module name (e.g., servicelib.Storage).",
              takesArg := .repeat "module" },
            { name := "keep-all-files",
              help := "Store intermediate Laurel and Core programs in <dir>.",
              takesArg := .arg "dir" },
            { name := "entry-point",
              help := "Which procedures to verify: main (main fn only), roots (user procs with no user callers, default), or all (all user procs). Only valid in bugFinding mode.",
              takesArg := .arg "mode" },
            { name := "warning-summary",
              help := "Write PySpec warning summary as JSON to <file>.",
              takesArg := .arg "file" }]
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
    let warningSummaryFile := pflags.getString "warning-summary"
    let combinedLaurel ←
      match ← Strata.pythonAndSpecToLaurel filePath dispatchModules pyspecModules sourcePath
                (specDir := specDir) (profile := profile)
                (quiet := quiet)
                (warningSummaryFile := warningSummaryFile) |>.toBaseIO with
      | .ok r => pure r
      | .error (.userCode range msg) =>
        let location := if range.isNone then "" else
          match mfm with
          | some (_, fm) =>
            let pos := fm.toPosition range.start
            s!" at line {pos.line}, col {pos.column}"
          | none => ""
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

    let keepPrefix := keepDir.map (s!"{·}/{baseName}")

    let (coreProgramOption, laurelTranslateErrors, _loweredLaurel, laurelPassStats) ←
      profileStep profile "Laurel to Core translation" do
        Strata.translateCombinedLaurelWithLowered combinedLaurel
          (keepAllFilesPrefix := keepPrefix) (profile := profile)

    if profile && !laurelPassStats.data.isEmpty then
      IO.println laurelPassStats.format

    let coreProgram ←
      match coreProgramOption with
      | none =>
        exitPyAnalyzeInternalError s!"Laurel to Core translation failed: {laurelTranslateErrors}"
      | some core => pure core

    if verbose then
      IO.println "\n==== Core Program ===="
      IO.print (Core.formatProgram coreProgram)

    -- Verify using Core verifier
    -- --keep-all-files implies vc-directory if not explicitly set
    let baseVcDir := keepDir.map (fun dir => (s!"{dir}/{baseName}" : System.FilePath))
    let pyAnalyzeBase : VerifyOptions :=
      { VerifyOptions.default with
        verbose := .quiet, removeIrrelevantAxioms := .Precise,
        vcDirectory := baseVcDir }
    let options ← parseVerifyOptions pflags pyAnalyzeBase
    let isBugFinding := options.checkMode == .bugFinding
                      || options.checkMode == .bugFindingAssumingCompleteSpec

    -- Parse --entry-point flag (only supported in bug-finding modes).
    let entryPointFlag := pflags.getString "entry-point"
    let entryPoint : EntryPoint ←
      if isBugFinding then
        match entryPointFlag with
        | some s =>
          match EntryPoint.ofString? s with
          | some ep => pure ep
          | none =>
            exitPyAnalyzeUserError s!"Invalid --entry-point value '{s}'. Must be {EntryPoint.options}."
        | none => pure .roots
      else
        if entryPointFlag.isSome then
          exitPyAnalyzeUserError s!"--entry-point is unsupported in {options.checkMode} mode"
        else pure .all

    -- Pick the procedures to verify and set up inlining phases.
    let userSourcePath := sourcePath.getD filePath
    let (_, userProcNames) :=
      Strata.splitProcNames coreProgram [userSourcePath]
    let (proceduresToVerify, inlinePhases) :=
      if isBugFinding then
        let ⟨p, i⟩ := Core.chooseEntryProceduresAndBuildInlinePhases coreProgram userProcNames entryPoint
        (p, [i])
      else (userProcNames, [])

    let vcResults ← profileStep profile "SMT verification" do
      match ← Core.verifyProgram coreProgram options
                (moreFns := Strata.Python.ReFactory)
                (proceduresToVerify := some proceduresToVerify)
                (externalPhases := [Strata.frontEndPhase])
                (prefixPhases := inlinePhases)
                (keepAllFilesPrefix := keepPrefix)
                |>.toBaseIO with
      | .ok r => pure r.mergeByAssertion
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
      Core.Sarif.writeSarifOutput options.checkMode files vcResults (filePath ++ ".sarif")
    printPyAnalyzeSummary vcResults options.checkMode

def pyAnalyzeToGotoCommand : Command where
  name := "pyAnalyzeToGoto"
  args := [ "file" ]
  help := "Translate a Strata Python Ion file to CProver GOTO JSON files."
  callback := fun v _ => do
    let filePath := v[0]
    let pySourceOpt ← tryReadPythonSource filePath
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let sourceText := pySourceOpt.map (·.2)
    let newPgm ← Strata.pythonDirectToCore filePath sourcePathForMetadata
    match Core.inlineProcedures newPgm { doInline := (fun _caller callee _ => callee ≠ "main") } with
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
            with
      | .error e => exitInternalError s!"{e}"
      | .ok (ctx, liftedFuncs) =>
        let extraSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure (Lean.toJson s)
          | .error e => exitInternalError s!"{e}"
        let (symtab, goto) ← emitProcWithLifted Env procName ctx liftedFuncs extraSyms
              (moduleName := baseName)
        let symTabFile := s!"{baseName}.symtab.json"
        let gotoFile := s!"{baseName}.goto.json"
        writeJsonFile symTabFile symtab
        writeJsonFile gotoFile goto
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

def laurelAnalyzeBinaryCommand : Command where
  name := "laurelAnalyzeBinary"
  args := []
  flags := laurelVerifyOptionsFlags
  help := "Verify Laurel Ion programs read from stdin and print diagnostics. Combines multiple input files."
  callback := fun _ pflags => do
    let options ← parseLaurelVerifyOptions pflags
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let combinedProgram ← Strata.readLaurelIonProgram stdinBytes
    let diagnostics ← Strata.Laurel.verifyToDiagnosticModels combinedProgram options

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
      | .ok (r, _) => pure r
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
    let _ ← Strata.readLaurelTextFile v[0]
    IO.println "Parse successful"

def laurelAnalyzeCommand : Command where
  name := "laurelAnalyze"
  args := [ "file" ]
  flags := laurelVerifyOptionsFlags
  help := "Analyze a Laurel source file. Write diagnostics to stdout."
  callback := fun v pflags => do
    let options ← parseLaurelVerifyOptions pflags
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (vcResultsOption, errors) ← Strata.Laurel.verifyToVcResults laurelProgram options
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
    let laurelProgram ← Strata.parseLaurelText path content
    match ← Strata.Laurel.translate {} laurelProgram with
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
                with
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
        writeJsonFile symTabFile symtab
        writeJsonFile gotoFile goto
        IO.println s!"Written {symTabFile} and {gotoFile}"

def laurelPrintCommand : Command where
  name := "laurelPrint"
  args := []
  help := "Read Laurel Ion from stdin and print in concrete syntax to stdout."
  callback := fun _ _ => do
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let strataFiles ← Strata.readLaurelIonFiles stdinBytes
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
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (coreProgramOption, errors) ← Strata.Laurel.translate {} laurelProgram
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

private def validPasses :=
  "inlineProcedures, loopElim, callElim, filterProcedures, removeIrrelevantAxioms"

/-- A single transform pass together with the `--procedures`/`--functions`
    that were specified immediately after it on the command line. -/
private structure PassConfig where
  name : String
  procedures : List String := []
  functions : List String := []
deriving Inhabited

/-- Walk the ordered flag entries and bind each `--procedures`/`--functions`
    to the most recent `--pass`. -/
private def buildPassConfigs (entries : Array (String × Option String))
    : IO (Array PassConfig) := do
  let mut configs : Array PassConfig := #[]
  for (flag, value) in entries do
    match flag with
    | "pass" => configs := configs.push { name := value.getD "" }
    | "procedures" =>
      let some cur := configs.back? | exitFailure "--procedures must appear after a --pass"
      let procs := (value.getD "").splitToList (· == ',')
      configs := configs.pop.push { cur with procedures := cur.procedures ++ procs }
    | "functions" =>
      let some cur := configs.back? | exitFailure "--functions must appear after a --pass"
      let fns := (value.getD "").splitToList (· == ',')
      configs := configs.pop.push { cur with functions := cur.functions ++ fns }
    | _ => pure ()
  return configs

def transformCommand : Command where
  name := "transform"
  args := [ "file" ]
  flags := [
    { name := "pass",
      help := s!"Transform pass to apply (repeatable, applied left to right). \
               Valid passes: {validPasses}. \
               --procedures and --functions after a --pass apply to that pass.",
      takesArg := .repeat "name" },
    { name := "procedures",
      help := "Comma-separated procedure names for the preceding --pass. \
               For filterProcedures: procedures to keep. \
               For inlineProcedures: procedures to inline.",
      takesArg := .repeat "procs" },
    { name := "functions",
      help := "Comma-separated function names for the preceding --pass (used by removeIrrelevantAxioms).",
      takesArg := .repeat "funcs" }]
  help := "Apply one or more transforms to a Core program and print the result."
  callback := fun v pflags => do
    let file := v[0]
    let passConfigs ← buildPassConfigs pflags.entries
    if passConfigs.isEmpty then
      exitFailure s!"No --pass specified. Valid passes: {validPasses}."
    -- Read and parse the Core program
    let (pgm, _) ← match ← readStrataProgram file with
      | .ok r => pure r
      | .error msgs =>
        for e in msgs do println! s!"Error: {← e.toString}"
        exitFailure s!"{msgs.size} parse error(s)"
    match Strata.genericToCore pgm with
    | .error msg =>
      exitFailure msg
    | .ok initProgram =>
      -- Validate and convert pass configs to TransformPass values
      let mut passes : List Strata.Core.TransformPass := []
      for pc in passConfigs do
        match pc.name with
        | "inlineProcedures" =>
          let opts : Core.InlineTransformOptions :=
            if pc.procedures.isEmpty then {}
            else { doInline := (fun _caller callee _ => callee ∈ pc.procedures) }
          passes := passes ++ [.inlineProcedures opts]
        | "loopElim" =>
          passes := passes ++ [.loopElim]
        | "callElim" =>
          passes := passes ++ [.callElim]
        | "filterProcedures" =>
          if pc.procedures.isEmpty then
            exitFailure "filterProcedures requires --procedures"
          passes := passes ++ [.filterProcedures pc.procedures]
        | "removeIrrelevantAxioms" =>
          if pc.functions.isEmpty then
            exitFailure "removeIrrelevantAxioms requires --functions"
          passes := passes ++ [.removeIrrelevantAxioms pc.functions]
        | other =>
          exitFailure s!"Unknown pass '{other}'. Valid passes: {validPasses}."
      -- Run all passes in a single CoreTransformM chain so fresh variable
      -- counters accumulate and cached analyses are reused across passes.
      match Strata.Core.runTransforms initProgram passes with
      | .ok program => IO.print (Core.formatProgram program)
      | .error e => exitFailure s!"Transform failed: {e}"

def verifyCommand : Command where
  name := "verify"
  args := [ "file" ]
  flags := verifyOptionsFlags ++ [
    { name := "check", help := "Process up until SMT generation, but don't solve." },
    { name := "type-check", help := "Exit after semantic dialect's type inference/checking." },
    { name := "parse-only", help := "Exit after DDM parsing and type checking." },
    { name := "output-format", help := "Output format (only 'sarif' supported).", takesArg := .arg "format" },
    { name := "procedures", help := "Verify only the specified procedures (comma-separated).", takesArg := .arg "procs" }]
  help := "Verify a Strata program file (.core.st, .csimp.st, or .b3.st)."
  callback := fun v pflags => do
    let file := v[0]
    let proceduresToVerify := pflags.getString "procedures" |>.map (·.splitToList (· == ','))
    let opts ← parseVerifyOptions pflags { VerifyOptions.default with verbose := .quiet }
    let opts := { opts with
      checkOnly := pflags.getBool "check",
      typeCheckOnly := pflags.getBool "type-check",
      parseOnly := pflags.getBool "parse-only",
      outputSarif := opts.outputSarif || pflags.getString "output-format" == some "sarif" }
    let (pgm, inputCtx) ← match ← readStrataProgram file with
      | .ok r => pure r
      | .error errors =>
        for e in errors do
          let msg ← e.toString
          println! s!"Error: {msg}"
        println! f!"Finished with {errors.size} errors."
        IO.Process.exit ExitCode.userError
    println! s!"Successfully parsed."
      if opts.parseOnly then return
      if opts.typeCheckOnly then
        let ans := if file.endsWith ".csimp.st" then
                     C_Simp.typeCheck pgm opts
                   else if pgm.dialect == "Boole" then
                     Boole.typeCheck pgm opts
                   else
                     typeCheck inputCtx pgm opts
        match ans with
        | .error e =>
          println! f!"{e.formatRange (some inputCtx.fileMap) true} {e.message}"
          IO.Process.exit ExitCode.userError
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
        else if pgm.dialect == "Boole" then
          Boole.verify opts.solver pgm inputCtx proceduresToVerify opts
        else
          verify pgm inputCtx proceduresToVerify opts
      catch e =>
        println! f!"{e}"
        IO.Process.exit ExitCode.internalError
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
        IO.Process.exit ExitCode.failuresFound

def pyInterpretCommand : Command where
  name := "pyInterpret"
  args := [ "file" ]
  flags := [{ name := "fuel", help := "Maximum execution steps.", takesArg := .arg "n" },
            { name := "verbose", help := "Show the generated Core program." }]
  help := "Interpret a Python Ion program concretely (Python → Laurel → Core → execute)."
  callback := fun v pflags => do
    let filePath := v[0]
    let verbose := pflags.getBool "verbose"
    let fuel := match pflags.getString "fuel" with
      | some s => s.toNat!
      | none => 10000

    let (core, _diags) ←
      match <- pyTranslateLaurel filePath #[] #[] (specDir := ".") |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    if verbose then
      IO.println "\n==== Core Program ===="
      IO.println f!"{core}"
    let core ← match Core.typeCheck Core.VerifyOptions.quiet core
        (moreFns := Strata.Python.ReFactory) with
      | .ok prog => pure prog
      | .error e =>
        println!  s!"Core type checking failed: {e.message}"
        IO.Process.exit ExitCode.userError
    match core.run with
    | .ok E =>
      let E := Core.Statement.Command.runCall [] "__main__" [] fuel E
      match E.error with
      | none =>
        if verbose then
          IO.println s!"{Std.format E}"
          IO.println "Execution completed successfully."
      | some e =>
          IO.println s!"{Std.format e}"
          IO.Process.exit ExitCode.failuresFound
    | .error diag =>
      IO.eprintln s!"Error: {diag}"
      IO.Process.exit ExitCode.failuresFound

def commandGroups : List CommandGroup := [
  { name := "Core"
    commands := [verifyCommand, transformCommand, checkCommand, toIonCommand, printCommand, diffCommand]
    commonFlags := [includeFlag] },
  { name := "Code Generation"
    commands := [javaGenCommand] },
  { name := "Python"
    commands := [pyAnalyzeLaurelCommand,
                 pyResolveOverloadsCommand,
                 pySpecsCommand, pySpecToLaurelCommand,
                 pyAnalyzeLaurelToGotoCommand,
                 pyAnalyzeToGotoCommand,
                 pyTranslateLaurelCommand,
                 pyInterpretCommand] },
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
          parseArgs cmdName flagMap acc (pflags.insert flagName Option.none) cmdArgs
        | .arg _ =>
          match inlineValue with
          | some value =>
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
          | none =>
            let value :: cmdArgs := cmdArgs
              | exitCmdFailure cmdName s!"Expected value after {arg}."
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
        | .repeat _ =>
          match inlineValue with
          | some value =>
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
          | none =>
            let value :: cmdArgs := cmdArgs
              | exitCmdFailure cmdName s!"Expected value after {arg}."
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
      | none =>
        exitCmdFailure cmdName s!"Unknown option {arg}."
    else
      parseArgs cmdName flagMap (acc.push arg) pflags cmdArgs
  | [] =>
    pure (acc, pflags)

public
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

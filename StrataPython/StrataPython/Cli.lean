/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Cli.Framework
public import Strata.Cli.VerifyOptions
public import Strata.Backends.CBMC.CollectSymbols
public import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
public import Strata.Languages.Core.EntryPoint
public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.SarifOutput
public import Strata.Languages.Core.ProgramEval
public import Strata.Languages.Core.StatementEval
public import Strata.Pipeline.Diagnostic
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Transform.ProcedureInlining
public import Strata.Util.Json
public import StrataPython
public import StrataPython.PyFactory
public import StrataPython.Pipeline.PyAnalyzeLaurel
public import StrataPython.Specs
public import StrataPython.Specs.DDM
public import StrataPython.Specs.IdentifyOverloads
public import StrataPython.Specs.ToLaurel
public import StrataPython.ReadPython

public import StrataDDM.Util.IO
import StrataDDM.Util.String

/-! # Python CLI command definitions

Holds the 8 Python-related `Command` definitions plus their helpers.
-/

public section

open Strata
open StrataPython
open Core (VerifyOptions VerboseMode VerificationMode CheckLevel EntryPoint)
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

namespace StrataPython.Cli

/-! ## Python source helpers -/

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

/-- Try to read Python source file for source location reconstruction. -/
def tryReadPythonSource (ionPath : String) : IO (Option (String × String)) := do
  match ionPathToPythonPath ionPath with
  | none => return none
  | some pyPath =>
    try
      let content ← IO.FS.readFile pyPath
      return some (pyPath, content)
    catch _ =>
      return none

/-- Strip well-known Strata file suffixes from a path's basename. -/
def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  let suffixes := [".python.st.ion", ".py.ion", ".st.ion", ".st"]
  match suffixes.find? (name.endsWith ·) with
  | some sfx => (name.dropEnd sfx.length).toString
  | none     => name

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

Exit codes follow the common scheme (see `ExitCode`).
A successful run exits 0 with `RESULT: Analysis success` or `RESULT: Inconclusive`. -/

/-- Determines which VC results count as successes and which count as failures
    for the purposes of the `pyAnalyzeLaurel` summary and exit code. -/
structure ResultClassifier where
  isSuccess : Core.VCResult → Bool := (·.isSuccess)
  isFailure : Core.VCResult → Bool := (·.isFailure)

private def printPyAnalyzeResult (category : String) (detail : String) : IO Unit := do
  IO.println s!"DETAIL: {detail}"
  IO.println s!"RESULT: {category}"

def exitPyAnalyzeUserError {α} (message : String) : IO α := do
  printPyAnalyzeResult "User error" message
  IO.Process.exit ExitCode.userError

private def exitPyAnalyzeFailuresFound {α} (detail : String) : IO α := do
  printPyAnalyzeResult "Failures found" detail
  IO.Process.exit ExitCode.failuresFound

def exitPyAnalyzeInternalError {α} (message : String) : IO α := do
  printPyAnalyzeResult "Internal error" message
  IO.Process.exit ExitCode.internalError

def exitPyAnalyzeKnownLimitation {α} (message : String) : IO α := do
  printPyAnalyzeResult "Known limitation" message
  IO.Process.exit ExitCode.knownLimitation

/-- Print the final RESULT/DETAIL lines based on solver outcomes. -/
private def printPyAnalyzeSummary (vcResults : Array Core.VCResult)
    (checkMode : VerificationMode := .deductive) : IO Unit := do
  let classifier : ResultClassifier :=
    match checkMode with
    | .bugFinding | .bugFindingAssumingCompleteSpec =>
      { isSuccess := (·.isBugFindingSuccess)
        isFailure := (·.isBugFindingFailure) }
    | _ => {}
  let (implError, rest1) :=
    vcResults.partition (fun r => r.isImplementationError || r.hasSMTError)
  let (timeouts, classifiable) := rest1.partition (·.isTimeout)
  let (success, rest)          := classifiable.partition classifier.isSuccess
  let (failure, inconclusive)  := rest.partition classifier.isFailure
  let nUnreachable  := vcResults.filter (·.isUnreachable) |>.size
  let nImplError    := implError.size
  let nTimeout      := timeouts.size
  let nSuccess      := success.size
  let nFailure      := failure.size
  let nInconclusive := inconclusive.size
  let unreachableStr := if nUnreachable > 0 then s!", {nUnreachable} unreachable" else ""
  let implErrorStr   := if nImplError > 0   then s!", {nImplError} internal errors" else ""
  let timeoutStr     := if nTimeout > 0     then s!", {nTimeout} solver timeouts" else ""
  let counts := s!"{nSuccess} passed, {nFailure} failed, {nInconclusive} inconclusive{unreachableStr}{timeoutStr}{implErrorStr}"
  if nImplError > 0 then
    exitPyAnalyzeInternalError s!"An unexpected result was produced. {counts}"
  else if nFailure > 0 then
    exitPyAnalyzeFailuresFound counts
  else
    let label :=
      if nTimeout > 0 then "Solver timeout"
      else if nInconclusive > 0 then "Inconclusive"
      else "Analysis success"
    printPyAnalyzeResult label counts

/-- Write SMT-style user-error diagnostics to stdout and `user_errors.txt`,
    and return a human-readable location suffix (e.g., " at line 42, col 5"). -/
def reportUserCodeError (range : StrataDDM.SourceRange) (msg : String)
    (mfm : Option (String × Lean.FileMap)) (filePath : String) : IO String := do
  let location := if range.isNone then "" else
    match mfm with
    | some (_, fm) =>
      let pos := fm.toPosition range.start
      s!" at line {pos.line}, col {pos.column}"
    | none => ""
  let mut lines := #[
    s!"(set-info :file {StrataDDM.escapeSMTStringLit filePath})"
  ]
  unless range.isNone do
    lines := lines.push s!"(set-info :start {range.start})"
    lines := lines.push s!"(set-info :stop {range.stop})"
  lines := lines.push s!"(set-info :error-message {StrataDDM.escapeSMTStringLit msg})"
  for line in lines do
    IO.println line
  IO.FS.Handle.mk "user_errors.txt" .write >>= fun h =>
    for line in lines do
      h.putStrLn line
  return location

/-! ## Command definitions -/

def pySpecsCommand : _root_.Command where
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
    let warningOutput : StrataPython.WarningOutput :=
      if quiet then .none else .detail
    -- Serialize embedded dialect for Python subprocess
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
      let r ← StrataPython.pySpecsDir (events := events)
                (skipNames := skipNames)
                (modules := modules)
                (warningOutput := warningOutput)
                v[0] v[1] dialectFile |>.toBaseIO
      match r with
      | .ok () => pure ()
      | .error msg => exitFailure msg

def pyAnalyzeLaurelCommand (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn) : _root_.Command where
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
            { name := "metrics",
              help := "Write pipeline metrics (diagnostics, timing, outcome) as JSONL to <file>.",
              takesArg := .arg "file" },
            { name := "skip-verification",
              help := "Run Python-to-Laurel and Laurel-to-Core translation only (skip SMT verification).",
              takesArg := .none }]
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
    let metricsHandle ← match pflags.getString "metrics" with
      | some path => some <$> IO.FS.Handle.mk path .write
      | none => pure none

    let keepPrefix := keepDir.map (s!"{·}/{baseName}")
    let baseVcDir := keepDir.map (fun dir => (s!"{dir}/{baseName}" : System.FilePath))
    let pyAnalyzeBase : VerifyOptions :=
      { VerifyOptions.default with
        verbose := .quiet, removeIrrelevantAxioms := .Precise,
        vcDirectory := baseVcDir }
    let options ← parseVerifyOptions pflags pyAnalyzeBase
    let isBugFinding := options.checkMode == .bugFinding
                      || options.checkMode == .bugFindingAssumingCompleteSpec

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

    let outputMode : Strata.Pipeline.OutputMode :=
      if verbose then .verbose
      else if profile then .profile
      else if quiet then .quiet
      else .default
    let skipVerification := pflags.getBool "skip-verification"

    let (outcome, laurelPassStats, pctx) ← StrataPython.Pipeline.runPyAnalyzePipeline {
      filePath, specDir
      dispatchModules, pyspecModules, sourcePath
      keepAllFilesPrefix := keepPrefix
      verifyOptions := options
      entryPoint, isBugFinding
      outputMode, skipVerification
      metricsHandle, mkDischarge
    }

    let msgs ← pctx.getMessages
    if !quiet && msgs.size > 0 then
      IO.eprintln s!"{msgs.size} pipeline warning(s)"
      if verbose then
        for err in msgs do
          IO.eprintln s!"  {err.file}: {err.phase}.{err.kind}: {err.message}"

    if profile && !laurelPassStats.data.isEmpty then
      IO.println laurelPassStats.format

    let emitOutcome (resultStr : String) (exitCode : UInt8) (detail : Option String := none) : IO Unit := do
      let totalMs ← pctx.elapsedNs
      let mut fields : List (String × Lean.Json) := [
        ("type", .str "outcome"), ("result", .str resultStr),
        ("exit_code", .num exitCode.toNat), ("total_ms", .num (Strata.Pipeline.nsToMs totalMs))]
      if let some d := detail then
        fields := fields ++ [("detail", .str d)]
      pctx.emitMetric (Lean.Json.mkObj fields)

    let toolErrors ← pctx.getToolErrors
    let userErrors ← pctx.getUserCodeErrors

    if let some lastErr := toolErrors.back? then
      emitOutcome "internalError" ExitCode.internalError (detail := lastErr.message)
      exitPyAnalyzeInternalError lastErr.message
    if let some lastErr := userErrors.back? then
      emitOutcome "userError" ExitCode.userError (detail := lastErr.message)
      let location ← reportUserCodeError lastErr.loc lastErr.message mfm (sourcePath.getD filePath)
      exitPyAnalyzeUserError s!"{lastErr.message}{location}"
    match outcome with
    | .verified vcResults _coreProgram =>
      emitOutcome "verified" 0
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
      if outputSarif then
        let files := match mfm with
          | some (pyPath, fm) => Map.empty.insert (Strata.Uri.file pyPath) fm
          | none => Map.empty
        Core.Sarif.writeSarifOutput options.checkMode files vcResults (filePath ++ ".sarif")
      printPyAnalyzeSummary vcResults options.checkMode
    | .failed =>
      let knownLimitations := msgs.filter (·.kind.impact == .knownLimitation)
      match knownLimitations.back? with
      | some lastErr =>
        emitOutcome "knownLimitation" ExitCode.knownLimitation (detail := lastErr.message)
        exitPyAnalyzeKnownLimitation lastErr.message
      | none =>
        let msg : String := match msgs.back? with
          | some m => m.message
          | none => "Pipeline aborted"
        emitOutcome "internalError" ExitCode.internalError (detail := msg)
        exitPyAnalyzeInternalError msg

def pyAnalyzeToGotoCommand : _root_.Command where
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
    let newPgm ← StrataPython.pythonDirectToCore filePath sourcePathForMetadata
    match ← (Strata.Core.runTransforms newPgm [Strata.Core.passInlineExcept ["main"]]).toBaseIO with
    | .error e => exitInternalError (toString e)
    | .ok (newPgm, _) =>
      let Ctx := { Lambda.LContext.default with functions := StrataPython.PythonFactory, knownTypes := Core.KnownTypes }
      let Env := Lambda.TEnv.default
      let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env newPgm with
        | .ok r => pure r
        | .error e => exitInternalError s!"{e.format none}"
      let tcPgm : Core.Program := tcPgm
      let some mainDecl := tcPgm.decls.find? fun (d : Core.Decl) =>
          match d with
          | .proc p _ => Core.CoreIdent.toPretty p.header.name == "main"
          | _ => false
        | exitInternalError "No main procedure found"
      let some p := mainDecl.getProc?
        | exitInternalError "main is not a procedure"
      let baseName := deriveBaseName filePath
      let procName := Core.CoreIdent.toPretty p.header.name
      let axioms := tcPgm.decls.filterMap fun (d : Core.Decl) => d.getAxiom?
      let distincts := tcPgm.decls.filterMap fun (d : Core.Decl) => match d with
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

def pyTranslateLaurelCommand : _root_.Command where
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
      match ← StrataPython.pyTranslateLaurel v[0] dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    IO.print coreProgram

def pyAnalyzeLaurelToGotoCommand : _root_.Command where
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
    let (coreProgram, _laurelTranslateErrors) ←
      match ← StrataPython.pyTranslateLaurel filePath dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    let sourceText := (← tryReadPythonSource filePath).map (·.2)
    let baseName := deriveBaseName filePath
    match ← Strata.inlineCoreToGotoFiles coreProgram baseName sourceText
              (factory := StrataPython.PythonFactory) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => exitFailure msg

def pySpecToLaurelCommand : _root_.Command where
  name := "pySpecToLaurel"
  args := [ "python_path", "strata_path" ]
  help := "Translate a PySpec Ion file to Laurel declarations. The Ion file must already exist."
  callback := fun v _ => do
    let pythonFile : System.FilePath := v[0]
    let strataDir : System.FilePath := v[1]
    let some mod := pythonFile.fileStem
      | exitFailure s!"No stem {pythonFile}"
    let some mod := StrataPython.ModuleName.ofString? mod
      | exitFailure s!"Invalid module {mod}"
    let ionFile := strataDir / mod.strataFileName
    let sigs ←
      match ← StrataPython.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => exitFailure s!"Could not read {ionFile}: {msg}"
    let result := StrataPython.Specs.ToLaurel.signaturesToLaurel pythonFile sigs mod
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

def pyResolveOverloadsCommand : _root_.Command where
  name := "pyResolveOverloads"
  args := [ "python_path", "dispatch_ion" ]
  help := "Identify which overloaded service modules a \
    Python program uses. Prints one module name per \
    line to stdout."
  callback := fun v _ => do
    let pythonFile : System.FilePath := v[0]
    let dispatchPath := v[1]
    let pctx ← Strata.Pipeline.PipelineContext.create
    let overloads ← match ← (readDispatchOverloads pctx #[dispatchPath]).toBaseIO with
      | .ok r => pure r
      | .error () =>
        for m in ← pctx.getMessages do
          IO.eprintln s!"{m}"
        exitFailure "readDispatchOverloads: fatal error"
    let stmts ←
      IO.FS.withTempFile fun _handle dialectFile => do
        IO.FS.writeBinFile dialectFile
          StrataPython.Python.toIon
        match ← StrataPython.pythonToStrata dialectFile pythonFile |>.toBaseIO with
        | .ok s => pure s
        | .error msg => exitFailure msg
    let state :=
      StrataPython.Specs.IdentifyOverloads.resolveOverloads
        overloads stmts
    for w in state.warnings do
      IO.eprintln s!"warning: {w}"
    let sorted := state.modules.toArray.qsort (· < ·)
    for m in sorted do
      IO.println m

def pyInterpretCommand : _root_.Command where
  name := "pyInterpret"
  args := [ "file" ]
  flags := [{ name := "fuel", help := "Maximum execution steps.", takesArg := .arg "n" }]
            ++ laurelTranslateFlags
  help := "Interpret a Python Ion program concretely (Python → Laurel → Core → execute)."
  callback := fun v pflags => do
    let filePath := v[0]
    let keepDir := pflags.getString "keep-all-files"
    let fuel ← match pflags.getString "fuel" with
      | some s => match s.toNat? with
        | .some n => pure n
        | .none => exitFailure s!"Invalid fuel: '{s}'"
      | none => pure 10000

    let quietCtx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    let (core, _diags) ←
      match ← (StrataPython.pythonAndSpecToLaurel filePath (specDir := ".")).run quietCtx |>.toBaseIO with
      | .ok (laurel, gradualConfig) =>
        if let some dir := keepDir then
          IO.FS.createDirAll dir
          IO.FS.writeFile (dir ++ "/laurel.st") (toString (Std.format laurel))
        match ← StrataPython.translateCombinedLaurel laurel (gradualConfig := some gradualConfig) with
        | (some core, diags) => pure (core, diags)
        | (none, diags) => exitFailure s!"Laurel to Core translation failed: {diags}"
      | .error () =>
        let msgs ← quietCtx.getMessages
        let detail := match msgs.back? with | some m => m.message | none => "Pipeline aborted"
        exitFailure detail
    if let some dir := keepDir then
      IO.FS.writeFile (dir ++ "/core.st") (toString (Std.format core))
    let core ← match Core.typeCheck Core.VerifyOptions.quiet core
        (moreFns := StrataPython.ReFactory) with
      | .ok prog => pure prog
      | .error e =>
        println!  s!"Core type checking failed: {e.message}"
        IO.Process.exit ExitCode.userError
    match core.run with
    | .ok E =>
      let mainProc := Core.Program.Procedure.find? core ⟨"__main__", ()⟩
      let outputNames := match mainProc with
        | some p => p.header.outputs.keys.map (·.name)
        | none => []
      let (lhs, exprEnv) := Core.Env.genVars outputNames E.exprEnv
      let E := { E with exprEnv }
      let E := Core.Statement.Command.runCall lhs "__main__" [] fuel E
      match E.error with
      | none =>
        IO.println "Execution completed successfully."
      | some e =>
          IO.println s!"{Std.format e}"
          IO.Process.exit ExitCode.failuresFound
    | .error diag =>
      IO.eprintln s!"Error: {diag}"
      IO.Process.exit ExitCode.failuresFound

end StrataPython.Cli

end -- public section

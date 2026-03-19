/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable with utilities for working with Strata files.
import Strata.DDM.Integration.Java.Gen
import Strata.Languages.Core.Options
import Strata.Languages.Core.SarifOutput
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
import Strata.Transform.ProcedureInlining
import Strata.Languages.Python.CorePrelude
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Languages.Python.PythonLaurelCorePrelude
import Strata.Backends.CBMC.CollectSymbols
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline

import Strata.SimpleAPI

open Strata

open Core (VerifyOptions VerboseMode VerificationMode CheckLevel)

def exitFailure {α} (message : String) (hint : String := "strata --help") : IO α := do
  IO.eprintln s!"Exception: {message}\n\nRun {hint} for additional help."
  IO.Process.exit 1

/-- Exit with code 1 for user code errors (detected bugs in the Python source). -/
def exitUserCodeError {α} (message : String) : IO α := do
  IO.eprintln s!"❌ {message}"
  IO.Process.exit 1

/-- Exit with code 2 for internal errors (tool limitations or crashes). -/
def exitInternalError {α} (message : String) : IO α := do
  IO.eprintln s!"Exception: {message}"
  IO.Process.exit 2

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
        | exitFailure "Internal error reading file."
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

def readPythonStrata (strataPath : String) : IO Strata.Program := do
  let bytes ← Strata.Util.readBinInputSource strataPath
  if ! Ion.isIonFile bytes then
    exitFailure s!"pyAnalyze expected Ion file"
  match Strata.Program.fromIon Strata.Python.Python_map Strata.Python.Python.name bytes with
  | .ok pgm => pure pgm
  | .error msg => exitFailure msg

def pySpecsCommand : Command where
  name := "pySpecs"
  args := [ "python_path", "strata_path" ]
  flags := [
    { name := "quiet", help := "Suppress default logging." },
    { name := "log", help := "Enable logging for an event type.",
      takesArg := .repeat "event" },
    { name := "skip",
      help := "Skip a top-level definition (module.name). Overloads are kept.",
      takesArg := .repeat "name" }
  ]
  help := "Translate a Python specification (.py) file into Strata DDM Ion format. Creates the output directory if needed. (Experimental)"
  callback := fun v pflags => do
    let quiet := pflags.getBool "quiet"
    let mut events : Std.HashSet String := {}
    if !quiet then
      events := events.insert "import"
    for e in pflags.getRepeated "log" do
      events := events.insert e
    let skipNames := pflags.getRepeated "skip"
    let warningOutput : Strata.WarningOutput :=
      if quiet then .none else .detail
    -- Serialize embedded dialect for Python subprocess
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
      let r ← Strata.pySpecs (events := events)
                (skipNames := skipNames)
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
    let pgm ← readPythonStrata v[0]
    let preludePgm := Strata.Python.Core.prelude
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures pgm preludePgm
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

def pyAnalyzeCommand : Command where
  name := "pyAnalyze"
  args := [ "file" ]
  flags := [{ name := "verbose", help := "Enable verbose output." },
            { name := "sarif", help := "Write results as SARIF to <file>.sarif." }]
  help := "Verify a Python Ion program. Translates to Core, inlines procedures, and runs SMT verification."
  callback := fun v pflags => do
    let verbose := pflags.getBool "verbose"
    let outputSarif := pflags.getBool "sarif"
    let filePath := v[0]
    let pgm ← readPythonStrata filePath
    -- Try to read the Python source for line number conversion
    let pySourceOpt ← tryReadPythonSource filePath
    if verbose then
      IO.print pgm
    let preludePgm := Strata.Python.Core.prelude
    -- Use the Python source path if available, otherwise fall back to Ion path
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures pgm preludePgm sourcePathForMetadata
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    if verbose then
      IO.print newPgm
    match Core.Transform.runProgram (targetProcList := .none)
          (Core.ProcedureInlining.inlineCallCmd
            (doInline := λ name _ => name ≠ "main"))
          newPgm .emp with
    | ⟨.error e, _⟩ => panic! e
    | ⟨.ok (_changed, newPgm), _⟩ =>
      if verbose then
        IO.println "Inlined: "
        IO.print newPgm
      let solverName : String := "Strata/Languages/Python/z3_parallel.py"
      let verboseMode := VerboseMode.ofBool verbose
      let options :=
              { VerifyOptions.default with
                stopOnFirstError := false,
                verbose := verboseMode,
                removeIrrelevantAxioms := true,
                solver := solverName }
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
        s := s ++ s!"\n{locationPrefix}{vcResult.obligation.label}: \
                      {outcomeStr}{locationSuffix}\n"
      IO.println s
      -- Output in SARIF format if requested
      if outputSarif then
        let files := match mfm with
          | some (pyPath, fm) => Map.empty.insert (Strata.Uri.file pyPath) fm
          | none => Map.empty
        Core.Sarif.writeSarifOutput .deductive files vcResults (filePath ++ ".sarif")

def pyAnalyzeLaurelCommand : Command where
  name := "pyAnalyzeLaurel"
  args := [ "file" ]
  flags := [{ name := "verbose", help := "Enable verbose output." },
            { name := "pyspec",
              help := "Add PySpec-derived Laurel declarations.",
              takesArg := .repeat "ion_file" },
            { name := "dispatch",
              help := "Extract overload dispatch table from a \
                PySpec Ion file (no Laurel translation).",
              takesArg := .repeat "ion_file" },
            { name := "sarif", help := "Write results as SARIF to <file>.sarif." },
            { name := "vc-directory",
              help := "Store VCs in SMT-Lib format in <dir>.",
              takesArg := .arg "dir" },
            checkModeFlag, checkLevelFlag]
  help := "Verify a Python Ion program via the Laurel pipeline. Translates Python to Laurel to Core, then runs SMT verification."
  callback := fun v pflags => do
    let verbose := pflags.getBool "verbose"
    let outputSarif := pflags.getBool "sarif"
    let filePath := v[0]
    let pySourceOpt ← tryReadPythonSource filePath

    if verbose then
      let pgm ← readPythonStrata filePath
      IO.println "==== Python AST ===="
      IO.print pgm

    let dispatchFiles := pflags.getRepeated "dispatch"
    let pyspecFiles := pflags.getRepeated "pyspec"
    let sourcePath := pySourceOpt.map (·.1)
    -- Build FileMap for source position resolution.
    let mfm : Option (String × Lean.FileMap) := match pySourceOpt with
      | some (pyPath, srcText) => some (pyPath, .ofString srcText)
      | none => none
    let combinedLaurel ←
      match ← Strata.pyAnalyzeLaurel filePath dispatchFiles pyspecFiles sourcePath |>.toBaseIO with
      | .ok r => pure r
      | .error (.userCode range msg) =>
        let location := if range.isNone then "" else
          match mfm with
          | some (_, fm) =>
            let pos := fm.toPosition range.start
            s!" at line {pos.line}, col {pos.column}"
          | none => ""
        exitUserCodeError s!"{msg}{location}"
      | .error (.internal msg) => exitInternalError msg

    if verbose then
      IO.println "\n==== Laurel Program ===="
      IO.println f!"{combinedLaurel}"

    let (coreProgramOption, laurelTranslateErrors) := Strata.translateCombinedLaurel combinedLaurel
    let coreProgram ←
      match coreProgramOption with
      | none =>
        exitInternalError s!"Laurel to Core translation failed: {laurelTranslateErrors}"
      | some core => pure core

    if verbose then
      IO.println "\n==== Core Program ===="
      IO.print coreProgram

    -- Verify using Core verifier
    let checkMode ← parseCheckMode pflags
    let checkLevel ← parseCheckLevel pflags
    let baseOptions : VerifyOptions :=
      { VerifyOptions.default with
        stopOnFirstError := false, verbose := .quiet, solver := "z3",
        checkMode := checkMode, checkLevel := checkLevel }
    let options : VerifyOptions := match pflags.getString "vc-directory" with
      | .some dir => { baseOptions with vcDirectory := some (dir : System.FilePath) }
      | .none => baseOptions
    let vcResults ←
      match ← Strata.verifyCore coreProgram options |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitInternalError msg

    -- Print results
    if !laurelTranslateErrors.isEmpty then
      IO.println "\n==== Errors ===="
      for err in laurelTranslateErrors do
        IO.println err

    -- Print results
    IO.println "\n==== Verification Results ===="
    let mut s := ""
    for vcResult in vcResults do
      let (locationPrefix, locationSuffix) := match Imperative.getFileRange vcResult.obligation.metadata with
        | some fr =>
          if fr.range.isNone then ("", "")
          else
            match mfm with
            | some (_, fm) =>
              match fr.file with
              | .file "" =>
                if vcResult.isFailure then
                  (s!"Assertion failed in prelude file: ", "")
                else
                  ("", s!" (in prelude file)")
              | .file path =>
                let pos := fm.toPosition fr.range.start
                if vcResult.isFailure then
                  (s!"Assertion failed at line {pos.line}, col {pos.column}: ", "")
                else
                  ("", s!" (at line {pos.line}, col {pos.column})")
            | none =>
              if vcResult.isFailure then
                (s!"Assertion failed: ", "")
              else
                ("", "")
        | none => ("", "")
      let outcomeStr := vcResult.formatOutcome
      s := s ++ s!"{locationPrefix}{vcResult.obligation.label}: \
                    {outcomeStr}{locationSuffix}\n"
    IO.println s
    -- Output in SARIF format if requested
    if outputSarif then
      let files := match mfm with
        | some (pyPath, fm) => Map.empty.insert (Strata.Uri.file pyPath) fm
        | none => Map.empty
      Core.Sarif.writeSarifOutput checkMode files vcResults (filePath ++ ".sarif")

private def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  if name.endsWith ".python.st.ion" then (name.dropEnd 14).toString
  else if name.endsWith ".py.ion" then (name.dropEnd 7).toString
  else if name.endsWith ".st.ion" then (name.dropEnd 7).toString
  else if name.endsWith ".st" then (name.dropEnd 3).toString
  else name

def pyAnalyzeToGotoCommand : Command where
  name := "pyAnalyzeToGoto"
  args := [ "file" ]
  help := "Translate a Strata Python Ion file to CProver GOTO JSON files."
  callback := fun v _ => do
    let filePath := v[0]
    let pgm ← readPythonStrata filePath
    let pySourceOpt ← tryReadPythonSource filePath
    let preludePgm := Strata.Python.Core.prelude
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let bpgm := Strata.pythonToCore Strata.Python.coreSignatures pgm preludePgm sourcePathForMetadata
    let sourceText := pySourceOpt.map (·.2)
    let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
    match Core.Transform.runProgram (targetProcList := .none)
          (Core.ProcedureInlining.inlineCallCmd
            (doInline := λ name _ => name ≠ "main"))
          newPgm .emp with
    | ⟨.error e, _⟩ => panic! e
    | ⟨.ok (_changed, newPgm), _⟩ =>
      -- Type-check the full program (registers Python types like ExceptOrNone)
      let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
      let Env := Lambda.TEnv.default
      let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env newPgm with
        | .ok r => pure r
        | .error e => panic! s!"{e.format none}"
      -- Find the main procedure
      let some mainDecl := tcPgm.decls.find? fun d =>
          match d with
          | .proc p _ => Core.CoreIdent.toPretty p.header.name == "main"
          | _ => false
        | panic! "No main procedure found"
      let some p := mainDecl.getProc?
        | panic! "main is not a procedure"
      -- Translate procedure to GOTO (mirrors CoreToGOTO.transformToGoto post-typecheck logic)
      let baseName := deriveBaseName filePath
      let procName := Core.CoreIdent.toPretty p.header.name
      let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
      let distincts := tcPgm.decls.filterMap fun d => match d with
        | .distinct name es _ => some (name, es) | _ => none
      match procedureToGotoCtx Env p sourceText (axioms := axioms) (distincts := distincts)
            (varTypes := tcPgm.getVarTy?) with
      | .error e => panic! s!"{e}"
      | .ok (ctx, liftedFuncs) =>
        let extraSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure (Lean.toJson s)
          | .error e => panic! s!"{e}"
        let (symtab, goto) ← emitProcWithLifted Env procName ctx liftedFuncs extraSyms
        let symTabFile := s!"{baseName}.symtab.json"
        let gotoFile := s!"{baseName}.goto.json"
        IO.FS.writeFile symTabFile symtab.pretty
        IO.FS.writeFile gotoFile goto.pretty
        IO.println s!"Written {symTabFile} and {gotoFile}"

def pyTranslateLaurelCommand : Command where
  name := "pyTranslateLaurel"
  args := [ "file" ]
  flags := [{ name := "pyspec",
              help := "Add PySpec-derived Laurel declarations.",
              takesArg := .repeat "ion_file" },
            { name := "dispatch",
              help := "Extract overload dispatch table from a \
                PySpec Ion file (no Laurel translation).",
              takesArg := .repeat "ion_file" }]
  help := "Translate a Strata Python Ion file through Laurel to Strata Core. Write results to stdout."
  callback := fun v pflags => do
    let dispatchFiles := pflags.getRepeated "dispatch"
    let pyspecFiles := pflags.getRepeated "pyspec"
    let coreProgram ←
      match ← Strata.pyTranslateLaurel v[0] dispatchFiles pyspecFiles |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    IO.print coreProgram

def pyAnalyzeLaurelToGotoCommand : Command where
  name := "pyAnalyzeLaurelToGoto"
  args := [ "file" ]
  flags := [{ name := "pyspec",
              help := "Add PySpec-derived Laurel declarations.",
              takesArg := .repeat "ion_file" },
            { name := "dispatch",
              help := "Extract overload dispatch table from a \
                PySpec Ion file (no Laurel translation).",
              takesArg := .repeat "ion_file" }]
  help := "Translate a Strata Python Ion file through Laurel to CProver GOTO JSON files."
  callback := fun v pflags => do
    let filePath := v[0]
    let dispatchFiles := pflags.getRepeated "dispatch"
    let pyspecFiles := pflags.getRepeated "pyspec"
    let (coreProgram, laurelTranslateErrors) ←
      match ← Strata.pyTranslateLaurel filePath dispatchFiles pyspecFiles |>.toBaseIO with
      | .ok r => pure r
      | .error msg => exitFailure msg
    let sourceText := (← tryReadPythonSource filePath).map (·.2)
    let baseName := deriveBaseName filePath
    match ← Strata.inlineCoreToGotoFiles coreProgram baseName sourceText |>.toBaseIO with
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
    let result := Strata.Python.Specs.ToLaurel.signaturesToLaurel pythonFile sigs
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
          | .error e => panic! s!"{e.format none}"
        let procs := tcPgm.decls.filterMap fun d => d.getProc?
        let funcs := tcPgm.decls.filterMap fun d =>
          match d.getFunc? with
          | some f =>
            let name := Core.CoreIdent.toPretty f.name
            if f.body.isSome && f.typeArgs.isEmpty
              && name != "Int.DivT" && name != "Int.ModT"
            then some f else none
          | none => none
        if procs.isEmpty && funcs.isEmpty then panic! "No procedures or functions found"
        let baseName := deriveBaseName path.toString
        let typeSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure s
          | .error e => panic! s!"{e}"
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
          | .error e => panic! s!"{e}"
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
          | .error e => panic! s!"{e}"
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
        let symtab := Lean.Json.mkObj dedupPairs
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

def commandGroups : List CommandGroup := [
  { name := "Core"
    commands := [checkCommand, toIonCommand, printCommand, diffCommand]
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
      let flagName := (arg.drop 2).toString
      match flagMap[flagName]? with
      | some flag =>
        match flag.takesArg with
        | .none =>
          parseArgs cmdName flagMap acc (pflags.insertFlag flagName Option.none) cmdArgs
        | .arg _ =>
          let value :: cmdArgs := cmdArgs
            | exitCmdFailure cmdName s!"Expected value after {arg}."
          parseArgs cmdName flagMap acc (pflags.insertFlag flagName (some value)) cmdArgs
        | .repeat _ =>
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

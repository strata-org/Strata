/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable with utilities for working with Strata files.
import Strata.DDM.Integration.Java.Gen
import Strata.Languages.Core.SarifOutput
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Python.Python
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Transform.ProcedureInlining
import Strata.Languages.Python.CorePrelude
import Strata.Languages.Python.PythonLaurelCorePrelude

def exitFailure {α} (message : String) (hint : String := "strata --help") : IO α := do
  IO.eprintln s!"Exception: {message}\n\nRun {hint} for additional help."
  IO.Process.exit 1

def exitCmdFailure {α} (cmdName : String) (message : String) : IO α :=
  exitFailure message (hint := s!"strata {cmdName} --help")

namespace Strata

def asText {m} [Monad m] [MonadExcept String m] (path : System.FilePath) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s =>
    pure s
  | none =>
    throw s!"{path} is not an Ion file and contains non UTF-8 data"

def mkErrorReport (path : System.FilePath) (errors : Array Lean.Message) : BaseIO String := do
  let msg : String := s!"{errors.size} error(s) reading {path}:\n"
  let msg ← errors.foldlM (init := msg) fun msg e =>
    return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
  return toString msg

inductive DialectOrProgram
| dialect (d : Dialect)
| program (pgm : Program)

end Strata

def readStrataText (fm : Strata.DialectFileMap) (input : System.FilePath) (bytes : ByteArray)
    : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let contents ←
    match Strata.asText input bytes with
    | Except.ok c => pure c
    | Except.error msg => exitFailure msg
  let inputContext := Strata.Parser.stringInputContext input contents
  let (header, errors, startPos) := Strata.Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    exitFailure  (← Strata.mkErrorReport input errors)
  match header with
  | .program _ dialect =>
    let dialects ←
      match ← Strata.Elab.loadDialect fm .builtin dialect with
      | (dialects, .ok _) => pure dialects
      | (_, .error msg) => exitFailure msg
    let .isTrue mem := inferInstanceAs (Decidable (dialect ∈ dialects.dialects))
      | panic! "internal: loadDialect failed"
    match Strata.Elab.elabProgramRest dialects leanEnv inputContext dialect mem startPos with
    | .ok program => pure (dialects, .program program)
    | .error errors => exitFailure (← Strata.mkErrorReport input errors)
  | .dialect stx dialect =>
    let (loaded, d, s) ←
      Strata.Elab.elabDialectRest fm .builtin #[] inputContext stx dialect startPos
    if s.errors.size > 0 then
      exitFailure (← Strata.mkErrorReport input s.errors)
    pure (loaded.addDialect! d, .dialect d)

def fileReadError {α} (path : System.FilePath) (msg : String) : IO α := do
  IO.eprintln s!"Error reading {path}:"
  IO.eprintln s!"  {msg}\n"
  IO.eprintln s!"Either the file is invalid or there is a bug in Strata."
  IO.Process.exit 1

def readStrataIon (fm : Strata.DialectFileMap) (path : System.FilePath) (bytes : ByteArray) : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let (hdr, frag) ←
    match Strata.Ion.Header.parse bytes with
    | .error msg =>
      exitFailure msg
    | .ok p =>
      pure p
  match hdr with
  | .dialect dialect =>
    match ← Strata.Elab.loadDialectFromIonFragment fm .builtin #[] dialect frag with
    | (_, .error msg) =>
      fileReadError path msg
    | (dialects, .ok d) =>
      pure (dialects, .dialect d)
  | .program dialect => do
    let dialects ←
      match ← Strata.Elab.loadDialect fm .builtin dialect with
      | (loaded, .ok _) => pure loaded
      | (_, .error msg) => exitFailure msg
    let .isTrue mem := inferInstanceAs (Decidable (dialect ∈ dialects.dialects))
      | panic! "loadDialect failed"
    let dm := dialects.dialects.importedDialects dialect mem
    match Strata.Program.fromIonFragment frag dm dialect with
    | .ok pgm =>
      pure (dialects, .program pgm)
    | .error msg =>
      fileReadError path msg

def readFile (fm : Strata.DialectFileMap) (path : System.FilePath) : IO (Strata.Elab.LoadedDialects × Strata.DialectOrProgram) := do
  let bytes ← Strata.Util.readBinInputSource path.toString
  let displayPath : System.FilePath := Strata.Util.displayName path.toString
  if Ion.isIonFile bytes then
    readStrataIon fm displayPath bytes
  else
    readStrataText fm displayPath bytes

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
  let mut sp : Strata.DialectFileMap := {}
  for path in pflags.getRepeated "include" do
    match ← sp.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok sp' => sp := sp'
  return sp

end ParsedFlags

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
    let _ ← readFile fm v[0]
    pure ()

def toIonCommand : Command where
  name := "toIon"
  args := [ "input", "output" ]
  flags := [includeFlag]
  help := "Convert a Strata text file to Ion binary format."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap
    let (_, pd) ← readFile searchPath v[0]
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
    let (ld, pd) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      let .isTrue mem := inferInstanceAs (Decidable (d.name ∈ ld.dialects))
        | IO.eprintln s!"Internal error reading file."
          return
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
    let ⟨_, p1⟩ ← readFile fm v[0]
    let ⟨_, p2⟩ ← readFile fm v[1]
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
  help := "Translate a Python specification (.py) file into Strata DDM Ion format. Creates the output directory if needed. (Experimental)"
  callback := fun v _ => do
    -- Serialize embedded dialect for Python subprocess
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
      let pythonFile : System.FilePath := v[0]
      let strataDir : System.FilePath := v[1]
      if (←pythonFile.metadata).type != .file then
        exitFailure s!"Expected Python to be a regular file."
      match ←strataDir.metadata |>.toBaseIO with
      | .ok md =>
        if md.type != .dir then
          exitFailure s!"Expected Strata to be a directory."
      | .error _ =>
        IO.FS.createDir strataDir
      let r ← Strata.Python.Specs.translateFile
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := pythonFile) |>.toBaseIO

      let sigs ←
        match r with
        | .ok t => pure t
        | .error msg => exitFailure msg
      let some mod := pythonFile.fileStem
        | exitFailure s!"No stem {pythonFile}"
      let .ok mod := Strata.Python.Specs.ModuleName.ofString mod
        | exitFailure s!"Invalid module {mod}"
      let strataFile := strataDir / mod.strataFileName
      Strata.Python.Specs.writeDDM strataFile sigs

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
  else
    none

/-- Try to read Python source file and create a FileMap for line/column conversion -/
def tryReadPythonSource (ionPath : String) : IO (Option (String × Lean.FileMap)) := do
  match ionPathToPythonPath ionPath with
  | none => return none
  | some pyPath =>
    try
      let content ← IO.FS.readFile pyPath
      let fileMap := Lean.FileMap.ofString content
      return some (pyPath, fileMap)
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
              { Options.default with
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
      let mut s := ""
      for vcResult in vcResults do
        -- Build location string based on available metadata
        let (locationPrefix, locationSuffix) := match Imperative.getFileRange vcResult.obligation.metadata with
          | some fr =>
            if fr.range.isNone then ("", "")
            else
              -- Convert byte offset to line/column if we have the source
              match pySourceOpt with
              | some (pyPath, fileMap) =>
                -- Check if this metadata is from the Python source (not CorePrelude)
                match fr.file with
                | .file path =>
                  if path == pyPath then
                    let pos := fileMap.toPosition fr.range.start
                    -- For failures, show at beginning; for passes, show at end
                    match vcResult.result with
                    | .fail => (s!"Assertion failed at line {pos.line}, col {pos.column}: ", "")
                    | _ => ("", s!" (at line {pos.line}, col {pos.column})")
                  else
                    -- From CorePrelude or other source, show byte offsets
                    match vcResult.result with
                    | .fail => (s!"Assertion failed at byte {fr.range.start}: ", "")
                    | _ => ("", s!" (at byte {fr.range.start})")
              | none =>
                match vcResult.result with
                | .fail => (s!"Assertion failed at byte {fr.range.start}: ", "")
                | _ => ("", s!" (at byte {fr.range.start})")
          | none => ("", "")
        s := s ++ s!"\n{locationPrefix}{vcResult.obligation.label}: {Std.format vcResult.result}{locationSuffix}\n"
      IO.println s
      -- Output in SARIF format if requested
      if outputSarif then
        let files := match pySourceOpt with
          | some (pyPath, fileMap) => Map.empty.insert (Strata.Uri.file pyPath) fileMap
          | none => Map.empty
        Core.Sarif.writeSarifOutput files vcResults (filePath ++ ".sarif")

/-- Result of building the PySpec-augmented prelude. -/
structure PySpecPrelude where
  corePrelude : Core.Program
  overloads : Strata.Python.Specs.ToLaurel.OverloadTable

/-- Build the Core prelude augmented with declarations from PySpec Ion files.
    Each Ion file is translated PySpec → Laurel → Core, and the resulting declarations
    are appended to the base prelude (with duplicates filtered out).
    Also accumulates overload dispatch tables. -/
def buildPySpecPrelude (pyspecPaths : Array String) : IO PySpecPrelude := do
  -- Laurel.translate prepends corePrelude.decls to every output.
  -- Add them once here and strip the prefix from each translated result.
  -- Accumulate into an Array for efficient appending; build Core.Program at the end.
  let laurelPreludeSize := Strata.Laurel.corePrelude.decls.length
  let mut preludeDecls : Array Core.Decl :=
    Strata.Python.Core.PythonLaurelPrelude.decls.toArray ++ Strata.Laurel.corePrelude.decls.toArray
  let mut existingNames : Std.HashSet String :=
    preludeDecls.foldl (init := {}) fun s d =>
      (Core.Decl.names d).foldl (init := s) fun s n => s.insert n.name
  let mut allOverloads : Strata.Python.Specs.ToLaurel.OverloadTable := {}
  for ionPath in pyspecPaths do
    let ionFile : System.FilePath := ionPath
    let some mod := ionFile.fileStem
      | exitFailure s!"No stem {ionFile}"
    let .ok _mod := Strata.Python.Specs.ModuleName.ofString mod
      | exitFailure s!"Invalid module {mod}"
    let sigs ←
      match ← Strata.Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => exitFailure s!"Could not read {ionFile}: {msg}"
    let result := Strata.Python.Specs.ToLaurel.signaturesToLaurel ionPath sigs
    if result.errors.size > 0 then
      IO.eprintln s!"{result.errors.size} PySpec translation warning(s) for {ionPath}:"
      for err in result.errors do
        IO.eprintln s!"  {err.file}: {err.message}"
    -- Merge overload table entries
    for (funcName, overloads) in result.overloads do
      let existing := allOverloads.getD funcName {}
      allOverloads := allOverloads.insert funcName
        (overloads.fold (init := existing) fun acc k v => acc.insert k v)
    match Strata.Laurel.translate result.program Strata.Python.CorePrelude_functions with
    | .error diagnostics =>
      exitFailure s!"PySpec Laurel to Core translation failed for {ionPath}: {diagnostics}"
    | .ok (coreSpec, _modifiesDiags) =>
      -- Strip the Laurel corePrelude prefix (always emitted by Laurel.translate)
      let pyspecDecls := coreSpec.decls.drop laurelPreludeSize
      -- Register new names, failing on collisions
      for d in pyspecDecls do
        for n in Core.Decl.names d do
          if existingNames.contains n.name then
            exitFailure s!"Core name collision in PySpec {ionPath}: {n.name}"
          existingNames := existingNames.insert n.name
      preludeDecls := preludeDecls ++ pyspecDecls.toArray
  let pyPrelude : Core.Program := { decls := preludeDecls.toList }
  return { corePrelude := pyPrelude, overloads := allOverloads }

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
            { name := "sarif", help := "Write results as SARIF to <file>.sarif." }]
  help := "Verify a Python Ion program via the Laurel pipeline. Translates Python to Laurel to Core, then runs SMT verification."
  callback := fun v pflags => do
    let verbose := pflags.getBool "verbose"
    let outputSarif := pflags.getBool "sarif"
    let filePath := v[0]
    let pgm ← readPythonStrata filePath
    let pySourceOpt ← tryReadPythonSource filePath
    let cmds := Strata.toPyCommands pgm.commands
    if verbose then
      IO.println "==== Python AST ===="
      IO.print pgm
    assert! cmds.size == 1

    let pySpecResult ← buildPySpecPrelude (pflags.getRepeated "pyspec")
    let pyPrelude := pySpecResult.corePrelude

    -- Extract overload dispatch tables from --dispatch files
    let mut allOverloads := pySpecResult.overloads
    for dispatchPath in pflags.getRepeated "dispatch" do
      let ionFile : System.FilePath := dispatchPath
      let sigs ←
        match ← Strata.Python.Specs.readDDM ionFile |>.toBaseIO with
        | .ok t => pure t
        | .error msg =>
          exitFailure s!"Could not read dispatch file {ionFile}: {msg}"
      let (overloads, errors) :=
        Strata.Python.Specs.ToLaurel.extractOverloads dispatchPath sigs
      if errors.size > 0 then
        IO.eprintln s!"{errors.size} dispatch warning(s) for {ionFile}:"
        for err in errors do
          IO.eprintln s!"  {err.file}: {err.message}"
      for (funcName, fnOverloads) in overloads do
        let existing := allOverloads.getD funcName {}
        allOverloads := allOverloads.insert funcName
          (fnOverloads.fold (init := existing) fun acc k v => acc.insert k v)

    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let laurelPgm := Strata.Python.pythonToLaurel pyPrelude cmds[0]! none
      sourcePathForMetadata allOverloads
    match laurelPgm with
      | .error e =>
        exitFailure s!"Python to Laurel translation failed: {e}"
      | .ok (laurelProgram, ctx)  =>
        if verbose then
          IO.println "\n==== Laurel Program ===="
          IO.println f!"{laurelProgram}"

        -- Translate Laurel to Core
        match Strata.Laurel.translate laurelProgram ctx.preludeFunctions with
        | .error diagnostics =>
          exitFailure s!"Laurel to Core translation failed: {diagnostics}"
        | .ok (coreProgramDecls, modifiesDiags) =>
          if verbose then
            IO.println "\n==== Core Program ===="
            IO.print (coreProgramDecls, modifiesDiags)

          -- Strip the Laurel corePrelude prefix (always emitted by
          -- Laurel.translate); already present in pyPrelude.
          let laurelPreludeSize := Strata.Laurel.corePrelude.decls.length
          let programDecls := coreProgramDecls.decls.drop laurelPreludeSize
          -- Check for name collisions between program and prelude
          let preludeNames : Std.HashSet String :=
            pyPrelude.decls.flatMap Core.Decl.names
              |>.foldl (init := {}) fun s n => s.insert n.name
          let collisions := programDecls.flatMap fun d =>
            d.names.filter fun n => preludeNames.contains n.name
          if !collisions.isEmpty then
            let names := ", ".intercalate (collisions.map (·.name))
            exitFailure s!"Core name collision between program and prelude: {names}"
          let coreProgram := {decls := pyPrelude.decls ++ programDecls }

          -- Verify using Core verifier
          let vcResults ← IO.FS.withTempDir (fun tempDir =>
              EIO.toIO
                (fun f => IO.Error.userError (toString f))
                (Core.verify coreProgram tempDir .none
                  { Options.default with stopOnFirstError := false, verbose := .quiet, solver := "z3" }))

          -- Print results
          IO.println "\n==== Verification Results ===="
          let mut s := ""
          for vcResult in vcResults do
            let (locationPrefix, locationSuffix) := match Imperative.getFileRange vcResult.obligation.metadata with
              | some fr =>
                if fr.range.isNone then ("", "")
                else
                  match pySourceOpt with
                  | some (pyPath, fileMap) =>
                    match fr.file with
                    | .file path =>
                      if path == pyPath then
                        let pos := fileMap.toPosition fr.range.start
                        match vcResult.result with
                        | .fail => (s!"Assertion failed at line {pos.line}, col {pos.column}: ", "")
                        | _ => ("", s!" (at line {pos.line}, col {pos.column})")
                      else
                        match vcResult.result with
                        | .fail => (s!"Assertion failed at byte {fr.range.start}: ", "")
                        | _ => ("", s!" (at byte {fr.range.start})")
                  | none =>
                    match vcResult.result with
                    | .fail => (s!"Assertion failed at byte {fr.range.start}: ", "")
                    | _ => ("", s!" (at byte {fr.range.start})")
              | none => ("", "")
            s := s ++ s!"{locationPrefix}{vcResult.obligation.label}: {Std.format vcResult.result}{locationSuffix}\n"
          IO.println s
          -- Output in SARIF format if requested
          if outputSarif then
            let files := match pySourceOpt with
              | some (pyPath, fileMap) => Map.empty.insert (Strata.Uri.file pyPath) fileMap
              | none => Map.empty
            Core.Sarif.writeSarifOutput files vcResults (filePath ++ ".sarif")

def javaGenCommand : Command where
  name := "javaGen"
  args := [ "dialect-file", "package", "output-dir" ]
  flags := [includeFlag]
  help := "Generate Java source files from a DDM dialect definition. Writes .java files under output-dir."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let (ld, pd) ← readFile fm v[0]
    match pd with
    | .dialect d =>
      match Strata.Java.generateDialect d v[1] with
      | .ok files =>
        Strata.Java.writeJavaFiles v[2] v[1] files
        IO.println s!"Generated Java files for {d.name} in {v[2]}/{Strata.Java.packageToPath v[1]}"
      | .error msg =>
        exitFailure s!"Error generating Java: {msg}"
    | .program _ =>
      exitFailure "Expected a dialect file, not a program file."

def deserializeIonToLaurelFiles (bytes : ByteArray) : IO (List Strata.StrataFile) := do
  match Strata.Program.filesFromIon Strata.Laurel.Laurel_map bytes with
  | .ok files => pure files
  | .error msg => exitFailure msg

def laurelAnalyzeCommand : Command where
  name := "laurelAnalyze"
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

    let diagnostics ← Strata.Laurel.verifyToDiagnosticModels combinedProgram Strata.Python.CorePrelude_functions

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
    commands := [pyAnalyzeCommand, pyAnalyzeLaurelCommand, pyTranslateCommand,
                 pySpecsCommand, pySpecToLaurelCommand] },
  { name := "Laurel"
    commands := [laurelAnalyzeCommand] },
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

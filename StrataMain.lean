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
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Transform.ProcedureInlining
import Strata.Languages.Python.CorePrelude
import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO

import Strata.SimpleAPI

open Core (VerifyOptions VerboseMode)

def exitFailure {α} (message : String) (hint : String := "strata --help") : IO α := do
  IO.eprintln s!"Exception: {message}\n\nRun {hint} for additional help."
  IO.Process.exit 1

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
    let _ ← Strata.readStrataFile fm v[0]
    pure ()

def toIonCommand : Command where
  name := "toIon"
  args := [ "input", "output" ]
  flags := [includeFlag]
  help := "Convert a Strata text file to Ion binary format."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap
    let (_, pd) ← Strata.readStrataFile searchPath v[0]
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
    let (ld, pd) ← Strata.readStrataFile searchPath v[0]
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
    let ⟨_, p1⟩ ← Strata.readStrataFile fm v[0]
    let ⟨_, p2⟩ ← Strata.readStrataFile fm v[1]
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
  else if ionPath.endsWith ".py.ion" then
    some (ionPath.dropEnd ".ion".length |>.toString)
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
    Strata.Python.Core.prelude.decls.toArray ++ Strata.Laurel.corePrelude.decls.toArray
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
    match Strata.Laurel.translate result.program with
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
    let laurelPgm := Strata.Python.pythonToLaurel pyPrelude cmds[0]!
      sourcePathForMetadata allOverloads
    match laurelPgm with
      | .error e =>
        exitFailure s!"Python to Laurel translation failed: {e}"
      | .ok laurelProgram =>
        if verbose then
          IO.println "\n==== Laurel Program ===="
          IO.println f!"{laurelProgram}"

        -- Translate Laurel to Core
        match Strata.Laurel.translate laurelProgram with
        | .error diagnostics =>
          exitFailure s!"Laurel to Core translation failed: {diagnostics}"
        | .ok (coreProgramDecls, modifiesDiags) =>
          if verbose then
            IO.println "\n==== Core Program ===="
            IO.print (coreProgramDecls, modifiesDiags)

          -- Strip the Laurel corePrelude prefix (always emitted by
          -- Laurel.translate); already present in pyPrelude.
          -- We don't want to strip types defined by the user program
          -- (e.g., Class declarations), so we add those back.
          let laurelPreludeSize := Strata.Laurel.corePrelude.decls.length
          let droppedPrefix := coreProgramDecls.decls.take laurelPreludeSize
          let programDecls := coreProgramDecls.decls.drop laurelPreludeSize
          let pyPreludeDecls := pyPrelude.decls.map fun d =>
            match droppedPrefix.find? (fun pd => pd.name.name == d.name.name) with
            | some replacement => replacement
            | none => d
          -- Check for name collisions between program and prelude
          let preludeNames : Std.HashSet String :=
            pyPreludeDecls.flatMap Core.Decl.names
              |>.foldl (init := {}) fun s n => s.insert n.name
          let collisions := programDecls.flatMap fun d =>
            d.names.filter fun n => preludeNames.contains n.name
          if !collisions.isEmpty then
            let names := ", ".intercalate (collisions.map (·.name))
            exitFailure s!"Core name collision between program and prelude: {names}"
          let coreProgram := {decls := pyPreludeDecls ++ programDecls }

          -- Verify using Core verifier
          let vcResults ← IO.FS.withTempDir (fun tempDir =>
              EIO.toIO
                (fun f => IO.Error.userError (toString f))
                (Core.verify coreProgram tempDir .none
                  { VerifyOptions.default with stopOnFirstError := false, verbose := .quiet, solver := "z3" }))

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

private def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  if name.endsWith ".python.st.ion" then (name.dropEnd 14).toString
  else if name.endsWith ".py.ion" then (name.dropEnd 7).toString
  else if name.endsWith ".st.ion" then (name.dropEnd 7).toString
  else if name.endsWith ".st" then (name.dropEnd 3).toString
  else name

private def renameIdent (rn : Std.HashMap String String) (id : Core.CoreIdent) : Core.CoreIdent :=
  match rn[id.name]? with
  | some new => ⟨new, id.metadata⟩
  | none => id

/-! ## Core-to-GOTO translation

### Known limitations

#### Program-level declarations (`Core.Decl`)
- **`Decl.var`** (global variables): Emitted as GOTO symbol table entries with
  `isStaticLifetime := true`. Optional initializers are translated to the symbol's
  `value` field.
- **`Decl.ax`** (axioms): Emitted as ASSUME instructions at the start of each
  procedure body.
- **`Decl.distinct`**: Emitted as pairwise `!=` ASSUME instructions at the
  start of each procedure body.

#### Procedure contracts (`Core.Procedure.Spec`)
Preconditions, postconditions, and modifies clauses are now emitted as
`#spec_requires`, `#spec_ensures`, and `#spec_assigns` named sub-expressions
on the code type in the symbol table. These are recognized by
`goto-instrument --apply-code-contracts` (DFCC).

The following are not yet handled:
- **`free requires`/`free ensures`**: Silently skipped (not emitted as contract
  annotations). CBMC's DFCC does not have a direct equivalent of Boogie's free specs.

#### Procedure calls
- **`CmdExt.call`**: Handled by `coreStmtsToGoto`, which emits FUNCTION_CALL
  instructions directly. The `unwrapCmdExt` path (used when no calls are present)
  returns an error on calls as a safety check.
-/

private partial def renameExpr (rn : Std.HashMap String String) : Core.Expression.Expr → Core.Expression.Expr
  | .fvar m name ty => .fvar m (renameIdent rn name) ty
  | .app m f e => .app m (renameExpr rn f) (renameExpr rn e)
  | .abs m ty e => .abs m ty (renameExpr rn e)
  | .quant m qk ty tr e => .quant m qk ty (renameExpr rn tr) (renameExpr rn e)
  | .ite m c t e => .ite m (renameExpr rn c) (renameExpr rn t) (renameExpr rn e)
  | .eq m e1 e2 => .eq m (renameExpr rn e1) (renameExpr rn e2)
  | e => e

private def renameCmd (rn : Std.HashMap String String) : Imperative.Cmd Core.Expression → Imperative.Cmd Core.Expression
  | .init name ty e md => .init (renameIdent rn name) ty (e.map (renameExpr rn)) md
  | .set name e md => .set (renameIdent rn name) (renameExpr rn e) md
  | .havoc name md => .havoc (renameIdent rn name) md
  | .assert l e md => .assert l (renameExpr rn e) md
  | .assume l e md => .assume l (renameExpr rn e) md
  | .cover l e md => .cover l (renameExpr rn e) md

private partial def unwrapCmdExt (rn : Std.HashMap String String) : Core.Statement → Except Std.Format (Imperative.Stmt Core.Expression (Imperative.Cmd Core.Expression))
  | .cmd (.cmd c) => .ok (.cmd (renameCmd rn c))
  | .cmd (.call ..) => .error f!"[unwrapCmdExt] Unexpected call; use coreStmtsToGoto instead."
  | .block l stmts md => do
    let stmts' ← stmts.mapM (unwrapCmdExt rn)
    .ok (.block l stmts' md)
  | .ite c t e md => do
    let t' ← t.mapM (unwrapCmdExt rn)
    let e' ← e.mapM (unwrapCmdExt rn)
    .ok (.ite (renameExpr rn c) t' e' md)
  | .loop g m i body md => do
    let body' ← body.mapM (unwrapCmdExt rn)
    .ok (.loop (renameExpr rn g) (m.map (renameExpr rn)) (i.map (renameExpr rn)) body' md)
  | .exit l md => .ok (.exit l md)
  | .funcDecl _d _md => .error f!"[unwrapCmdExt] Unexpected funcDecl; should have been lifted by collectFuncDecls."

/-- Check whether a Core statement list contains any call statements. -/
private def hasCallStmt : List Core.Statement → Bool
  | [] => false
  | .cmd (.call ..) :: _ => true
  | .block _ stmts _ :: rest => hasCallStmt stmts || hasCallStmt rest
  | .ite _ t e _ :: rest => hasCallStmt t || hasCallStmt e || hasCallStmt rest
  | .loop _ _ _ body _ :: rest => hasCallStmt body || hasCallStmt rest
  | _ :: rest => hasCallStmt rest

/-- Collect all funcDecl statements from a procedure body (recursively) and
    return them as Core.Functions, stripping them from the body. -/
private def collectFuncDecls : List Core.Statement →
    Except Std.Format (List Core.Function × List Core.Statement)
  | [] => return ([], [])
  | .funcDecl decl _ :: rest => do
    let f ← Core.Function.ofPureFunc decl
    let (fs, rest') ← collectFuncDecls rest
    return (f :: fs, rest')
  | .block l stmts md :: rest => do
    let (fs1, stmts') ← collectFuncDecls stmts
    let (fs2, rest') ← collectFuncDecls rest
    return (fs1 ++ fs2, .block l stmts' md :: rest')
  | .ite c t e md :: rest => do
    let (fs1, t') ← collectFuncDecls t
    let (fs2, e') ← collectFuncDecls e
    let (fs3, rest') ← collectFuncDecls rest
    return (fs1 ++ fs2 ++ fs3, .ite c t' e' md :: rest')
  | .loop g m i body md :: rest => do
    let (fs1, body') ← collectFuncDecls body
    let (fs2, rest') ← collectFuncDecls rest
    return (fs1 ++ fs2, .loop g m i body' md :: rest')
  | s :: rest => do
    let (fs, rest') ← collectFuncDecls rest
    return (fs, s :: rest')

/-- Translate Core statements to GOTO instructions, handling calls at any nesting level. -/
private partial def coreStmtsToGoto
    (Env : Core.Expression.TyEnv) (pname : String)
    (rn : Std.HashMap String String)
    (stmts : List Core.Statement)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    : Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) := do
  let toExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Core.Visibility⟩) []
  match stmts with
  | [] => return trans
  | stmt :: rest =>
    let trans ← match stmt with
      | .cmd (.call lhs procName args _md) =>
        let renamedLhs := lhs.map (renameIdent rn)
        let renamedArgs := args.map (renameExpr rn)
        let argExprs ← renamedArgs.mapM toExpr
        let lhsExpr := match renamedLhs with
          | id :: _ =>
            let name := Core.CoreIdent.toPretty id
            let ty := match trans.T.context.types.find? id with
              | some lty =>
                lty.toMonoTypeUnsafe.toGotoType |>.toOption |>.getD .Integer
              | none => .Integer
            CProverGOTO.Expr.symbol name ty
          | [] => CProverGOTO.Expr.symbol "" .Empty
        let calleeExpr := CProverGOTO.Expr.symbol procName .Empty
        let callCode := CProverGOTO.Code.functionCall lhsExpr calleeExpr argExprs
        let inst : CProverGOTO.Instruction :=
          { type := .FUNCTION_CALL, code := callCode, locationNum := trans.nextLoc }
        pure { trans with instructions := trans.instructions.push inst, nextLoc := trans.nextLoc + 1 }
      | .block l body md =>
        if hasCallStmt body then
          let srcLoc := Imperative.metadataToSourceLoc md pname trans.fileMap
          let trans := Imperative.emitLabel l srcLoc trans
          coreStmtsToGoto Env pname rn body trans
        else
          let impStmt ← unwrapCmdExt rn stmt
          Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
      | .ite cond thenb elseb md =>
        if hasCallStmt thenb || hasCallStmt elseb then
          let srcLoc := Imperative.metadataToSourceLoc md pname trans.fileMap
          let cond_expr ← toExpr (renameExpr rn cond)
          let (trans, goto_else_idx) := Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr) srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn thenb trans
          let (trans, goto_end_idx) := Imperative.emitUncondGoto srcLoc trans
          let else_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"else_{else_loc}" srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn elseb trans
          let end_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"end_if_{else_loc}" srcLoc trans
          pure (Imperative.patchGotoTargets trans [(goto_else_idx, else_loc), (goto_end_idx, end_loc)])
        else
          let impStmt ← unwrapCmdExt rn stmt
          Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
      | .loop guard measure invariants body md =>
        if hasCallStmt body then
          let srcLoc := Imperative.metadataToSourceLoc md pname trans.fileMap
          let loop_head := trans.nextLoc
          let trans := Imperative.emitLabel s!"loop_{loop_head}" srcLoc trans
          let guard_expr ← toExpr (renameExpr rn guard)
          let (trans, goto_end_idx) := Imperative.emitCondGoto (CProverGOTO.Expr.not guard_expr) srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn body trans
          let mut backGuard := CProverGOTO.Expr.true
          for inv in invariants do
            let inv_expr ← toExpr (renameExpr rn inv)
            backGuard := backGuard.setNamedField "#spec_loop_invariant" inv_expr
          match measure with
            | some meas =>
              let meas_expr ← toExpr (renameExpr rn meas)
              backGuard := backGuard.setNamedField "#spec_decreases" meas_expr
            | none => pure ()
          let backInst : CProverGOTO.Instruction :=
            { type := .GOTO, guard := backGuard, target := some loop_head,
              locationNum := trans.nextLoc, sourceLoc := srcLoc }
          let trans := { trans with
            instructions := trans.instructions.push backInst
            nextLoc := trans.nextLoc + 1 }
          let end_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"end_loop_{loop_head}" srcLoc trans
          pure (Imperative.patchGotoTargets trans [(goto_end_idx, end_loc)])
        else
          let impStmt ← unwrapCmdExt rn stmt
          Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
      | other => do
        let impStmt ← unwrapCmdExt rn other
        Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
    coreStmtsToGoto Env pname rn rest trans

def procedureToGotoCtx (Env : Core.Expression.TyEnv) (p : Core.Procedure)
    (fileMap : Option Lean.FileMap := none)
    (axioms : List Core.Axiom := [])
    (distincts : List (Core.Expression.Ident × List Core.Expression.Expr) := [])
    : Except Std.Format (CoreToGOTO.CProverGOTO.Context × List Core.Function) := do
  -- Lift local function declarations out of the body
  let (liftedFuncs, body) ← collectFuncDecls p.body
  let pname := Core.CoreIdent.toPretty p.header.name
  if !p.header.typeArgs.isEmpty then
    .error f!"[procedureToGotoCtx] Polymorphic procedures unsupported."
  let ret_ty := CProverGOTO.Ty.Empty
  let formals := p.header.inputs.keys.map Core.CoreIdent.toPretty
  let formals_tys ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol pname ·)
  let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys
  let outputs := p.header.outputs.keys.map Core.CoreIdent.toPretty
  let new_outputs := outputs.map (CProverGOTO.mkLocalSymbol pname ·)
  let locals := (Imperative.Block.definedVars body).map Core.CoreIdent.toPretty
  let new_locals := locals.map (CProverGOTO.mkLocalSymbol pname ·)
  let rn : Std.HashMap String String :=
    (formals.zip new_formals ++ outputs.zip new_outputs ++ locals.zip new_locals).foldl
      (init := {}) fun m (k, v) => m.insert k v
  -- Seed the type environment with renamed input and output parameter types
  let inputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_formals.zip p.header.inputs.values).map fun (n, ty) =>
      (Core.CoreIdent.locl n, .forAll [] ty)
  let outputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_outputs.zip p.header.outputs.values).map fun (n, ty) =>
      (Core.CoreIdent.locl n, .forAll [] ty)
  let Env' : Core.Expression.TyEnv :=
    @Lambda.TEnv.addInNewestContext ⟨Core.ExpressionMetadata, Core.Visibility⟩ Env (inputEntries ++ outputEntries)
  -- Emit axioms as ASSUME instructions at the start of the body
  let mut axiomInsts : Array CProverGOTO.Instruction := #[]
  let mut axiomLoc : Nat := 0
  for ax in axioms do
    let gotoExpr ← Lambda.LExpr.toGotoExprCtx
      (TBase := ⟨Core.ExpressionMetadata, Core.Visibility⟩) [] ax.e
    axiomInsts := axiomInsts.push
      { type := .ASSUME, locationNum := axiomLoc,
        guard := gotoExpr,
        sourceLoc := { CProverGOTO.SourceLocation.nil with function := pname, comment := s!"axiom {ax.name}" } }
    axiomLoc := axiomLoc + 1
  -- Emit distinct declarations as pairwise != ASSUME instructions
  for (dname, exprs) in distincts do
    let gotoExprs ← exprs.mapM
      (Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Core.Visibility⟩) [])
    for i in List.range gotoExprs.length do
      for j in List.range gotoExprs.length do
        if i < j then
          let ei := gotoExprs[i]!
          let ej := gotoExprs[j]!
          let neqExpr : CProverGOTO.Expr :=
            { id := .binary .NotEqual, type := .Boolean, operands := [ei, ej] }
          let srcLoc : CProverGOTO.SourceLocation :=
            { CProverGOTO.SourceLocation.nil with
                function := pname
                comment := s!"distinct {Core.CoreIdent.toPretty dname}" }
          axiomInsts := axiomInsts.push
            { type := .ASSUME, locationNum := axiomLoc, guard := neqExpr, sourceLoc := srcLoc }
          axiomLoc := axiomLoc + 1
  let ans ← if hasCallStmt body then
    coreStmtsToGoto Env' pname rn body
      { instructions := axiomInsts, nextLoc := axiomLoc, T := Env', fileMap := fileMap }
  else do
    let impBody ← body.mapM (unwrapCmdExt rn)
    Imperative.Stmts.toGotoTransform Env' pname impBody (loc := axiomLoc) (fileMap := fileMap)
      |>.map fun ans => { ans with instructions := axiomInsts ++ ans.instructions }
  let ending_insts : Array CProverGOTO.Instruction :=
    #[{ type := .END_FUNCTION, locationNum := ans.nextLoc + 1 }]
  let pgm := { name := pname,
               parameterIdentifiers := new_formals.toArray,
               instructions := ans.instructions ++ ending_insts }
  -- Translate procedure contracts to GOTO JSON annotations
  -- Free specs (CheckAttr.Free) are assumed but not checked, so we skip them.
  let mut contracts : List (String × Lean.Json) := []
  let preExprs := p.spec.preconditions.values.filter (fun c => c.attr == .Default)
    |>.map (fun c => renameExpr rn c.expr)
  let postExprs := p.spec.postconditions.values.filter (fun c => c.attr == .Default)
    |>.map (fun c => renameExpr rn c.expr)
  if !preExprs.isEmpty then
    let preGoto ← preExprs.mapM (Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Core.Visibility⟩) [])
    let preJson := preGoto.map CProverGOTO.exprToJson
    contracts := contracts ++ [("#spec_requires",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr preJson.toArray)])]
  if !postExprs.isEmpty then
    let postGoto ← postExprs.mapM (Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Core.Visibility⟩) [])
    let postJson := postGoto.map CProverGOTO.exprToJson
    contracts := contracts ++ [("#spec_ensures",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr postJson.toArray)])]
  if !p.spec.modifies.isEmpty then
    let modGoto := p.spec.modifies.map fun ident =>
      CProverGOTO.Expr.symbol (Core.CoreIdent.toPretty ident) .Integer
    let modJson := modGoto.map CProverGOTO.exprToJson
    contracts := contracts ++ [("#spec_assigns",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr modJson.toArray)])]
  -- Build localTypes map for output parameters (so they get proper types in symbol table)
  let output_tys ← p.header.outputs.values.mapM Lambda.LMonoTy.toGotoType
  let localTypes : Std.HashMap String CProverGOTO.Ty :=
    (outputs.zip output_tys).foldl (init := {}) fun m (k, v) => m.insert k v
  let ctx : CoreToGOTO.CProverGOTO.Context :=
    { program := pgm, formals := formals_tys, ret := ret_ty,
      locals := outputs ++ locals, contracts := contracts,
      localTypes := localTypes }
  return (ctx, liftedFuncs)

private def functionToGotoCtx (_Env : Core.Expression.TyEnv) (f : Core.Function)
    : Except Std.Format CoreToGOTO.CProverGOTO.Context := do
  let fname := Core.CoreIdent.toPretty f.name
  if !f.typeArgs.isEmpty then
    .error f!"[functionToGotoCtx] Polymorphic functions unsupported."
  let some body := f.body
    | .error f!"[functionToGotoCtx] Function {fname} has no body."
  let ret_ty ← Lambda.LMonoTy.toGotoType f.output
  let formals := f.inputs.keys.map Core.CoreIdent.toPretty
  let formals_tys ← f.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol fname ·)
  let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys
  let rn : Std.HashMap String String :=
    (formals.zip new_formals).foldl (init := {}) fun m (k, v) => m.insert k v
  let bodyExpr := renameExpr rn body
  let gotoBody ← Lambda.LExpr.toGotoExpr bodyExpr
  let retInst : CProverGOTO.Instruction :=
    { type := .SET_RETURN_VALUE, code := .set_return_value gotoBody, locationNum := 0 }
  let endInst : CProverGOTO.Instruction :=
    { type := .END_FUNCTION, locationNum := 1 }
  let pgm := { name := fname,
               parameterIdentifiers := new_formals.toArray,
               instructions := #[retInst, endInst] }
  return { program := pgm, formals := formals_tys, ret := ret_ty, locals := [] }

/-- Emit a procedure context and its lifted functions as combined symtab/goto JSON. -/
private def emitProcWithLifted (Env : Core.Expression.TyEnv) (procName : String)
    (ctx : CoreToGOTO.CProverGOTO.Context) (liftedFuncs : List Core.Function)
    (extraSyms : Lean.Json)
    : IO (Lean.Json × Lean.Json) := do
  let json := CoreToGOTO.CProverGOTO.Context.toJson procName ctx
  let mut symtabObj := match json.symtab with | .obj m => m | _ => .empty
  let mut gotoFns := match json.goto with
    | .obj m => match m.toList.find? (·.1 == "functions") with
      | some (_, .arr fns) => fns | _ => #[]
    | _ => #[]
  for f in liftedFuncs do
    let funcName := Core.CoreIdent.toPretty f.name
    match functionToGotoCtx Env f with
    | .error e => panic! s!"{e}"
    | .ok fctx =>
      let fjson := CoreToGOTO.CProverGOTO.Context.toJson funcName fctx
      match fjson.symtab with | .obj m => for (k, v) in m.toList do symtabObj := symtabObj.insert k v | _ => pure ()
      match fjson.goto with
      | .obj m => match m.toList.find? (·.1 == "functions") with
        | some (_, .arr fns) => gotoFns := gotoFns ++ fns | _ => pure ()
      | _ => pure ()
  match extraSyms with | .obj m => for (k, v) in m.toList do symtabObj := symtabObj.insert k v | _ => pure ()
  return (Lean.Json.obj symtabObj, Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)])

private def datatypeToSymbolEntry (dt : Lambda.LDatatype Core.Visibility) :
    Except Std.Format (String × CProverGOTO.CBMCSymbol) := do
  let mut components : Array (String × Lean.Json) :=
    #[("$tag", CProverGOTO.tyToJson .Integer)]
  for constr in dt.constrs do
    for (fieldId, fieldTy) in constr.args do
      let gty ← Lambda.LMonoTy.toGotoType fieldTy
      let tyJson := CProverGOTO.tyToJson gty
      -- Recursive fields (type refers back to this datatype) must be pointers
      let tyJson := match fieldTy with
        | .tcons name _ =>
          if name == dt.name then
            Lean.Json.mkObj [
              ("id", "pointer"),
              ("sub", Lean.Json.arr #[tyJson]),
              ("namedSub", Lean.Json.mkObj [("width", Lean.Json.mkObj [("id", "64")])])
            ]
          else tyJson
        | _ => tyJson
      components := components.push (fieldId.name, tyJson)
  let componentsSub := components.map fun (name, tyJson) =>
    Lean.Json.mkObj [
      ("id", ""),
      ("namedSub", Lean.Json.mkObj [
        ("#pretty_name", Lean.Json.mkObj [("id", name)]),
        ("name", Lean.Json.mkObj [("id", name)]),
        ("type", tyJson)
      ])
    ]
  let structTy := Lean.Json.mkObj [
    ("id", "struct"),
    ("namedSub", Lean.Json.mkObj [
      ("tag", Lean.Json.mkObj [("id", dt.name)]),
      ("components", Lean.Json.mkObj [
        ("id", ""),
        ("sub", Lean.Json.arr componentsSub)
      ])
    ])
  ]
  return (s!"tag-{dt.name}", {
    baseName := dt.name
    isType := true
    mode := "C"
    module := ""
    name := s!"tag-{dt.name}"
    prettyName := s!"struct {dt.name}"
    type := structTy
    value := Lean.Json.mkObj [("id", "nil")]
  })

private def typeConstructorToSymbolEntry (tc : Core.TypeConstructor) :
    String × CProverGOTO.CBMCSymbol :=
  let structTy := Lean.Json.mkObj [
    ("id", "struct"),
    ("namedSub", Lean.Json.mkObj [
      ("tag", Lean.Json.mkObj [("id", tc.name)]),
      ("components", Lean.Json.mkObj [
        ("id", ""),
        ("sub", Lean.Json.arr #[])
      ])
    ])
  ]
  (s!"tag-{tc.name}", {
    baseName := tc.name
    isType := true
    mode := "C"
    module := ""
    name := s!"tag-{tc.name}"
    prettyName := s!"struct {tc.name}"
    type := structTy
    value := Lean.Json.mkObj [("id", "nil")]
  })

private def collectDatatypeSymbols (pgm : Core.Program) :
    Except Std.Format (Map String CProverGOTO.CBMCSymbol) := do
  let mut syms : List (String × CProverGOTO.CBMCSymbol) := []
  for decl in pgm.decls do
    match decl with
    | .type (.data dts) _ =>
      for dt in dts do
        if dt.typeArgs.isEmpty then
          let entry ← datatypeToSymbolEntry dt
          syms := syms ++ [entry]
    | .type (.con tc) _ =>
      if tc.numargs == 0 then
        syms := syms ++ [typeConstructorToSymbolEntry tc]
    | _ => pure ()
  return syms

/-- Collect global variable declarations and emit GOTO symbol table entries. -/
private def collectGlobalSymbols (pgm : Core.Program) :
    Except Std.Format (Map String CProverGOTO.CBMCSymbol) := do
  let mut syms : List (String × CProverGOTO.CBMCSymbol) := []
  for decl in pgm.decls do
    match decl with
    | .var name ty e _md =>
      let gname := Core.CoreIdent.toPretty name
      let gty ← Lambda.LMonoTy.toGotoType ty.toMonoTypeUnsafe
      let tyJson := CProverGOTO.tyToJson gty
      let valueJson ← match e with
        | some expr =>
          let gotoExpr ← Lambda.LExpr.toGotoExprCtx
            (TBase := ⟨Core.ExpressionMetadata, Core.Visibility⟩) [] expr
          pure (CProverGOTO.exprToJson gotoExpr)
        | none => pure (Lean.Json.mkObj [("id", "nil")])
      syms := syms ++ [(gname, {
        baseName := gname
        isLvalue := true
        isStaticLifetime := true
        mode := "C"
        module := ""
        name := gname
        prettyName := gname
        type := tyJson
        value := valueJson
      })]
    | _ => pure ()
  return syms

/-- Collect all extra symbol table entries (datatypes, type constructors, globals). -/
def collectExtraSymbols (pgm : Core.Program) :
    Except Std.Format (Map String CProverGOTO.CBMCSymbol) := do
  let typeSyms ← collectDatatypeSymbols pgm
  let globalSyms ← collectGlobalSymbols pgm
  return typeSyms ++ globalSyms

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
    let fileMap := pySourceOpt.map (·.2)
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
      match procedureToGotoCtx Env p fileMap (axioms := axioms) (distincts := distincts) with
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
  help := "Translate a Strata Python Ion file through Laurel to Strata Core. Write results to stdout."
  callback := fun v _ => do
    let pgm ← readPythonStrata v[0]
    let cmds := Strata.toPyCommands pgm.commands
    assert! cmds.size == 1
    let prelude := Strata.Python.Core.prelude
    let laurelPgm := Strata.Python.pythonToLaurel prelude cmds[0]!
    match laurelPgm with
    | .error e =>
      exitFailure s!"Python to Laurel translation failed: {e}"
    | .ok laurelProgram =>
      match Strata.Laurel.translate laurelProgram with
      | .error diagnostics =>
        exitFailure s!"Laurel to Core translation failed: {diagnostics}"
      | .ok coreProgram =>
        let coreProgram : Core.Program := {decls := prelude.decls ++ coreProgram.fst.decls }
        IO.print coreProgram

def pyAnalyzeLaurelToGotoCommand : Command where
  name := "pyAnalyzeLaurelToGoto"
  args := [ "file" ]
  help := "Translate a Strata Python Ion file through Laurel to CProver GOTO JSON files."
  callback := fun v _ => do
    let filePath := v[0]
    let pgm ← readPythonStrata filePath
    let pySourceOpt ← tryReadPythonSource filePath
    let cmds := Strata.toPyCommands pgm.commands
    assert! cmds.size == 1
    let prelude := Strata.Python.Core.prelude
    let sourcePathForMetadata := match pySourceOpt with
      | some (pyPath, _) => pyPath
      | none => filePath
    let laurelPgm := Strata.Python.pythonToLaurel prelude cmds[0]! sourcePathForMetadata
    match laurelPgm with
    | .error e => exitFailure s!"Python to Laurel translation failed: {e}"
    | .ok laurelProgram =>
      match Strata.Laurel.translate laurelProgram with
      | .error diagnostics =>
        exitFailure s!"Laurel to Core translation failed: {diagnostics}"
      | .ok coreProgram =>
        let coreProgram := {decls := prelude.decls ++ coreProgram.fst.decls }
        -- Inline procedure calls (except main) repeatedly until fixpoint
        let mut coreProgram := coreProgram
        for _ in List.range 10 do
          match Core.Transform.runProgram (targetProcList := .none)
                (Core.ProcedureInlining.inlineCallCmd
                  (doInline := λ name _ => name ≠ "main"))
                coreProgram .emp with
          | ⟨.ok (changed, pgm), _⟩ =>
            coreProgram := pgm
            if !changed then break
          | ⟨.error e, _⟩ => panic! e
        let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
        let Env := Lambda.TEnv.default
        let fileMap := pySourceOpt.map (·.2)
        let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env coreProgram with
          | .ok r => pure r
          | .error e => panic! s!"{e.format none}"
        -- Find the main procedure; fall back to __main__ for top-level scripts
        let findProc (name : String) := tcPgm.decls.find? fun d =>
            match d with
            | .proc p _ => Core.CoreIdent.toPretty p.header.name == name
            | _ => false
        let mainDecl ← match findProc "main" with
          | some d => pure d
          | none => match findProc "__main__" with
            | some d => pure d
            | none => panic! "No main or __main__ procedure found"
        let some p := mainDecl.getProc?
          | panic! "entry point is not a procedure"
        let baseName := deriveBaseName filePath
        -- Always use "main" as the GOTO function name (CBMC expects --function main)
        let procName := "main"
        let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
        let distincts := tcPgm.decls.filterMap fun d => match d with
          | .distinct name es _ => some (name, es) | _ => none
        match procedureToGotoCtx Env p fileMap (axioms := axioms) (distincts := distincts) with
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

def javaGenCommand : Command where
  name := "javaGen"
  args := [ "dialect-file", "package", "output-dir" ]
  flags := [includeFlag]
  help := "Generate Java source files from a DDM dialect definition. Writes .java files under output-dir."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let (ld, pd) ← Strata.readStrataFile fm v[0]
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

    let diagnostics ← Strata.Laurel.verifyToDiagnosticModels combinedProgram

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
      let results ← Strata.Laurel.verifyToVcResults laurelProgram { Options.default with solver := "z3" }
      match results with
      | .error errors =>
        IO.println s!"==== ERRORS ===="
        for err in errors do
          IO.println s!"{err.message}"
      | .ok vcResults =>
        IO.println s!"==== RESULTS ===="
        for vc in vcResults do
          IO.println s!"{vc.obligation.label}: {repr vc.result}"

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
      match Strata.Laurel.translate laurelProgram with
      | .error diags => exitFailure s!"Core translation errors: {diags.map (·.message)}"
      | .ok coreProgram =>
        let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
        let Env := Lambda.TEnv.default
        let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env coreProgram.fst with
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
        let fileMap := Lean.FileMap.ofString content
        let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
        let distincts := tcPgm.decls.filterMap fun d => match d with
          | .distinct name es _ => some (name, es) | _ => none
        let mut symtabPairs : List (String × Lean.Json) := []
        let mut gotoFns : Array Lean.Json := #[]
        let mut allLiftedFuncs : List Core.Function := []
        for p in procs do
          let procName := Core.CoreIdent.toPretty p.header.name
          match procedureToGotoCtx Env p (fileMap := fileMap) (axioms := axioms) (distincts := distincts) with
          | .error e => panic! s!"{e}"
          | .ok (ctx, liftedFuncs) =>
            allLiftedFuncs := allLiftedFuncs ++ liftedFuncs
            let json := CoreToGOTO.CProverGOTO.Context.toJson procName ctx
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
            let json := CoreToGOTO.CProverGOTO.Context.toJson funcName ctx
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
      match Strata.Laurel.translate laurelProgram with
      | .error diags => exitFailure s!"Core translation errors: {diags.map (·.message)}"
      | .ok coreProgram => IO.println (prettyPrintCore coreProgram.fst)

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
                 pySpecsCommand, pySpecToLaurelCommand,
                 pyAnalyzeLaurelToGotoCommand, pyAnalyzeToGotoCommand,
                 pyTranslateCommand, pyTranslateLaurelCommand] },
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

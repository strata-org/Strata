/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Elab
import Strata.DDM.Ion
import Strata.DDM.Util.ByteArray
public import Strata.Util.IO
public import Std.Data.HashSet.Basic

import Strata.DDM.Integration.Java.Gen
public import Strata.Transform.CoreTransform
import Strata.Transform.ProcedureInlining

public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Options

import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
public import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator

public import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM

/-! ## Simple Strata API

A simple API for reading, writing, transforming, and analyzing Strata programs.

This API allows clients of Strata to perform its basic operations as directly as
possible. It is intended for use cases that are essentially equivalent to more
fine-grained or more structured equivalents of what the `strata` CLI can
currently do.

**Note:** Some definitions are opaque for the moment, so that we can discuss the
structure. Most can be implemented straightforwardly by calling existing code.
Those that can't are noted explicitly.
**Note:** This is a proposed API that is only partially implemented. Functions
that have been implemented are marked `def`. Proposed but unimplemented functions
are declared using `opaque` to define the intended API surface; these should not
be invoked.
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
-/

namespace Strata

public section

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
noncomputable opaque genericToCore : Strata.Program → Except String Core.Program

/--
Translate a program in the dialect-specific AST for Laurel into the generic Strata
AST. Usually useful as a step before serialization.
-/
noncomputable opaque laurelToGeneric : Laurel.Program → Strata.Program

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Laurel. This can fail with an error message if the input is not a
well-structured instance of the Core dialect.
-/
noncomputable opaque genericToLaurel : Strata.Program → Except String Laurel.Program

/-! ### Transformation between dialects -/

/--
Translate a program represented in the dialect-specific AST for the Laurel
dialect into the dialect-specific AST for the Core dialect. This can fail with
an error message if the input program contains constructs that are not yet
supported.
-/
noncomputable opaque laurelToCore : Laurel.Program → Except String Core.Program

/-! ### Transformation of Core programs -/

/--
Options to control the behavior of inlining procedure calls in a Core program.
-/
noncomputable opaque Core.InlineTransformOptions : Type

/--
Transform a Core program to inline some or all procedure calls.
-/
noncomputable opaque Core.inlineProcedures : Core.Program → Core.InlineTransformOptions → Core.Program

/--
Transform a Core program to replace each loop with assertions and assumptions about
its invariants.
-/
noncomputable opaque Core.loopElimWithContract : Core.Program → Core.Program

/--
Transform a Core program to replace each procedure call with assertions and
assumptions about its contract.
-/
noncomputable opaque Core.callElimWithContract : Core.Program → Core.Program

/-! ### Analysis of Core programs -/

/--
Do deductive verification of a Core program, including any external solver
invocation that is necessary.
-/
noncomputable opaque Core.verify : Core.Program → Core.VerifyOptions → IO Core.VCResults

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
def pySpecsDir (sourceDir strataDir dialectFile : System.FilePath)
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
def pyTranslateLaurel
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

/-! ### Deductive verification of Core programs -/

/-- Run deductive verification on a Core program.
    Creates a temporary directory for solver interaction,
    runs the Core verifier, and returns verification-condition results. -/
def verifyCore (program : Core.Program)
    (options : Core.VerifyOptions)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults :=
    EIO.toIO (IO.Error.userError ∘ toString)
      (_root_.Core.verify (proceduresToVerify := none) program tempDir options moreFns)
  let result ← match options.vcDirectory with
    | .some vcDir =>
      match ← (IO.FS.createDirAll vcDir *> runVerification vcDir) |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"{e}"
    | .none =>
      match ← (IO.FS.withTempDir runVerification) |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"{e}"
  return result

end -- public section

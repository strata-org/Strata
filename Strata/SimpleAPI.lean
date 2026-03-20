/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.IO

public import Strata.Transform.CoreTransform
import Strata.Transform.CallElim
import Strata.Transform.ProcedureInlining

public import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM

/-! ## Simple Strata API

A simple API for reading, writing, transforming, and analyzing Strata programs.

This API allows clients of Strata to perform its basic operations as directly as
possible. It is intended for use cases that are essentially equivalent to more
fine-grained or more structured equivalents of what the `strata` CLI can
currently do.

**Note:** Several functions in this API are currently unimplemented due to
functionality that remains to be implemented in the DDM. These functions are
declared using `noncomputable opaque` to define the intended API surface; these
should not be invoked yet.

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
def genericToCore (p : Strata.Program) : Except String Core.Program :=
  let (program, errors) := Core.getProgram p
  if errors.isEmpty then
    .ok program
  else
    .error s!"Core DDM translation errors: {errors.toList}"

/--
Translate a program in the dialect-specific AST for Laurel into the generic Strata
AST. Usually useful as a step before serialization.
-/
noncomputable opaque laurelToGeneric : Laurel.Program → Strata.Program

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
def laurelToCore (p : Laurel.Program) : Except String Core.Program :=
  let (coreOpt, diags) := Laurel.translate { emitResolutionErrors := true } p
  match coreOpt with
  | some core => .ok core
  | none => .error s!"Laurel to Core translation failed: {diags.map (·.message)}"

/-! ### Transformation of Core programs -/

/--
Options to control the behavior of inlining procedure calls in a Core program.
The `doInline` predicate decides, for each call site, whether to inline.
When `none`, all calls are inlined.
-/
structure Core.InlineTransformOptions where
  doInline : Option (String → _root_.Core.Transform.CachedAnalyses → Bool) := none

/--
Transform a Core program to inline some or all procedure calls.
-/
def Core.inlineProcedures (p : Core.Program) (opts : Core.InlineTransformOptions)
    : Except String Core.Program :=
  let pred := opts.doInline.getD (fun _ _ => true)
  match Core.Transform.run p (fun prog => do
    let (_, prog) ← Core.Transform.runProgram (coreInlineCallCmd (doInline := pred)) prog
    return prog) with
  | .ok prog => .ok prog
  | .error e => .error e

/--
Transform a Core program to replace each loop with assertions and assumptions about
its invariants.
-/
def Core.loopElimUsingContract (p : Core.Program) : Core.Program :=
  let newDecls := p.decls.map fun d => match d with
    | .proc proc md =>
      let newBody := (StateT.run (Core.Block.removeLoopsM proc.body) 0).fst
      .proc { proc with body := newBody } md
    | other => other
  { decls := newDecls }

/--
Transform a Core program to replace each procedure call with assertions and
assumptions about its contract.
-/
def Core.callElimUsingContract (p : Core.Program) : Except String Core.Program :=
  match Core.Transform.run p (fun prog => do
    let (_, prog) ← Core.Transform.runProgram coreCallElimCmd prog
    return prog) with
  | .ok prog => .ok prog
  | .error e => .error e

/-! ### Analysis of Core programs -/

/--
Do deductive verification of a Core program, including any external solver
invocation that is necessary.
-/
def Core.verifyProgram
    (program : Core.Program)
    (options : Core.VerifyOptions)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults :=
    EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify program tempDir .none options moreFns)
  match options.vcDirectory with
    | .some vcDir =>
      match ← (IO.FS.createDirAll vcDir *> runVerification vcDir) |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"{e}"
    | .none =>
      match ← (IO.FS.withTempDir runVerification) |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"{e}"

/-- Controls how translation warnings are reported. -/
inductive WarningOutput where
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
def pySpecs (pythonFile strataDir dialectFile : System.FilePath)
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

  -- Parse skip names into PythonIdents
  let some fileStem := pythonFile.fileStem
    | throw s!"No file stem for {pythonFile}"

  let mod ← match Strata.Python.Specs.ModuleName.ofString fileStem with
    | .ok m => pure m
    | .error e => throw s!"Invalid module name '{fileStem}': {e}"

  let skipIdents := skipNames.foldl (init := {}) fun acc s =>
    match Strata.Python.Specs.PythonIdent.ofString s with
    | some id => acc.insert id
    | none => acc.insert { pythonModule := fileStem, name := s }

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

/-! ### Python-to-Core via Laurel pipeline -/

/-- Translate a Python Ion file all the way to Core.  Composes
    `pyAnalyzeLaurel` (Python → combined Laurel) and
    `translateCombinedLaurel` (Laurel → Core with prelude). -/
def pyTranslateLaurel
    (pythonIonPath : String)
    (dispatchPaths : Array String := #[])
    (pyspecPaths : Array String := #[])
    : EIO String (Core.Program × List DiagnosticModel) := do
  let laurel ←
    match ← pyAnalyzeLaurel pythonIonPath dispatchPaths pyspecPaths |>.toBaseIO with
    | .ok r => pure r
    | .error err => throw (toString err)
  let (coreOption, laurelTranslateErrors) := translateCombinedLaurel laurel
  match coreOption with
  | none => throw s!"Laurel to Core translation failed: {laurelTranslateErrors}"
  | some core => pure (core, laurelTranslateErrors)

end -- public section

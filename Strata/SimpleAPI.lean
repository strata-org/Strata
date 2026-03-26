/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.IO

public import Strata.Transform.CoreTransform
import Strata.Transform.CallElim
import Strata.Transform.ProcedureInlining

public import Strata.Languages.Core.Options
public import Strata.Languages.Core.Verifier
import Strata.Languages.Laurel.LaurelToCoreTranslator
public import Strata.SimpleAPI.Python

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
    .error s!"Core DDM translation errors:\n{String.intercalate "\n" errors.toList}"

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
  doInline : Option (String → Core.Transform.CachedAnalyses → Bool) := none

/--
Transform a Core program to inline some or all procedure calls.
-/
def Core.inlineProcedures (p : Core.Program) (opts : Core.InlineTransformOptions)
    : Except String Core.Program :=
  let pred := opts.doInline.getD (fun _ _ => true)
  Core.Transform.run p (fun prog => do
    let (_, prog) ← Core.Transform.runProgram (coreInlineCallCmd (doInline := pred)) prog
    return prog)

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
  Core.Transform.run p (fun prog => do
    let (_, prog) ← Core.Transform.runProgram coreCallElimCmd prog
    return prog)

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
  let ioAction := match options.vcDirectory with
    | .some vcDir => IO.FS.createDirAll vcDir *> runVerification vcDir
    | .none => IO.FS.withTempDir runVerification
  IO.toEIO (fun e => s!"{e}") ioAction

end -- public section

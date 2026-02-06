/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.Ion
import Strata.DDM.Util.ByteArray
import Strata.Util.IO

import Strata.DDM.Integration.Java.Gen
import Strata.Languages.Python.Python
import Strata.Transform.CoreTransform
import Strata.Transform.ProcedureInlining

import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-! ## Simple Strata API

A simple API for reading, writing, transforming, and analyzing Strata programs.

This API allows clients of Strata to perform its basic operations as directly as
possible. It is intended for use cases that are essentially equivalent to more
fine-grained or more structured equivalents of what the `strata` CLI can
currently do.

**Note:** All definitions are opaque for the moment, so that we can discuss the
structure. Most can be implemented straightforwardly by calling existing code.
Those that can't are noted explicitly.

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

/-! ### File I/O -/

/--
Either a Strata dialect description or a Strata program in a specific dialect.
This is represented in a single type because an arbitrary Ion file could contain
either one.
-/
inductive DialectOrProgram
| dialect (d : Strata.Dialect)
| program (pgm : Strata.Program)

/--
Parse a Strata dialect or program in textual format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
opaque readStrataText :
  Strata.DialectFileMap →
  System.FilePath →
  ByteArray →
  IO (Strata.Elab.LoadedDialects × DialectOrProgram)

/--
Parse a Strata dialect or program in Ion format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
opaque readStrataIon :
  Strata.DialectFileMap →
  System.FilePath →
  ByteArray →
  IO (Strata.Elab.LoadedDialects × DialectOrProgram)

/--
Parse a Strata dialect or program in either textual or Ion format, possibly
loading other dialects as needed along the way. The `DialectFileMap` indicates
where to find the definitions of other dialects. The `FilePath` indicates the
name of the file to be loaded.
-/
opaque readStrataFile :
  Strata.DialectFileMap →
  System.FilePath →
  IO (Strata.Elab.LoadedDialects × DialectOrProgram)

/--
Serialize a Strata program in textual format. Returns a byte array rather than
writing directly to a file.
-/
opaque writeStrataText : Strata.Program → ByteArray

/--
Serialize a Strata program in Ion format. Returns a byte array rather than
writing directly to a file.
-/
opaque writeStrataIon : Strata.Program → ByteArray

/-! ### Transformation between generic and dialect-specific representation -/

/--
Translate a program in the dialect-specific AST for Core into the generic Strata
AST. Usually useful as a step before serialization. TODO: we can't yet implement
this, but will be able to once we use DDM-generated translation between the
generic and Strata-specific ASTs.
-/
opaque coreToGeneric : Core.Program → Strata.Program

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Core. This can fail with an error message if the input is not a
well-structured instance of the Core dialect.
-/
opaque genericToCore : Strata.Program → Except String Core.Program

/--
Translate a program in the dialect-specific AST for Laurel into the generic Strata
AST. Usually useful as a step before serialization.
-/
opaque laurelToGeneric : Laurel.Program → Strata.Program

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Laurel. This can fail with an error message if the input is not a
well-structured instance of the Core dialect.
-/
opaque genericToLaurel : Strata.Program → Except String Laurel.Program

/-! ### Transformation between dialects -/

/--
Translate a program represented in the dialect-specific AST for the Laurel
dialect into the dialect-specific AST for the Core dialect. This can fail with
an error message if the input program contains constructs that are not yet
supported.
-/
opaque laurelToCore : Laurel.Program → Except String Core.Program

/-! ### Transformation of Core programs -/

/--
Options to control the behavior of inlining procedure calls in a Core program.
-/
opaque Core.InlineTransformOptions : Type

/--
Transform a Core program to inline some or all procedure calls.
-/
opaque Core.inlineProcedures : Core.Program → Core.InlineTransformOptions → Core.Program

/--
Transform a Core program to replace each loop with assertions and assumptions about
its invariants.
-/
opaque Core.loopElimWithContract : Core.Program → Core.Program

/--
Transform a Core program to replace each procedure call with assertions and
assumptions about its contract.
-/
opaque Core.callElimWithContract : Core.Program → Core.Program

/-! ### Analysis of Core programs -/

/--
Options to control the behavior of deductive verification of Core programs.
-/
opaque Core.VerifyOptions : Type

/--
Do deductive verification of a Core program, including any external solver
invocation that is necessary.
-/
opaque Core.verify : Core.Program → Core.VerifyOptions → IO Core.VCResults

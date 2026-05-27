/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Debug-only helpers for running the Laurel compilation pipeline manually
(e.g. via `#eval`) when diagnosing pass-internal issues.

Not used by any test in this repo. The regular test framework lives in
`StrataTest.Util.TestLaurel`; see `docs/Testing.md`.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelCompilationPipeline

open Strata
open Strata.Elab (parseStrataProgramFromDialect)
open Lean.Parser (InputContext)

namespace Strata.Laurel

/-- Parse + translate + run the configurable Laurel pipeline on raw source,
    returning the diagnostics. Useful for ad-hoc invocations from `#eval`
    where you want to control `LaurelVerifyOptions` (solver, timeout,
    intermediate-file capture, etc.). -/
def processLaurelFileWithOptions (options : LaurelVerifyOptions) (input : InputContext) :
    IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error transErrors => throw (IO.userError s!"Translation errors: {transErrors}")
  | .ok laurelProgram =>
    let files := Map.insert Map.empty uri input.fileMap
    Laurel.verifyToDiagnostics files laurelProgram options

/-- Path to the directory for intermediate files, inside the build directory.
    Resolved from the current working directory so it works on any machine. -/
def buildDir : IO String := do
  let cwd ← IO.currentDir
  return s!"{cwd}/.lake/build/intermediatePrograms/"

/-- Debug helper: run the Laurel pipeline keeping intermediate pass outputs
    in `.lake/build/intermediatePrograms/`. Invoke manually via
    `#eval processLaurelFileKeepIntermediates (Strata.Parser.stringInputContext "name" source)`
    when diagnosing pass-internal issues. -/
def processLaurelFileKeepIntermediates (input : InputContext) : IO (Array Diagnostic) := do
  let dir ← buildDir
  processLaurelFileWithOptions { translateOptions := { keepAllFilesPrefix := dir } } input

end Laurel

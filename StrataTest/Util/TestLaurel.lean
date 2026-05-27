/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean.HashCommandsExpect
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.Laurel

open Strata
open Strata.Laurel

namespace StrataTest.Util

/-- Translate a `Strata.Program` (typically produced by `#strata`) to a Laurel
    `Program`. Used by tests that need to plug in a custom post-translation
    pipeline stage; throws if translation fails. -/
def translateLaurel (program : Strata.Program) : IO Laurel.Program := do
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram program) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok laurelProgram => pure laurelProgram

/-- Pretty-print a `Diagnostic` for `#guard_msgs` golden output.
    Format: `<line>:<colStart>-<colEnd>  <kind>: <message>` -/
def formatDiagnostic (d : Strata.Diagnostic) : String :=
  let kind := match d.type with
    | .Warning => "warning"
    | .UserError => "error"
    | .NotYetImplemented => "not-yet-implemented"
    | .StrataBug => "strata-bug"
  s!"{d.start.line}:{d.start.column}-{d.ending.column}  {kind}: {d.message}"

/-- Run translate + resolve only on a parsed program. Skips SMT verification,
    matching the old `processResolution` helper. Useful for resolution-only
    negative tests where running the verifier would surface unrelated noise. -/
private def runLaurelResolution (program : Strata.Program) (source : String) :
    IO (Array Strata.Diagnostic) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[{ start := ⟨0, 0⟩, ending := ⟨0, 0⟩,
               message := s!"Translation error: {e}", type := .UserError }]
  | .ok laurelProgram =>
    let result := Laurel.resolve laurelProgram
    let files := Map.insert Map.empty uri (Lean.FileMap.ofString source)
    return result.errors.map (fun dm => dm.toDiagnostic files)

/-- Run the full Laurel pipeline (translate + resolve + verify). -/
private def runLaurelPipeline (program : Strata.Program) (source : String) :
    IO (Array Strata.Diagnostic) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[{ start := ⟨0, 0⟩, ending := ⟨0, 0⟩,
               message := s!"Translation error: {e}", type := .UserError }]
  | .ok laurelProgram =>
    let files := Map.insert Map.empty uri (Lean.FileMap.ofString source)
    let options : LaurelVerifyOptions := { verifyOptions := .quiet }
    Laurel.verifyToDiagnostics files laurelProgram options

/-- Positive-test helper: run the full Laurel pipeline on a `#strata`-parsed
    program and print diagnostics in a stable format. Empty output means the
    program checks cleanly. -/
def testLaurel (program : Strata.Program) : IO Unit := do
  let pipelineDiags ← runLaurelPipeline program ""
  if pipelineDiags.isEmpty then
    IO.println "ok"
  else
    for d in pipelineDiags do IO.println (formatDiagnostic d)

/-- Positive resolution-only helper: run translate + resolve and print
    diagnostics. Use when the test only cares about resolution, not the
    verifier (e.g. "shadowing in nested blocks is OK"). -/
def testLaurelResolution (program : Strata.Program) : IO Unit := do
  let resolutionDiags ← runLaurelResolution program ""
  if resolutionDiags.isEmpty then
    IO.println "ok"
  else
    for d in resolutionDiags do IO.println (formatDiagnostic d)

/-- Negative-test helper: run the full Laurel pipeline, print diagnostics in a
    stable format, and *throw* if no diagnostics were produced. The throw is the
    safety net for the contract that `#strata_expect` blocks always produce at
    least one diagnostic; otherwise the user should use `#strata`. -/
def testLaurelExpect (block : Strata.ExpectedBlock) : IO Unit := do
  let pipelineDiags ← runLaurelPipeline block.program block.source
  let all := block.parseDiagnostics ++ pipelineDiags
  if all.isEmpty then
    throw <| IO.userError
      "#strata_expect block produced no diagnostics; use #strata for positive tests"
  for d in all do IO.println (formatDiagnostic d)

/-- Resolution-only negative-test helper: run translate + resolve and print
    diagnostics, throwing if no diagnostics were produced. Use this when the
    test asserts a resolution-pass error and running the verifier would
    surface unrelated noise. -/
def testLaurelExpectResolution (block : Strata.ExpectedBlock) : IO Unit := do
  let resolutionDiags ← runLaurelResolution block.program block.source
  let all := block.parseDiagnostics ++ resolutionDiags
  if all.isEmpty then
    throw <| IO.userError
      "#strata_expect block produced no diagnostics; use #strata for positive tests"
  for d in all do IO.println (formatDiagnostic d)

end StrataTest.Util

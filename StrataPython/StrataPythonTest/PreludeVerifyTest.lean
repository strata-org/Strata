/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PySpecPipeline
meta import all StrataPython.PyFactory
meta import all Strata.Languages.Core

meta section

/-! # Prelude Verification Test

Verify that all prelude procedures pass verification.
This ensures the Python runtime prelude is well-formed
after PrecondElim generates WF-checking procedures. -/

open Strata
namespace StrataPython.PreludeVerifyTest

/-- Build the full Core prelude program (Laurel-translated + Core-only parts). -/
private def preludeProgram : IO Core.Program := do
  let (coreOption, _) ← StrataPython.translateCombinedLaurel pythonRuntimeLaurelPart
  match coreOption with
  | some prog => return prog
  | none => return { decls := [] }

private def verifyPrelude : IO (Array DiagnosticModel) := do
  let prog ← preludeProgram
  IO.FS.withTempDir fun tempDir => do
    let r ← EIO.toIO (IO.Error.userError ∘ toString)
      (_root_.Core.verify prog tempDir
        (options := .quiet)
        (moreFns := StrataPython.ReFactory)
        (externalPhases := [Strata.frontEndPhase]))
    return r.flatMap (fun vcr => (toDiagnosticModel vcr []).toArray)

/-- info: #[] -/
#guard_msgs in
#eval verifyPrelude

end StrataPython.PreludeVerifyTest
end

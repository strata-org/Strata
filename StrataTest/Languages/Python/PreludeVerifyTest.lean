/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.PyFactory
import Strata.Languages.Core.Verifier

/-! # Prelude Verification Test

Verify that all prelude procedures pass verification.
This ensures the Python runtime prelude is well-formed
after PrecondElim generates WF-checking procedures. -/

namespace Strata.Python.PreludeVerifyTest

/-- Build the full Core prelude program (Laurel-translated + Core-only parts). -/
private def preludeProgram : IO Core.Program := do
  let (coreOption, _) ← Strata.translateCombinedLaurel pythonRuntimeLaurelPart
  match coreOption with
  | some prog => return prog
  | none => return { decls := [] }

private def verifyPrelude : IO (Array DiagnosticModel) := do
  let prog ← preludeProgram
  IO.FS.withTempDir fun tempDir => do
    let r ← EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify prog tempDir
        (options := .quiet)
        (moreFns := Strata.Python.ReFactory)
        (externalPhases := [Strata.frontEndPhase]))
    return r.flatMap (fun vcr => (toDiagnosticModel vcr []).toArray)

/-- info: #[] -/
#guard_msgs in
#eval verifyPrelude

end Strata.Python.PreludeVerifyTest

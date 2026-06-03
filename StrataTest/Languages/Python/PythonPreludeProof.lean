/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.PyFactory
import Strata.Languages.Python.pythonRuntimeLaurelPartProof
import Strata.Languages.Core.Verifier


/-! # Prelude Proof Verification Test

Verify that all prelude theorems pass verification.  -/

namespace Strata.Python.PreludeVerifyTest

private def mergePrograms (p1 p2: Laurel.Program) : Laurel.Program :=
{
  staticProcedures := p1.staticProcedures ++ p2.staticProcedures
  staticFields := p1.staticFields ++ p2.staticFields
  types := p1.types ++ p2.types
  constants := p1.constants ++ p2.constants
}

/-- Build the full Core prelude program (Laurel-translated + Core-only parts). -/
private def preludeProgramProof : IO Core.Program := do
  let prog := mergePrograms pythonRuntimeLaurelPart pythonRuntimeLaurelPartProof
  let (coreOption, _) ← Strata.translateCombinedLaurel prog
  match coreOption with
  | some prog => return prog
  | none => return { decls := [] }


private def verifyPreludeProof : IO (Array DiagnosticModel) := do
  let prog ← preludeProgramProof
  IO.FS.withTempDir fun tempDir => do
    let r ← EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify prog tempDir
        (options := .quiet)
        (moreFns := Strata.Python.ReFactory)
        (externalPhases := [Strata.frontEndPhase]))
    return r.flatMap (fun vcr => (toDiagnosticModel vcr []).toArray)

/-- info: #[] -/
#guard_msgs in
#eval verifyPreludeProof

end Strata.Python.PreludeVerifyTest

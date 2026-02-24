/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreSMT.StmtVerifier
import Strata.Languages.Core.CoreSMT.Diagnosis

/-!
# CoreSMT Verifier Public Interface

Provides the main entry point for verifying CoreSMT programs. The verifier
processes statements sequentially, accumulating results and returning updated
state for reuse.
-/

namespace Strata.Core.CoreSMT

/-- Add diagnosis to a failed verification result -/
def addDiagnosis (state : CoreSMTState) (E : Core.Env) (result : Core.VCResult)
    (smtCtx : Core.SMT.Context) : IO Core.VCResult := do
  if result.result == .pass then
    return result
  else
    -- Diagnose the failure
    let diagResult ← Diagnosis.diagnoseFailure state E result.obligation.obligation false smtCtx
    let failedExprs := diagResult.diagnosedFailures.map (·.expression)
    let isRefuted := diagResult.diagnosedFailures.any (·.isRefuted)
    return { result with diagnosis := some { isRefuted, failedSubExpressions := failedExprs } }

/-- Verify a list of CoreSMT statements. Returns updated state and check results. -/
def verify (state : CoreSMTState) (E : Core.Env) (stmts : List Core.Statement)
    (smtCtx : Core.SMT.Context := Core.SMT.Context.default)
    : IO (CoreSMTState × Core.SMT.Context × List Core.VCResult) := do
  let (state, smtCtx, results) ← processStatements state E stmts smtCtx
  -- Add diagnosis to failed results
  let mut diagnosedResults := []
  for result in results do
    let diagnosed ← addDiagnosis state E result smtCtx
    diagnosedResults := diagnosedResults ++ [diagnosed]
  return (state, smtCtx, diagnosedResults)

/-- Process prelude statements to initialize state for subsequent verification.
    Returns state ready for reuse across multiple verify calls. -/
def processPrelude (state : CoreSMTState) (E : Core.Env)
    (prelude : List Core.Statement)
    (smtCtx : Core.SMT.Context := Core.SMT.Context.default)
    : IO (CoreSMTState × Core.SMT.Context) := do
  let (state, smtCtx, _) ← processStatements state E prelude smtCtx
  return (state, smtCtx)

end Strata.Core.CoreSMT

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreSMT.StmtVerifier

/-!
# CoreSMT Verifier Public Interface

Provides the main entry point for verifying CoreSMT programs. The verifier
processes statements sequentially, accumulating results and returning updated
state for reuse.
-/

namespace Strata.Core.CoreSMT

/-- Verify a list of CoreSMT statements. Returns updated state and check results. -/
def verify (state : CoreSMTState) (E : Core.Env) (stmts : List Core.Statement)
    (smtCtx : Core.SMT.Context := Core.SMT.Context.default)
    : IO (CoreSMTState × Core.SMT.Context × List Core.VCResult) :=
  processStatements state E stmts smtCtx

/-- Process prelude statements to initialize state for subsequent verification.
    Returns state ready for reuse across multiple verify calls. -/
def processPrelude (state : CoreSMTState) (E : Core.Env)
    (prelude : List Core.Statement)
    (smtCtx : Core.SMT.Context := Core.SMT.Context.default)
    : IO (CoreSMTState × Core.SMT.Context) := do
  let (state, smtCtx, _) ← processStatements state E prelude smtCtx
  return (state, smtCtx)

end Strata.Core.CoreSMT

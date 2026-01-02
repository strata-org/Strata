/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Core
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.Verifier.Statements
import Strata.Languages.B3.Verifier.ExecuteWithDiagnosis

/-!
# Automatic Verification with Diagnosis

Verifies B3 programs and automatically diagnoses failures to identify root causes.

## Workflow

1. Build program state (functions, axioms)
2. For each parameter-free procedure:
   - Generate VCs from body
   - Check each VC
   - If failed, automatically diagnose to find root cause
3. Report all results with diagnosements

This is the main entry point for verification with automatic debugging.
-/

namespace Strata.B3.Verifier

open Strata.SMT

structure VerificationReport where
  procedureName : String
  results : List (CheckResult × Option DiagnosisResult)  -- Each VC with optional diagnosement

/-- Verify a B3 program with automatic diagnosis -/
def verifyWithDiagnosis (prog : Strata.B3AST.Program SourceRange) (solverPath : String := "z3") : IO (List VerificationReport) := do
  let solver ← createInteractiveSolver solverPath
  let state ← buildProgramState prog solver
  let mut reports := []

  match prog with
  | .program _ decls =>
      for decl in decls.val.toList do
        match decl with
        | .procedure _ name params _ body =>
            if params.val.isEmpty && body.val.isSome then
              let bodyStmt := body.val.get!
              let (results, _finalState) ← executeStatementsWithDiagnosis ConversionContext.empty state decl bodyStmt

              reports := reports ++ [{
                procedureName := name.val
                results := results
              }]
            else
              pure ()
        | _ => pure ()

  closeVerificationState state
  return reports

end Strata.B3.Verifier

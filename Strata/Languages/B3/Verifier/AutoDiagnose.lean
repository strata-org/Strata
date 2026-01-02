/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Core
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.Verifier.Statements

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

/-- Verify a B3 program with automatic diagnosement on failures -/
def verifyWithDiagnosis (prog : Strata.B3AST.Program SourceRange) (solverPath : String := "z3") : IO (List VerificationReport) := do
  let state ← buildProgramState prog solverPath
  let mut reports := []

  match prog with
  | .program _ decls =>
      -- Verify each parameter-free procedure
      for decl in decls.val.toList do
        match decl with
        | .procedure _ name params _ body =>
            if params.val.isEmpty && body.val.isSome then
              let bodyStmt := body.val.get!
              let vcState := statementToVCs ConversionContext.empty VCGenState.empty bodyStmt

              let mut procResults := []
              let mut currentState := state

              -- Check VCs sequentially, accumulating successful asserts
              for (vc, sourceStmt) in vcState.verificationConditions.reverse do
                let (result, diagnosis, newState) ← match sourceStmt with
                  | .check _ expr =>
                      let result ← prove currentState vc decl (some sourceStmt)
                      let diag ← if result.decision != .unsat then
                        let d ← diagnoseFailure currentState expr decl sourceStmt
                        pure (some d)
                      else
                        pure none
                      pure (result, diag, currentState)

                  | .assert _ expr =>
                      let result ← prove currentState vc decl (some sourceStmt)
                      let diag ← if result.decision != .unsat then
                        let d ← diagnoseFailure currentState expr decl sourceStmt
                        pure (some d)
                      else
                        pure none
                      -- Add successful assert to state
                      let newState ← if result.decision == .unsat then
                        addAxiom currentState vc
                      else
                        pure currentState
                      pure (result, diag, newState)

                  | .reach _ expr =>
                      let result ← reach currentState vc decl (some sourceStmt)
                      let diag ← if result.decision == .unsat then
                        let d ← diagnoseUnreachable currentState expr decl sourceStmt
                        pure (some d)
                      else
                        pure none
                      pure (result, diag, currentState)

                  | _ =>
                      let result ← prove currentState vc decl (some sourceStmt)
                      pure (result, none, currentState)

                currentState := newState
                procResults := procResults ++ [(result, diagnosis)]

              reports := reports ++ [{
                procedureName := name.val
                results := procResults
              }]
            else
              pure ()  -- Skip procedures with parameters
        | _ => pure ()

  closeVerificationState state
  return reports

end Strata.B3.Verifier

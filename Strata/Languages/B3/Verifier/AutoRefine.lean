/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Core
import Strata.Languages.B3.Verifier.Refinement
import Strata.Languages.B3.Verifier.Statements

/-!
# Automatic Verification with Refinement

Verifies B3 programs and automatically refines failures to identify root causes.

## Workflow

1. Build program state (functions, axioms)
2. For each parameter-free procedure:
   - Generate VCs from body
   - Check each VC
   - If failed, automatically refine to find root cause
3. Report all results with refinements

This is the main entry point for verification with automatic debugging.
-/

namespace Strata.B3.Verifier

open Strata.SMT

structure VerificationReport where
  procedureName : String
  results : List (CheckResult × Option RefinementResult)  -- Each VC with optional refinement

/-- Verify a B3 program with automatic refinement on failures -/
def verifyWithRefinement (prog : Strata.B3AST.Program SourceRange) (solverPath : String := "z3") : IO (List VerificationReport) := do
  let state := buildProgramState prog
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
              -- Check each VC
              for (vc, sourceStmt) in vcState.verificationConditions.reverse do
                let result ← checkProperty state vc decl (some sourceStmt) solverPath

                -- If failed, try refinement
                let refinement ← if result.decision != .unsat then
                  -- Extract the expression from the source statement
                  match sourceStmt with
                  | .check _ expr =>
                      let refResult ← refineFailure state expr decl sourceStmt solverPath
                      pure (some refResult)
                  | .assert _ expr =>
                      let refResult ← refineFailure state expr decl sourceStmt solverPath
                      pure (some refResult)
                  | _ => pure none
                else
                  pure none

                procResults := procResults ++ [(result, refinement)]

              reports := reports ++ [{
                procedureName := name.val
                results := procResults
              }]
            else
              pure ()  -- Skip procedures with parameters
        | _ => pure ()

  return reports

end Strata.B3.Verifier

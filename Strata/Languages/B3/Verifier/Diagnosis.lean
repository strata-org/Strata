/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion

/-!
# Verification Diagnosis Strategies

Interactive debugging strategies for failed verifications.

When a verification fails, these strategies help identify the root cause by:
- Splitting conjunctions to find which conjunct fails
- Inlining definitions
- Simplifying expressions
-/

namespace Strata.B3.Verifier

open Strata.SMT

structure DiagnosisResult where
  originalCheck : CheckResult
  diagnosedFailures : List (String × B3AST.Expression SourceRange × CheckResult)  -- Description, expression, result

/-- Automatically diagnose a failed check to find root cause -/
def diagnoseFailureGeneric
    (checkFn : B3VerificationState → Term → B3AST.Decl SourceRange → Option (B3AST.Statement SourceRange) → IO CheckResult)
    (isFailure : B3Result → Bool)
    (state : B3VerificationState)
    (expr : B3AST.Expression SourceRange)
    (sourceDecl : B3AST.Decl SourceRange)
    (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult := do
  match expressionToSMT ConversionContext.empty expr with
  | .error _ =>
      let dummyResult : CheckResult := {
        decl := sourceDecl
        sourceStmt := some sourceStmt
        result := .checkResult .proofUnknown  -- Conversion failure treated as unknown
        model := none
      }
      return { originalCheck := dummyResult, diagnosedFailures := [] }
  | .ok term =>
      let originalResult ← checkFn state term sourceDecl (some sourceStmt)

      if !isFailure originalResult.result then
        return { originalCheck := originalResult, diagnosedFailures := [] }

      let mut diagnosements := []

      -- Strategy: Split conjunctions
      match expr with
      | .binaryOp _ (.and _) lhs rhs =>
          match expressionToSMT ConversionContext.empty lhs with
          | .ok lhsTerm =>
              let lhsResult ← checkFn state lhsTerm sourceDecl (some sourceStmt)
              if isFailure lhsResult.result then
                diagnosements := diagnosements ++ [("left conjunct", lhs, lhsResult)]
          | .error _ => pure ()

          match expressionToSMT ConversionContext.empty rhs with
          | .ok rhsTerm =>
              let rhsResult ← checkFn state rhsTerm sourceDecl (some sourceStmt)
              if isFailure rhsResult.result then
                diagnosements := diagnosements ++ [("right conjunct", rhs, rhsResult)]
          | .error _ => pure ()
      | _ => pure ()

      return { originalCheck := originalResult, diagnosedFailures := diagnosements }

/-- Diagnose a failed check/assert -/
def diagnoseFailure (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult :=
  diagnoseFailureGeneric prove (fun r => r.isError) state expr sourceDecl sourceStmt

/-- Diagnose an unreachable reach -/
def diagnoseUnreachable (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult :=
  diagnoseFailureGeneric reach (fun r => r.isError) state expr sourceDecl sourceStmt

end Strata.B3.Verifier

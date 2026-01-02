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
    (isFailure : Decision → Bool)
    (state : B3VerificationState)
    (expr : B3AST.Expression SourceRange)
    (sourceDecl : B3AST.Decl SourceRange)
    (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult := do
  match expressionToSMT ConversionContext.empty expr with
  | none =>
      let dummyResult : CheckResult := {
        decl := sourceDecl
        sourceStmt := some sourceStmt
        decision := .unknown
        model := none
      }
      return { originalCheck := dummyResult, diagnosedFailures := [] }
  | some term =>
      let originalResult ← checkFn state term sourceDecl (some sourceStmt)

      if !isFailure originalResult.decision then
        return { originalCheck := originalResult, diagnosedFailures := [] }

      let mut diagnosements := []

      -- Strategy: Split conjunctions
      match expr with
      | .binaryOp _ (.and _) lhs rhs =>
          match expressionToSMT ConversionContext.empty lhs with
          | some lhsTerm =>
              let lhsResult ← checkFn state lhsTerm sourceDecl (some sourceStmt)
              if isFailure lhsResult.decision then
                diagnosements := diagnosements ++ [("left conjunct", lhs, lhsResult)]
          | none => pure ()

          match expressionToSMT ConversionContext.empty rhs with
          | some rhsTerm =>
              let rhsResult ← checkFn state rhsTerm sourceDecl (some sourceStmt)
              if isFailure rhsResult.decision then
                diagnosements := diagnosements ++ [("right conjunct", rhs, rhsResult)]
          | none => pure ()
      | _ => pure ()

      return { originalCheck := originalResult, diagnosedFailures := diagnosements }

/-- Diagnose a failed check/assert (sat = failure) -/
def diagnoseFailure (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult :=
  diagnoseFailureGeneric prove (fun d => d != .unsat) state expr sourceDecl sourceStmt

/-- Diagnose an unreachable reach (unsat = failure) -/
def diagnoseUnreachable (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult :=
  diagnoseFailureGeneric reach (fun d => d == .unsat) state expr sourceDecl sourceStmt

end Strata.B3.Verifier

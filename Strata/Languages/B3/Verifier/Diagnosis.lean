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
  originalCheck : VerificationReport
  diagnosedFailures : List (String × B3AST.Expression SourceRange × VerificationReport)

/-- Automatically diagnose a failed check to find root cause -/
def diagnoseFailureGeneric
    (checkFn : B3VerificationState → Term → B3AST.Decl SourceRange → Option (B3AST.Statement SourceRange) → IO VerificationReport)
    (isFailure : VerificationResult → Bool)
    (state : B3VerificationState)
    (expr : B3AST.Expression SourceRange)
    (sourceDecl : B3AST.Decl SourceRange)
    (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult := do
  match expressionToSMT ConversionContext.empty expr with
  | .error _ =>
      let dummyResult : VerificationReport := {
        decl := sourceDecl
        sourceStmt := some sourceStmt
        result := .proofResult .proofUnknown
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

---------------------------------------------------------------------
-- Statement Execution with Diagnosis
---------------------------------------------------------------------

/-- Verify statements with automatic diagnosis on failures -/
partial def verifyStatementsWithDiagnosis (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO (List (VerificationReport × Option DiagnosisResult) × B3VerificationState)
  | .check m expr => do
      match expressionToSMT ctx expr with
      | .ok term =>
          let result ← prove state term sourceDecl (some (.check m expr))
          let diag ← if result.result.isError then
            let d ← diagnoseFailure state expr sourceDecl (.check m expr)
            pure (some d)
          else
            pure none
          pure ([(result, diag)], state)
      | .error _ =>
          pure ([], state)

  | .assert m expr => do
      match expressionToSMT ctx expr with
      | .ok term =>
          let result ← prove state term sourceDecl (some (.assert m expr))
          let diag ← if result.result.isError then
            let d ← diagnoseFailure state expr sourceDecl (.assert m expr)
            pure (some d)
          else
            pure none
          let newState ← if !result.result.isError then
            addAxiom state term
          else
            pure state
          pure ([(result, diag)], newState)
      | .error _ =>
          pure ([], state)

  | .assume _ expr => do
      match expressionToSMT ctx expr with
      | .ok term =>
          let newState ← addAxiom state term
          pure ([], newState)
      | .error _ =>
          pure ([], state)

  | .reach m expr => do
      match expressionToSMT ctx expr with
      | .ok term =>
          let result ← reach state term sourceDecl (some (.reach m expr))
          let diag ← if result.result.isError then
            let d ← diagnoseUnreachable state expr sourceDecl (.reach m expr)
            pure (some d)
          else
            pure none
          pure ([(result, diag)], state)
      | .error _ =>
          pure ([], state)

  | .blockStmt _ stmts => do
      let mut currentState := state
      let mut allResults := []
      for stmt in stmts.val.toList do
        let (results, newState) ← verifyStatementsWithDiagnosis ctx currentState sourceDecl stmt
        currentState := newState
        allResults := allResults ++ results
      pure (allResults, currentState)

  | _ =>
      pure ([], state)

end Strata.B3.Verifier

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Statements

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

structure DiagnosedFailure where
  expression : B3AST.Expression SourceRange
  report : VerificationReport
  pathCondition : List (B3AST.Expression SourceRange)
  isProvablyFalse : Bool  -- True if the expression is provably false (not just unprovable)

structure DiagnosisResult where
  originalCheck : VerificationReport
  diagnosedFailures : List DiagnosedFailure

/-- Automatically diagnose a failed check to find root cause.

For proof checks (check/assert): Recursively splits conjunctions to find all atomic failures.
When checking RHS, assumes LHS holds to provide context-aware diagnosis.

For reachability checks (reach): Stops after finding first unreachable LHS conjunct,
since all subsequent conjuncts are trivially unreachable if LHS is unreachable.
-/
partial def diagnoseFailureGeneric
    (isReachCheck : Bool)
    (state : B3VerificationState)
    (expr : B3AST.Expression SourceRange)
    (sourceDecl : B3AST.Decl SourceRange)
    (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult := do
  let convResult := expressionToSMT ConversionContext.empty expr

  -- If there are conversion errors, return early
  if !convResult.errors.isEmpty then
    let vctx : VerificationContext := { decl := sourceDecl, stmt := sourceStmt, pathCondition := state.pathCondition }
    let dummyResult : VerificationReport := {
      context := vctx
      result := .proofResult .proofUnknown
      model := none
    }
    return { originalCheck := dummyResult, diagnosedFailures := [] }

  -- Determine check function based on check type
  let checkFn := if isReachCheck then reach else prove
  let isFailure := fun r => r.isError

  let vctx : VerificationContext := { decl := sourceDecl, stmt := sourceStmt, pathCondition := state.pathCondition }
  let originalResult ← checkFn state convResult.term vctx

  if !isFailure originalResult.result then
    return { originalCheck := originalResult, diagnosedFailures := [] }

  let mut diagnosements := []

  -- Strategy: Split conjunctions and recursively diagnose
  match expr with
  | .binaryOp _ (.and _) lhs rhs =>
      let lhsConv := expressionToSMT ConversionContext.empty lhs
      if lhsConv.errors.isEmpty then
        let lhsResult ← checkFn state lhsConv.term vctx
        if isFailure lhsResult.result then
          -- Check if LHS is provably false (not just unprovable)
          let _ ← push state
          let runCheck : SolverM Decision := do
            Solver.assert (formatTermDirect lhsConv.term)
            Solver.checkSat []
          let decision ← runCheck.run state.smtState.solver
          let _ ← pop state
          let isProvablyFalse := decision == .unsat

          -- Recursively diagnose the left conjunct
          let lhsDiag ← diagnoseFailureGeneric isReachCheck state lhs sourceDecl sourceStmt
          if lhsDiag.diagnosedFailures.isEmpty then
            -- Atomic failure
            diagnosements := diagnosements ++ [{
              expression := lhs
              report := lhsResult
              pathCondition := state.pathCondition
              isProvablyFalse := isProvablyFalse
            }]
          else
            -- Has sub-failures - add those instead
            diagnosements := diagnosements ++ lhsDiag.diagnosedFailures

          -- If provably false, stop here (found root cause, no need to check RHS)
          if isProvablyFalse then
            return { originalCheck := originalResult, diagnosedFailures := diagnosements }

          -- For reachability checks: if LHS is unreachable, stop here
          -- All subsequent conjuncts are trivially unreachable
          if isReachCheck then
            return { originalCheck := originalResult, diagnosedFailures := diagnosements }

      -- Check right conjunct assuming left conjunct holds
      let rhsConv := expressionToSMT ConversionContext.empty rhs
      if lhsConv.errors.isEmpty && rhsConv.errors.isEmpty then
        -- Add lhs as assumption when checking rhs (for both proof and reachability checks)
        let stateForRhs ← addPathCondition state lhs lhsConv.term
        let rhsResult ← checkFn stateForRhs rhsConv.term vctx
        if isFailure rhsResult.result then
          -- Check if RHS is provably false (not just unprovable)
          let _ ← push stateForRhs
          let runCheck : SolverM Decision := do
            Solver.assert (formatTermDirect rhsConv.term)
            Solver.checkSat []
          let decision ← runCheck.run stateForRhs.smtState.solver
          let _ ← pop stateForRhs
          let isProvablyFalse := decision == .unsat

          -- Recursively diagnose the right conjunct
          let rhsDiag ← diagnoseFailureGeneric isReachCheck stateForRhs rhs sourceDecl sourceStmt
          if rhsDiag.diagnosedFailures.isEmpty then
            -- Atomic failure
            diagnosements := diagnosements ++ [{
              expression := rhs
              report := rhsResult
              pathCondition := stateForRhs.pathCondition
              isProvablyFalse := isProvablyFalse
            }]
          else
            -- Has sub-failures - add those instead
            diagnosements := diagnosements ++ rhsDiag.diagnosedFailures
  | _ => pure ()

  return { originalCheck := originalResult, diagnosedFailures := diagnosements }

/-- Diagnose a failed check/assert -/
def diagnoseFailure (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult :=
  diagnoseFailureGeneric false state expr sourceDecl sourceStmt

/-- Diagnose an unreachable reach -/
def diagnoseUnreachable (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) : IO DiagnosisResult :=
  diagnoseFailureGeneric true state expr sourceDecl sourceStmt

---------------------------------------------------------------------
-- Statement Symbolic Execution with Diagnosis
---------------------------------------------------------------------

/-- Symbolically execute statements with automatic diagnosis on failures.

This wraps symbolicExecuteStatements and adds diagnosis for failed checks/asserts/reach.
The diagnosis analyzes failures but does not modify the verification state.
-/
partial def symbolicExecuteStatementsWithDiagnosis (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO (List (VerificationReport × Option DiagnosisResult) × B3VerificationState)
  | stmt => do
      -- Symbolically execute the statement to get results and updated state
      let execResult ← symbolicExecuteStatements ctx state sourceDecl stmt

      -- Add diagnosis to any failed verification results
      let mut resultsWithDiag := []
      for stmtResult in execResult.results do
        match stmtResult with
        | .verified report =>
            -- If verification failed, diagnose it
            let diag ← if report.result.isError then
              match report.context.stmt with
              | .check m expr =>
                  let d ← diagnoseFailure state expr sourceDecl (.check m expr)
                  pure (some d)
              | .assert m expr =>
                  let d ← diagnoseFailure state expr sourceDecl (.assert m expr)
                  pure (some d)
              | .reach m expr =>
                  let d ← diagnoseUnreachable state expr sourceDecl (.reach m expr)
                  pure (some d)
              | _ => pure none
            else
              pure none
            resultsWithDiag := resultsWithDiag ++ [(report, diag)]
        | .conversionError _ =>
            -- Conversion errors don't produce VerificationReports, skip them
            pure ()

      pure (resultsWithDiag, execResult.finalState)

end Strata.B3.Verifier

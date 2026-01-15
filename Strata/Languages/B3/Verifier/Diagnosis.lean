/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Expression
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

---------------------------------------------------------------------
-- Pure Helper Functions
---------------------------------------------------------------------

/-- Extract conjunction operands if expression is a conjunction, otherwise return none -/
def splitConjunction (expr : B3AST.Expression SourceRange) : Option (B3AST.Expression SourceRange × B3AST.Expression SourceRange) :=
  match expr with
  | .binaryOp _ (.and _) lhs rhs => some (lhs, rhs)
  | _ => none

/-- Determine if diagnosis should stop early based on check type and failure status -/
def shouldStopDiagnosis (isReachCheck : Bool) (isProvablyFalse : Bool) : Bool :=
  isProvablyFalse || isReachCheck

/-- Upgrade verification result to refuted if provably false -/
def upgradeToRefutedIfNeeded (result : VerificationReport) (isProvablyFalse : Bool) : VerificationReport :=
  if isProvablyFalse then
    { result with result := .error .refuted }
  else
    result

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
      result := .error .unknown
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
  match splitConjunction expr with
  | some (lhs, rhs) =>
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
            -- Atomic failure - upgrade to refuted if provably false
            let finalResult := upgradeToRefutedIfNeeded lhsResult isProvablyFalse
            diagnosements := diagnosements ++ [{
              expression := lhs
              report := finalResult
            }]
          else
            -- Has sub-failures - add those instead
            diagnosements := diagnosements ++ lhsDiag.diagnosedFailures

          -- Stop early if needed (provably false or reachability check)
          if shouldStopDiagnosis isReachCheck isProvablyFalse then
            return { originalCheck := originalResult, diagnosedFailures := diagnosements }

      -- Check right conjunct assuming left conjunct holds
      let rhsConv := expressionToSMT ConversionContext.empty rhs
      if lhsConv.errors.isEmpty && rhsConv.errors.isEmpty then
        -- Add lhs as assumption when checking rhs (for both proof and reachability checks)
        let stateForRhs ← addPathCondition state lhs lhsConv.term
        let vctxForRhs : VerificationContext := { decl := sourceDecl, stmt := sourceStmt, pathCondition := stateForRhs.pathCondition }
        let rhsResult ← checkFn stateForRhs rhsConv.term vctxForRhs
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
            -- Atomic failure - upgrade to refuted if provably false
            let finalResult := upgradeToRefutedIfNeeded rhsResult isProvablyFalse
            diagnosements := diagnosements ++ [{
              expression := rhs
              report := finalResult
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

/-- Determine which diagnosis function to use based on statement type -/
def diagnoseFailed (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) (stmt : B3AST.Statement SourceRange) : IO (Option DiagnosisResult) :=
  match stmt with
  | .check m expr => do
      let d ← diagnoseFailure state expr sourceDecl (.check m expr)
      pure (some d)
  | .assert m expr => do
      let d ← diagnoseFailure state expr sourceDecl (.assert m expr)
      pure (some d)
  | .reach m expr => do
      let d ← diagnoseUnreachable state expr sourceDecl (.reach m expr)
      pure (some d)
  | _ => pure none

---------------------------------------------------------------------
-- Statement Symbolic Execution with Diagnosis
---------------------------------------------------------------------

/-- Translate statements to SMT with automatic diagnosis on failures (default, recommended).

This adds diagnosis for failed checks/asserts/reach to help identify root causes.
The diagnosis analyzes failures but does not modify the verification state.

For faster verification without diagnosis, use statementToSMTWithoutDiagnosis.
-/
partial def statementToSMT (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO SymbolicExecutionResult
  | stmt => do
      -- Translate the statement to SMT and get results
      let execResult ← statementToSMTWithoutDiagnosis ctx state sourceDecl stmt

      -- Add diagnosis to any failed verification results
      let mut resultsWithDiagRev := []
      for (stmtResult, _) in execResult.results do
        match stmtResult with
        | .verified report =>
            -- If verification failed, diagnose it
            let diag ← if report.result.isError then
              diagnoseFailed state sourceDecl report.context.stmt
            else
              pure none
            resultsWithDiagRev := (stmtResult, diag) :: resultsWithDiagRev
        | .conversionError _ =>
            -- Conversion errors don't have diagnosis
            resultsWithDiagRev := (stmtResult, none) :: resultsWithDiagRev

      pure { results := resultsWithDiagRev.reverse, finalState := execResult.finalState }

end Strata.B3.Verifier

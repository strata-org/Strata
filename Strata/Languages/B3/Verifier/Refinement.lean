/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion

/-!
# Verification Refinement Strategies

Interactive debugging strategies for failed verifications.

When a verification fails, these strategies help identify the root cause by:
- Splitting conjunctions to find which conjunct fails
- Inlining definitions
- Simplifying expressions
-/

namespace Strata.B3.Verifier

open Strata.SMT

structure RefinementResult where
  originalCheck : CheckResult
  refinedFailures : List (String × B3AST.Expression SourceRange × CheckResult)  -- Description, expression, result

/-- Automatically refine a failed check to find root cause -/
def refineFailure (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : B3AST.Statement SourceRange) (solverPath : String := "z3") : IO RefinementResult := do
  match expressionToSMT ConversionContext.empty expr with
  | none =>
      let dummyResult : CheckResult := {
        decl := sourceDecl
        sourceStmt := some sourceStmt
        decision := .unknown
        model := none
      }
      return { originalCheck := dummyResult, refinedFailures := [] }
  | some term =>
      let originalResult ← checkProperty state term sourceDecl (some sourceStmt) solverPath

      if originalResult.decision == .unsat then
        return { originalCheck := originalResult, refinedFailures := [] }

      let mut refinements := []

      -- Strategy: Split conjunctions
      match expr with
      | .binaryOp _ (.and _) lhs rhs =>
          match expressionToSMT ConversionContext.empty lhs with
          | some lhsTerm =>
              let lhsResult ← checkProperty state lhsTerm sourceDecl (some sourceStmt) solverPath
              if lhsResult.decision != .unsat then
                refinements := refinements ++ [("left conjunct", lhs, lhsResult)]
          | none => pure ()

          match expressionToSMT ConversionContext.empty rhs with
          | some rhsTerm =>
              let rhsResult ← checkProperty state rhsTerm sourceDecl (some sourceStmt) solverPath
              if rhsResult.decision != .unsat then
                refinements := refinements ++ [("right conjunct", rhs, rhsResult)]
          | none => pure ()
      | _ => pure ()

      return { originalCheck := originalResult, refinedFailures := refinements }

end Strata.B3.Verifier

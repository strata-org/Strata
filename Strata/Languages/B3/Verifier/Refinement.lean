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
  fullCheck : CheckResult
  refinements : List (String × CheckResult)  -- Description and result for each refinement

/-- Split a conjunction and check each side separately -/
def refineConjunction (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (sourceDecl : B3AST.Decl SourceRange) (solverPath : String := "z3") : IO RefinementResult := do
  -- Check the full expression first
  match expressionToSMT ConversionContext.empty expr with
  | none =>
      let dummyResult : CheckResult := {
        decl := sourceDecl
        sourceStmt := none
        decision := .unknown
        model := none
      }
      return { fullCheck := dummyResult, refinements := [] }
  | some fullTerm =>
      let fullResult ← checkProperty state fullTerm sourceDecl none solverPath

      -- If verified, no need to refine
      if fullResult.decision == .unsat then
        return { fullCheck := fullResult, refinements := [] }

      -- Try to split if it's a conjunction
      match expr with
      | .binaryOp _ (.and _) lhs rhs =>
          let mut refinements := []

          -- Check left side
          match expressionToSMT ConversionContext.empty lhs with
          | some lhsTerm =>
              let lhsResult ← checkProperty state lhsTerm sourceDecl none solverPath
              refinements := refinements ++ [("left conjunct", lhsResult)]
          | none => pure ()

          -- Check right side
          match expressionToSMT ConversionContext.empty rhs with
          | some rhsTerm =>
              let rhsResult ← checkProperty state rhsTerm sourceDecl none solverPath
              refinements := refinements ++ [("right conjunct", rhsResult)]
          | none => pure ()

          return { fullCheck := fullResult, refinements := refinements }
      | _ =>
          return { fullCheck := fullResult, refinements := [] }

end Strata.B3.Verifier

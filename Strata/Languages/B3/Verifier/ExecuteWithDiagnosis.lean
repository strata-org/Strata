/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Statements
import Strata.Languages.B3.Verifier.Diagnosis

/-!
# Statement Execution with Automatic Diagnosis

Executes B3 statements with automatic diagnosis on failures.
-/

namespace Strata.B3.Verifier

open Strata.SMT

/-- Execute statements with automatic diagnosis on failures -/
partial def executeStatementsWithDiagnosis (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO (List (CheckResult × Option DiagnosisResult) × B3VerificationState)
  | .check m expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let result ← prove state term sourceDecl (some (.check m expr))
          let diag ← if result.result.isError then
            let d ← diagnoseFailure state expr sourceDecl (.check m expr)
            pure (some d)
          else
            pure none
          pure ([(result, diag)], state)
      | none =>
          pure ([], state)

  | .assert m expr => do
      match expressionToSMT ctx expr with
      | some term =>
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
      | none =>
          pure ([], state)

  | .assume _ expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let newState ← addAxiom state term
          pure ([], newState)
      | none =>
          pure ([], state)

  | .reach m expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let result ← reach state term sourceDecl (some (.reach m expr))
          let diag ← if result.result.isError then  -- Diagnose when unreachable (error)
            let d ← diagnoseUnreachable state expr sourceDecl (.reach m expr)
            pure (some d)
          else
            pure none
          pure ([(result, diag)], state)
      | none =>
          pure ([], state)

  | .blockStmt _ stmts => do
      let mut currentState := state
      let mut allResults := []
      for stmt in stmts.val.toList do
        let (results, newState) ← executeStatementsWithDiagnosis ctx currentState sourceDecl stmt
        currentState := newState
        allResults := allResults ++ results
      pure (allResults, currentState)

  | _ =>
      pure ([], state)

end Strata.B3.Verifier

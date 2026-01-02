/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.State

/-!
# B3 Statement Streaming Translation

Translates B3 statements to SMT via streaming execution (NOT batch VCG).

## Streaming Translation

Statements are translated and executed immediately:
- `assert e` - prove e, then add to solver state
- `check e` - prove e (push/pop, doesn't affect state)
- `assume e` - add to solver state
- `reach e` - check satisfiability (push/pop)

This allows the solver to learn from asserts, making later checks easier.
Key advantage: O(n) not O(n²), solver accumulates lemmas.
-/

namespace Strata.B3.Verifier

open Strata.SMT

inductive StatementResult where
  | verified : CheckResult → StatementResult  -- Successful check/reach/assert
  | conversionError : String → StatementResult

structure ExecutionResult where
  results : List StatementResult
  finalState : B3VerificationState

/-- Execute B3 statements via streaming translation to SMT -/
partial def executeStatements (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO ExecutionResult
  | .check m expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let result ← prove state term sourceDecl (some (.check m expr))
          pure { results := [.verified result], finalState := state }
      | none =>
          pure { results := [.conversionError "Failed to convert expression to SMT"], finalState := state }

  | .assert m expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let result ← prove state term sourceDecl (some (.assert m expr))
          -- Add to solver state if successful (not an error)
          let newState ← if !result.result.isError then
            addAxiom state term
          else
            pure state
          pure { results := [.verified result], finalState := newState }
      | none =>
          pure { results := [.conversionError "Failed to convert expression to SMT"], finalState := state }

  | .assume _ expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let newState ← addAxiom state term
          pure { results := [], finalState := newState }
      | none =>
          pure { results := [.conversionError "Failed to convert expression to SMT"], finalState := state }

  | .reach m expr => do
      match expressionToSMT ctx expr with
      | some term =>
          let result ← reach state term sourceDecl (some (.reach m expr))
          pure { results := [.verified result], finalState := state }
      | none =>
          pure { results := [.conversionError "Failed to convert expression to SMT"], finalState := state }

  | .blockStmt _ stmts => do
      let mut currentState := state
      let mut allResults := []
      for stmt in stmts.val.toList do
        let execResult ← executeStatements ctx currentState sourceDecl stmt
        currentState := execResult.finalState
        allResults := allResults ++ execResult.results
      pure { results := allResults, finalState := currentState }

  | _ =>
      pure { results := [], finalState := state }

end Strata.B3.Verifier

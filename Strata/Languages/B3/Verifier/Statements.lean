/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.State

/-!
# B3 Statement Streaming Translation

Translates B3 statements to SMT via streaming symbolic execution (NOT batch VCG).

## Streaming Symbolic Execution

Statements are translated and symbolically executed immediately:
- `assert e` - prove e, then add to solver state (assumes e regardless of proof result)
- `check e` - prove e (push/pop, doesn't affect state)
- `assume e` - add to solver state
- `reach e` - check satisfiability (push/pop)

This allows the solver to learn from asserts, making later checks easier.
Key advantage: O(n) not O(n²), solver accumulates lemmas.
-/

namespace Strata.B3.Verifier

open Strata.SMT

inductive StatementResult where
  | verified : VerificationReport → StatementResult
  | conversionError : String → StatementResult

structure SymbolicExecutionResult where
  results : List StatementResult
  finalState : B3VerificationState

/-- Symbolically execute B3 statements via streaming translation to SMT -/
partial def symbolicExecuteStatements (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO SymbolicExecutionResult
  | .check m expr => do
      let convResult := expressionToSMT ctx expr
      let result ← prove state convResult.term sourceDecl (some (.check m expr))
      let errorResults := convResult.errors.map (fun err => StatementResult.conversionError (toString err))
      pure { results := errorResults ++ [.verified result], finalState := state }

  | .assert m expr => do
      let convResult := expressionToSMT ctx expr
      let result ← prove state convResult.term sourceDecl (some (.assert m expr))
      -- Always add to solver state (assert assumes its condition regardless of proof result)
      let newState ← addPathCondition state expr convResult.term
      let errorResults := convResult.errors.map (fun err => StatementResult.conversionError (toString err))
      pure { results := errorResults ++ [.verified result], finalState := newState }

  | .assume _ expr => do
      let convResult := expressionToSMT ctx expr
      let newState ← addPathCondition state expr convResult.term
      let errorResults := convResult.errors.map (fun err => StatementResult.conversionError (toString err))
      pure { results := errorResults, finalState := newState }

  | .reach m expr => do
      let convResult := expressionToSMT ctx expr
      let result ← reach state convResult.term sourceDecl (some (.reach m expr))
      let errorResults := convResult.errors.map (fun err => StatementResult.conversionError (toString err))
      pure { results := errorResults ++ [.verified result], finalState := state }

  | .blockStmt _ stmts => do
      let mut currentState := state
      let mut allResults := []
      for stmt in stmts.val.toList do
        let execResult ← symbolicExecuteStatements ctx currentState sourceDecl stmt
        currentState := execResult.finalState
        allResults := allResults ++ execResult.results
      pure { results := allResults, finalState := currentState }

  | _ =>
      pure { results := [], finalState := state }

end Strata.B3.Verifier

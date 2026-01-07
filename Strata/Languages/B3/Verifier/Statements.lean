/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Expression
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion
import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

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

open Strata
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
      let vctx : VerificationContext := { decl := sourceDecl, stmt := .check m expr, pathCondition := state.pathCondition }
      let result ← prove state convResult.term vctx
      let errorResults := convResult.errors.map (fun err => StatementResult.conversionError (toString err))
      pure { results := errorResults ++ [.verified result], finalState := state }

  | .assert m expr => do
      let convResult := expressionToSMT ctx expr
      let vctx : VerificationContext := { decl := sourceDecl, stmt := .assert m expr, pathCondition := state.pathCondition }
      let result ← prove state convResult.term vctx
      -- Always add to path condition (assert assumes its condition regardless of proof result)
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
      let vctx : VerificationContext := { decl := sourceDecl, stmt := .reach m expr, pathCondition := state.pathCondition }
      let result ← reach state convResult.term vctx
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

---------------------------------------------------------------------
-- Statement Formatting
---------------------------------------------------------------------

def formatStatement (prog : Program) (stmt : B3AST.Statement SourceRange) (ctx: B3.ToCSTContext): String :=
  let (cstStmt, _) := B3.stmtToCST ctx stmt
  let fmtCtx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  (mformat (ArgF.op cstStmt.toAst) fmtCtx fmtState).format.pretty.trim

---------------------------------------------------------------------
-- Metadata Extraction
---------------------------------------------------------------------

/-- Extract metadata from any B3 statement -/
def getStatementMetadata : B3AST.Statement M → M
  | .check m _ => m
  | .assert m _ => m
  | .assume m _ => m
  | .reach m _ => m
  | .blockStmt m _ => m
  | .probe m _ => m
  | .varDecl m _ _ _ _ => m
  | .assign m _ _ => m
  | .reinit m _ => m
  | .ifStmt m _ _ _ => m
  | .ifCase m _ => m
  | .choose m _ => m
  | .loop m _ _ => m
  | .labeledStmt m _ _ => m
  | .exit m _ => m
  | .returnStmt m => m
  | .aForall m _ _ _ => m
  | .call m _ _ => m

end Strata.B3.Verifier

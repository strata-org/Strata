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
import Strata.Util.Tactics

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

/-- Convert StatementResult to Except for easier error handling -/
def StatementResult.toExcept : StatementResult → Except String VerificationReport
  | .verified report => .ok report
  | .conversionError msg => .error msg

structure SymbolicExecutionResult where
  results : List (StatementResult × Option DiagnosisResult)
  finalState : B3VerificationState

/-- Convert conversion errors to StatementResults -/
def conversionErrorsToResults {M : Type} [Repr M] (errors : List (ConversionError M)) : List StatementResult :=
  errors.map (fun err => StatementResult.conversionError (toString err))

/-- Create VerificationContext from state and statement -/
def mkVerificationContext (state : B3VerificationState) (decl : B3AST.Decl SourceRange) (stmt : B3AST.Statement SourceRange) : VerificationContext :=
  { decl := decl, stmt := stmt, pathCondition := state.pathCondition }

/-- Create a SymbolicExecutionResult with conversion errors and optional verification result -/
def mkExecutionResult {M : Type} [Repr M] (convErrors : List (ConversionError M)) (verificationResult : Option VerificationReport) (state : B3VerificationState) : SymbolicExecutionResult :=
  let errorResults := conversionErrorsToResults convErrors
  let allResults := match verificationResult with
    | some report => errorResults.map (·, none) ++ [(StatementResult.verified report, none)]
    | none => errorResults.map (·, none)
  { results := allResults, finalState := state }

/-- Translate B3 statements to SMT via streaming symbolic execution (without diagnosis) -/
def statementToSMTWithoutDiagnosis (ctx : ConversionContext) (state : B3VerificationState) (sourceDecl : B3AST.Decl SourceRange) : B3AST.Statement SourceRange → IO SymbolicExecutionResult
  | .check m expr => do
      let convResult := expressionToSMT ctx expr
      let vctx := mkVerificationContext state sourceDecl (.check m expr)
      let result ← prove state convResult.term vctx
      pure <| mkExecutionResult convResult.errors (some result) state

  | .assert m expr => do
      let convResult := expressionToSMT ctx expr
      let vctx := mkVerificationContext state sourceDecl (.assert m expr)
      let result ← prove state convResult.term vctx
      -- Always add to path condition (assert assumes its condition regardless of proof result)
      let newState ← addPathCondition state expr convResult.term
      pure <| mkExecutionResult convResult.errors (some result) newState

  | .assume _ expr => do
      let convResult := expressionToSMT ctx expr
      let newState ← addPathCondition state expr convResult.term
      pure <| mkExecutionResult convResult.errors none newState

  | .reach m expr => do
      let convResult := expressionToSMT ctx expr
      let vctx := mkVerificationContext state sourceDecl (.reach m expr)
      let result ← reach state convResult.term vctx
      pure <| mkExecutionResult convResult.errors (some result) state

  | .blockStmt _ stmts => do
      let mut currentState := state
      let mut allResultsRev := []
      for stmt in stmts.val.toList do
        let execResult ← statementToSMTWithoutDiagnosis ctx currentState sourceDecl stmt
        currentState := execResult.finalState
        allResultsRev := execResult.results.reverse ++ allResultsRev
      pure { results := allResultsRev.reverse, finalState := currentState }

  | _ =>
      pure { results := [], finalState := state }
  termination_by stmt => SizeOf.sizeOf stmt
  decreasing_by cases stmts; simp_all; term_by_mem

---------------------------------------------------------------------
-- Statement Formatting
---------------------------------------------------------------------

def formatStatement (prog : Program) (stmt : B3AST.Statement SourceRange) (ctx: B3.ToCSTContext): String :=
  let (cstStmt, _) := B3.stmtToCST ctx stmt
  let fmtCtx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  (mformat (ArgF.op cstStmt.toAst) fmtCtx fmtState).format.pretty.trimAscii.toString

end Strata.B3.Verifier

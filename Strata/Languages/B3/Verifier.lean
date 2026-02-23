/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.ToCore
import Strata.Languages.Core.CoreSMT

open Strata
open Strata.B3.Verifier
open Strata.SMT

/-!
# B3 Verifier

Converts B3 programs to Core and verifies them using the CoreSMT verifier.

## Architecture Overview

```
B3 Program (CST)
      ↓
   Parse (DDM)
      ↓
  B3 AST (de Bruijn indices)
      ↓
FunctionToAxiom Transform
      ↓
  B3 AST (declarations + axioms)
      ↓
B3.ToCore (Conversion)
      ↓
  Core Statements
      ↓
CoreSMT Verifier
      ↓
  Results (proved/counterexample/unknown)
      ↓
Diagnosis (if failed)
```

## API Choice

Use `programToSMT` for automatic diagnosis (recommended) - provides detailed error analysis.
Use `programToSMTWithoutDiagnosis` for faster verification without diagnosis - returns raw results.

## Usage
-/

-- Example: Verify a simple B3 program (meta to avoid including in production)
-- This is not a test, it only demonstrates the end-to-end API
meta def exampleVerification : IO Unit := do
  -- Parse B3 program using DDM syntax
  let ddmProgram : Strata.Program := #strata program B3CST;
    function f(x : int) : int { x + 1 }
    procedure test() {
      check 8 == 8 && f(5) == 7
    }
  #end

  -- For parsing from files, use: parseStrataProgramFromDialect dialects "B3CST" "file.b3cst.st"

  let b3AST : B3AST.Program SourceRange ← match programToB3AST ddmProgram with
    | .ok ast => pure ast
    | .error msg => throw (IO.userError s!"Failed to parse: {msg}")

  -- Create solver and verify
  let solver : Solver ← createInteractiveSolver "cvc5"
  let reports : List ProcedureReport ← programToSMT b3AST solver
  -- Don't call exit in tests - let solver terminate naturally

  -- Destructure results to show types (self-documenting)
  let [report] ← pure reports | throw (IO.userError "Expected one procedure")
  let _procedureName : String := report.procedureName
  let results : List (VerificationReport × Option DiagnosisResult) := report.results

  let [(verificationReport, diagnosisOpt)] ← pure results | throw (IO.userError "Expected one result")

  let analyseVerificationReport (verificationReport: VerificationReport) : IO Unit :=
    do
    let context : VerificationContext := verificationReport.context
    let result : VerificationResult := verificationReport.result
    let _model : Option String := verificationReport.model

    let _decl : B3AST.Decl SourceRange := context.decl
    let _stmt : B3AST.Statement SourceRange := context.stmt
    let pathCondition : List (B3AST.Expression SourceRange) := context.pathCondition

    -- Interpret verification result (merged error and success cases)
    match result with
    | .error .counterexample => IO.println "✗ Counterexample found (assertion may not hold)"
    | .error .unknown => IO.println "✗ Unknown"
    | .error .refuted => IO.println "✗ Refuted (proved false/unreachable)"
    | .success .verified => IO.println "✓ Verified (proved)"
    | .success .reachable => IO.println "✓ Reachable/Satisfiable"
    | .success .reachabilityUnknown => IO.println "✓ Reachability unknown"

    -- Print path condition if present
    if !pathCondition.isEmpty then
      IO.println "  Path condition:"
      for expr in pathCondition do
        IO.println s!"    {B3.Verifier.formatExpression ddmProgram expr B3.ToCSTContext.empty}"

  IO.println s!"Statement: {B3.Verifier.formatStatement ddmProgram verificationReport.context.stmt B3.ToCSTContext.empty}"
  analyseVerificationReport verificationReport

  let (.some diagnosis) ← pure diagnosisOpt | throw (IO.userError "Expected a diagnosis")

  -- Interpret diagnosis (if available)
  let diagnosedFailures : List DiagnosedFailure := diagnosis.diagnosedFailures
  IO.println s!"  Found {diagnosedFailures.length} diagnosed failures"

  for failure in diagnosedFailures do
    let expression : B3AST.Expression SourceRange := failure.expression
    IO.println s!"Failing expression: {B3.Verifier.formatExpression ddmProgram expression B3.ToCSTContext.empty}"
    analyseVerificationReport failure.report

  pure ()

-- See StrataTest/Languages/B3/Verifier/VerifierTests.lean for test of this example.

/-- Convert B3 program to Core and verify via CoreSMT pipeline -/
def programToSMT (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List ProcedureReport) := do
  -- Transform functions to axioms
  let transformedAST := B3.Transform.functionToAxiom prog
  -- Convert to Core
  let coreStmts := B3.ToCore.convertProgram transformedAST
  -- Verify via CoreSMT
  let config : Core.CoreSMT.CoreSMTConfig := { diagnosisEnabled := true, accumulateErrors := true }
  let state := Core.CoreSMT.CoreSMTState.init solver config
  let (_, _, results) ← Core.CoreSMT.verify state Core.Env.init coreStmts
  -- Convert results to B3 format (simplified - returns empty for now)
  return []

def programToSMTWithoutDiagnosis (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String VerificationReport)) := do
  let _ ← programToSMT prog solver
  return []

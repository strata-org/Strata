/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Expression
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Program
import Strata.Languages.B3.Verifier.Diagnosis

open Strata
open Strata.B3.Verifier
open Strata.SMT

/-!
# B3 Verifier

Converts B3 programs to SMT and verifies them using Z3/CVC5.

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
expressionToSMT (Conversion)
      ↓
  SMT Terms
      ↓
formatTermDirect (Formatter)
      ↓
  SMT-LIB strings
      ↓
  Solver (Z3/CVC5)
      ↓
  Results (proved/counterexample/unknown)
      ↓
Diagnosis (if failed)
```

## API Choice

Use `verify` for automatic diagnosis (recommended) - provides detailed error analysis.
Use `verifyWithoutDiagnosis` for faster verification without diagnosis - returns raw results.

## Diagnosis Behavior

**For proof checks (check/assert):**
- Recursively splits conjunctions to find all atomic failures
- Reports multiple failures: "could not prove A", "it is impossible that B"
- Assumes LHS when diagnosing RHS (context-aware)
- Continues diagnosis even after finding provably false conjuncts

**For reachability checks (reach):**
- Stops at first unreachable or provably false conjunct
- Reports single failure: "it is impossible that A"
- All subsequent conjuncts are trivially unreachable if LHS is unreachable
- Always uses "it is impossible that" (reachability is an impossibility proof)

**Provably false detection:**
- "could not prove" - assertion is unprovable (sat/unknown when checking `not A`)
- "it is impossible that" - assertion is provably false (unsat when checking `A`)
- Diagnosis stops when provably false found (root cause identified)

## Usage
-/

-- Example: Verify a simple B3 program (meta to avoid including in production)
meta def exampleVerification : IO Unit := do
  -- Parse B3 program using DDM syntax
  let ddmProgram : Strata.Program := #strata program B3CST;
    function f(x : int) : int { x + 1 }
    procedure test() {
      check f(5) == 6
    }
  #end

  -- For parsing from files, use: parseStrataProgramFromDialect dialects "B3CST" "file.b3cst.st"

  -- Convert Strata.Program to B3AST.Program
  -- (internally: Strata.Program → B3CST.Program → B3AST.Program)
  let b3AST : B3AST.Program SourceRange ← match programToB3AST ddmProgram with
    | .ok ast => pure ast
    | .error msg => throw (IO.userError s!"Failed to parse: {msg}")

  -- Create solver and verify
  let solver : Solver ← createInteractiveSolver "z3"
  let reports : List ProcedureReport ← verify b3AST solver
  let _ ← (Solver.exit).run solver

  -- Destructure results to show types (self-documenting)
  let [report] ← pure reports | throw (IO.userError "Expected one procedure")
  let _procedureName : String := report.procedureName
  let results : List (VerificationReport × Option DiagnosisResult) := report.results

  let [(verificationReport, diagnosisOpt)] ← pure results | throw (IO.userError "Expected one result")
  let context : VerificationContext := verificationReport.context
  let _result : VerificationResult := verificationReport.result
  let _model : Option String := verificationReport.model

  let _decl : B3AST.Decl SourceRange := context.decl
  let _stmt : B3AST.Statement SourceRange := context.stmt
  let _pathCondition : List (B3AST.Expression SourceRange) := context.pathCondition

  match diagnosisOpt with
  | some diagnosis =>
      let diagnosedFailures : List DiagnosedFailure := diagnosis.diagnosedFailures
      let [failure] ← pure diagnosedFailures | pure ()
      let _expression : B3AST.Expression SourceRange := failure.expression
      let _failurePathCondition : List (B3AST.Expression SourceRange) := failure.pathCondition
      let _isProvablyFalse : Bool := failure.isProvablyFalse
      pure ()
  | none => pure ()

  pure ()

  match diagnosisOpt with
  | some diagnosis =>
      let diagnosedFailures : List DiagnosedFailure := diagnosis.diagnosedFailures
      let [failure] ← pure diagnosedFailures | pure ()
      let _expression : B3AST.Expression SourceRange := failure.expression
      let _failurePathCondition : List (B3AST.Expression SourceRange) := failure.pathCondition
      let _isProvablyFalse : Bool := failure.isProvablyFalse
      pure ()
  | none => pure ()

  pure ()

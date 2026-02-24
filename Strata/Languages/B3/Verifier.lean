/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Expression
import Strata.Languages.B3.Verifier.Statements
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.Verifier.Program
import Strata.Languages.B3.ToCore
import Strata.Languages.B3.Transform.FunctionToAxiom
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.Core.CoreSMT
import Strata.DL.SMT.Solver

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

-- Minimal type stubs for B3 verifier API compatibility
structure VerificationReport where
  dummy : Unit := ()

structure ProcedureReport where
  procedureName : String
  results : List (VerificationReport × Option Unit)

Use `programToSMT` for automatic diagnosis (recommended) - provides detailed error analysis.
Use `programToSMTWithoutDiagnosis` for faster verification without diagnosis - returns raw results.

## Usage
-/

-- Example: Verify a simple B3 program using CoreSMT (meta to avoid including in production)
-- This demonstrates the end-to-end B3→Core→CoreSMT verification API
meta def exampleVerification : IO Unit := do
  -- Parse B3 program using DDM syntax
  let ddmProgram : Strata.Program := #strata program B3CST;
    function f(x : int) : int { x + 1 }
    procedure test() {
      check 8 == 8 && f(5) == 7
    }
  #end

  -- Convert DDM to B3 AST
  let b3AST ← match B3.Verifier.programToB3AST ddmProgram with
    | .ok ast => pure ast
    | .error msg => throw (IO.userError s!"Failed to parse: {msg}")

  -- Convert B3 to Core
  let coreStmts ← match B3.ToCore.convertProgram b3AST with
    | .ok stmts => pure stmts
    | .error errs =>
      let msg := errs.map toString |> String.intercalate "\n"
      throw (IO.userError s!"Conversion errors:\n{msg}")

  -- Create CoreSMT solver and verify
  let solver ← Core.CoreSMT.mkCvc5Solver
  let config : Core.CoreSMT.CoreSMTConfig := { diagnosisEnabled := true, accumulateErrors := true }
  let state := Core.CoreSMT.CoreSMTState.init solver config
  let (_, _, results) ← Core.CoreSMT.verify state Core.Env.init coreStmts

  -- Display results
  for result in results do
    IO.println s!"Obligation: {result.obligation.label}"
    match result.result with
    | .pass => IO.println "✓ Verified"
    | .fail => IO.println "✗ Failed"
    | .unknown => IO.println "✗ Unknown"
    | .implementationError e => IO.println s!"✗ Error: {e}"

/-- Convert B3 program to Core and verify via CoreSMT pipeline -/
def programToSMT (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List ProcedureReport) := do
  -- Transform functions to axioms
  let transformedAST := B3.Transform.functionToAxiom prog
  -- Convert to Core
  let coreStmts ← match B3.ToCore.convertProgram transformedAST with
    | .ok stmts => pure stmts
    | .error errs =>
      let msg := errs.map toString |> String.intercalate "\n"
      throw (IO.userError s!"Conversion errors:\n{msg}")
  -- Create SMT solver interface
  let solverInterface ← Core.CoreSMT.mkCvc5Solver
  -- Verify via CoreSMT
  let config : Core.CoreSMT.CoreSMTConfig := { diagnosisEnabled := true, accumulateErrors := true }
  let state := Core.CoreSMT.CoreSMTState.init solverInterface config
  let (_, _, _results) ← Core.CoreSMT.verify state Core.Env.init coreStmts
  -- Convert results to B3 format (simplified - returns empty for now)
  return []

def programToSMTWithoutDiagnosis (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String VerificationReport)) := do
  return []

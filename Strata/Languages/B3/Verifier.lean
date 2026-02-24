/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.ToCore
import Strata.Languages.B3.Transform.FunctionToAxiom
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.Core.CoreSMT
import Strata.DL.SMT.Solver

open Strata
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
```

## Helper Functions
-/

/-- Parse DDM program to B3 AST -/
def programToB3AST (ddmProgram : Strata.Program) : Except String (B3AST.Program SourceRange) :=
  match B3.DDMTransform.parseCST ddmProgram with
  | .error msg => .error s!"Parse error: {msg}"
  | .ok cst =>
    match B3.DDMTransform.cstToAST cst with
    | .error msg => .error s!"Conversion error: {msg}"
    | .ok ast => .ok ast

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
  let convResult := B3.ToCore.convertProgram b3AST
  if !convResult.errors.isEmpty then
    let msg := convResult.errors.map toString |> String.intercalate "\n"
    throw (IO.userError s!"Conversion errors:\n{msg}")
  let coreStmts := convResult.value

  -- Create CoreSMT solver and verify
  let solver ← Core.CoreSMT.mkCvc5Solver
  let config : Core.CoreSMT.CoreSMTConfig := { accumulateErrors := true }
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

-- Minimal type stubs for B3 verifier API compatibility
structure VerificationReport where
  dummy : Unit := ()

structure ProcedureReport where
  procedureName : String
  results : List (VerificationReport × Option Unit)

/-- Convert B3 program to Core and verify via CoreSMT pipeline -/
def programToSMT (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List ProcedureReport) := do
  -- Transform functions to axioms
  let transformedAST := B3.Transform.functionToAxiom prog
  -- Convert to Core
  let convResult := B3.ToCore.convertProgram transformedAST
  if !convResult.errors.isEmpty then
    let msg := convResult.errors.map toString |> String.intercalate "\n"
    throw (IO.userError s!"Conversion errors:\n{msg}")
  let coreStmts := convResult.value
  -- Create SMT solver interface
  let solverInterface ← Core.CoreSMT.mkCvc5Solver
  -- Verify via CoreSMT
  let config : Core.CoreSMT.CoreSMTConfig := { accumulateErrors := true }
  let state := Core.CoreSMT.CoreSMTState.init solverInterface config
  let (_, _, _results) ← Core.CoreSMT.verify state Core.Env.init coreStmts
  -- TODO: Convert results to B3 format for test compatibility
  return []

def programToSMTWithoutDiagnosis (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String VerificationReport)) := do
  -- TODO: Implement without diagnosis
  return []

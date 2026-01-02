/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.DL.SMT.Solver

/-!
# B3 Verification State

Manages incremental verification state for interactive debugging.
-/

namespace Strata.B3.Verifier

open Strata.SMT

---------------------------------------------------------------------
-- Verification State
---------------------------------------------------------------------

structure B3VerificationState where
  solver : Solver  -- Single solver instance reused for all checks
  declaredFunctions : List (String × List String × String)
  assertions : List Term
  context : ConversionContext

structure CheckResult where
  decl : B3AST.Decl SourceRange
  sourceStmt : Option (B3AST.Statement SourceRange) := none
  decision : Decision
  model : Option String := none

def initVerificationState (solverPath : String := "z3") : IO B3VerificationState := do
  let solver ← Solver.spawn solverPath #["-smt2", "-in"]
  let _ ← (Solver.setLogic "ALL").run solver
  let _ ← (Solver.setOption "produce-models" "true").run solver
  return {
    solver := solver
    declaredFunctions := []
    assertions := []
    context := ConversionContext.empty
  }

def addFunctionDecl (state : B3VerificationState) (name : String) (argTypes : List String) (returnType : String) : IO B3VerificationState := do
  let _ ← (Solver.declareFun name argTypes returnType).run state.solver
  return { state with declaredFunctions := (name, argTypes, returnType) :: state.declaredFunctions }

def addAssertion (state : B3VerificationState) (term : Term) : IO B3VerificationState := do
  let _ ← (Solver.assert (formatTermDirect term)).run state.solver
  return { state with assertions := term :: state.assertions }

def checkProperty (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO CheckResult := do
  -- Use push/pop for isolated check - reuses existing solver state!
  let runCheck : SolverM (Decision × Option String) := do
    -- Push new scope
    let solver ← read
    solver.smtLibInput.putStr "(push 1)\n"
    solver.smtLibInput.flush

    -- Assert negation
    Solver.assert s!"(not {formatTermDirect term})"

    -- Check sat
    let decision ← Solver.checkSat []

    -- Pop scope (restore state)
    solver.smtLibInput.putStr "(pop 1)\n"
    solver.smtLibInput.flush

    let model := if decision == .sat then some "model available" else none
    return (decision, model)

  let (decision, model) ← runCheck.run state.solver
  return {
    decl := sourceDecl
    sourceStmt := sourceStmt
    decision := decision
    model := model
  }

def closeVerificationState (state : B3VerificationState) : IO Unit := do
  let _ ← (Solver.exit).run state.solver
  pure ()

end Strata.B3.Verifier

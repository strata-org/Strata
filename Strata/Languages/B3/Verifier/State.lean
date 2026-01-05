/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.DL.SMT.Solver

/-!
# B3 Verification State

Manages incremental verification state for interactive debugging.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.SMT
open Strata.B3AST
open Strata.B3.Verifier (UF_ARG_PLACEHOLDER)

---------------------------------------------------------------------
-- B3 Verification Results
---------------------------------------------------------------------

inductive B3CheckResult where
  | proved : B3CheckResult
  | counterexample : B3CheckResult
  | proofUnknown : B3CheckResult

def B3CheckResult.isError : B3CheckResult → Bool
  | .proved => false
  | .counterexample => true
  | .proofUnknown => true

inductive B3ReachResult where
  | unreachable : B3ReachResult
  | reachable : B3ReachResult
  | reachabilityUnknown : B3ReachResult

def B3ReachResult.isError : B3ReachResult → Bool
  | .unreachable => true
  | .reachable => false
  | .reachabilityUnknown => false

inductive B3Result where
  | checkResult : B3CheckResult → B3Result
  | reachResult : B3ReachResult → B3Result

def B3Result.isError : B3Result → Bool
  | .checkResult r => r.isError
  | .reachResult r => r.isError

def B3Result.fromDecisionForProve (d : Decision) : B3Result :=
  match d with
  | .unsat => .checkResult .proved
  | .sat => .checkResult .counterexample
  | .unknown => .checkResult .proofUnknown

def B3Result.fromDecisionForReach (d : Decision) : B3Result :=
  match d with
  | .unsat => .reachResult .unreachable
  | .sat => .reachResult .reachable
  | .unknown => .reachResult .reachabilityUnknown

---------------------------------------------------------------------
-- Verification State
---------------------------------------------------------------------

---------------------------------------------------------------------
-- SMT Solver State (reusable for any language)
---------------------------------------------------------------------

structure SMTSolverState where
  solver : Solver
  declaredFunctions : List (String × List String × String)
  assertions : List Term

structure B3VerificationState where
  smtState : SMTSolverState
  context : ConversionContext  -- B3-specific: maps de Bruijn indices to names

structure CheckResult where
  decl : B3AST.Decl SourceRange
  sourceStmt : Option (B3AST.Statement SourceRange) := none
  result : B3Result  -- B3-level result
  model : Option String := none

def initVerificationState (solver : Solver) : IO B3VerificationState := do
  let _ ← (Solver.setLogic "ALL").run solver
  let _ ← (Solver.setOption "produce-models" "true").run solver
  return {
    smtState := {
      solver := solver
      declaredFunctions := []
      assertions := []
    }
    context := ConversionContext.empty
  }

def addFunctionDecl (state : B3VerificationState) (name : String) (argTypes : List String) (returnType : String) : IO B3VerificationState := do
  let _ ← (Solver.declareFun name argTypes returnType).run state.smtState.solver
  return { state with smtState := { state.smtState with declaredFunctions := (name, argTypes, returnType) :: state.smtState.declaredFunctions } }

def addAxiom (state : B3VerificationState) (term : Term) : IO B3VerificationState := do
  let _ ← (Solver.assert (formatTermDirect term)).run state.smtState.solver
  return { state with smtState := { state.smtState with assertions := term :: state.smtState.assertions } }

def push (state : B3VerificationState) : IO B3VerificationState := do
  let solver := state.smtState.solver
  solver.smtLibInput.putStr "(push 1)\n"
  solver.smtLibInput.flush
  return state

def pop (state : B3VerificationState) : IO B3VerificationState := do
  let solver := state.smtState.solver
  solver.smtLibInput.putStr "(pop 1)\n"
  solver.smtLibInput.flush
  return state

/-- Prove a property holds (check/assert statement) -/
def prove (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO CheckResult := do
  let _ ← push state
  let runCheck : SolverM (Decision × Option String) := do
    Solver.assert s!"(not {formatTermDirect term})"
    let decision ← Solver.checkSat []
    let model := if decision == .sat then some "model available" else none
    return (decision, model)
  let (decision, model) ← runCheck.run state.smtState.solver
  let _ ← pop state
  return {
    decl := sourceDecl
    sourceStmt := sourceStmt
    result := B3Result.fromDecisionForProve decision
    model := model
  }

/-- Check if a property is reachable (reach statement) -/
def reach (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO CheckResult := do
  let _ ← push state
  let runCheck : SolverM (Decision × Option String) := do
    Solver.assert (formatTermDirect term)
    let decision ← Solver.checkSat []
    let model := if decision == .sat then some "reachable" else none
    return (decision, model)
  let (decision, model) ← runCheck.run state.smtState.solver
  let _ ← pop state
  return {
    decl := sourceDecl
    sourceStmt := sourceStmt
    result := B3Result.fromDecisionForReach decision
    model := model
  }

def closeVerificationState (state : B3VerificationState) : IO Unit := do
  let _ ← (Solver.exit).run state.smtState.solver
  pure ()

end Strata.B3.Verifier

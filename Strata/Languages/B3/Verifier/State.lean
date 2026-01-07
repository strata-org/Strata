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

/-- Result of a proof check (check/assert statement).
Represents the SMT solver's decision. -/
inductive ProofResult where
  | proved : ProofResult
  | counterexample : ProofResult
  | proofUnknown : ProofResult

def ProofResult.isError : ProofResult → Bool
  | .proved => false
  | .counterexample => true
  | .proofUnknown => true

/-- Result of a reachability check (reach statement).
Represents the SMT solver's decision. -/
inductive ReachabilityResult where
  | unreachable : ReachabilityResult
  | reachable : ReachabilityResult
  | reachabilityUnknown : ReachabilityResult

def ReachabilityResult.isError : ReachabilityResult → Bool
  | .unreachable => true
  | .reachable => false
  | .reachabilityUnknown => false

/-- Unified verification result (proof or reachability).
Allows uniform handling of both verification types. -/
inductive VerificationResult where
  | proofResult : ProofResult → VerificationResult
  | reachabilityResult : ReachabilityResult → VerificationResult

def VerificationResult.isError : VerificationResult → Bool
  | .proofResult r => r.isError
  | .reachabilityResult r => r.isError

def VerificationResult.fromDecisionForProve (d : Decision) : VerificationResult :=
  match d with
  | .unsat => .proofResult .proved
  | .sat => .proofResult .counterexample
  | .unknown => .proofResult .proofUnknown

def VerificationResult.fromDecisionForReach (d : Decision) : VerificationResult :=
  match d with
  | .unsat => .reachabilityResult .unreachable
  | .sat => .reachabilityResult .reachable
  | .unknown => .reachabilityResult .reachabilityUnknown

---------------------------------------------------------------------
-- Verification State
---------------------------------------------------------------------

/-- VerificationReport combines VerificationResult with source location.
Top-level result type returned to users, containing:
- The verification result (proved/counterexample/reachable/etc.)
- Source location (declaration and optional statement)
- Optional model/counterexample information
- Path condition (accumulated assertions) for debugging failures -/
structure VerificationReport where
  decl : B3AST.Decl SourceRange
  sourceStmt : Option (B3AST.Statement SourceRange) := none
  result : VerificationResult
  model : Option String := none
  pathCondition : List (B3AST.Expression SourceRange) := []  -- For debugging failures

---------------------------------------------------------------------
-- SMT Solver State
---------------------------------------------------------------------

/-- SMT solver state (reusable for any language) -/
structure SMTSolverState where
  solver : Solver
  declaredFunctions : List (String × List String × String)
  assertions : List Term

/-- B3-specific verification state -/
structure B3VerificationState where
  smtState : SMTSolverState
  context : ConversionContext
  pathCondition : List (B3AST.Expression SourceRange)  -- Accumulated assertions for debugging

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
    pathCondition := []
  }

def addFunctionDecl (state : B3VerificationState) (name : String) (argTypes : List String) (returnType : String) : IO B3VerificationState := do
  let _ ← (Solver.declareFun name argTypes returnType).run state.smtState.solver
  return { state with smtState := { state.smtState with declaredFunctions := (name, argTypes, returnType) :: state.smtState.declaredFunctions } }

def addPathCondition (state : B3VerificationState) (expr : B3AST.Expression SourceRange) (term : Term) : IO B3VerificationState := do
  let _ ← (Solver.assert (formatTermDirect term)).run state.smtState.solver
  return {
    state with
    smtState := { state.smtState with assertions := term :: state.smtState.assertions }
    pathCondition := expr :: state.pathCondition
  }

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
def prove (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO VerificationReport := do
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
    result := VerificationResult.fromDecisionForProve decision
    model := model
    pathCondition := state.pathCondition
  }

/-- Check if a property is reachable (reach statement) -/
def reach (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO VerificationReport := do
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
    result := VerificationResult.fromDecisionForReach decision
    model := model
    pathCondition := state.pathCondition
  }

def closeVerificationState (state : B3VerificationState) : IO Unit := do
  let _ ← (Solver.exit).run state.smtState.solver
  pure ()

---------------------------------------------------------------------
-- Solver Creation Helpers
---------------------------------------------------------------------

/-- Create an interactive solver (Z3/CVC5) -/
def createInteractiveSolver (solverPath : String := "z3") : IO Solver :=
  Solver.spawn solverPath #["-smt2", "-in"]

/-- Create a buffer solver for SMT command generation -/
def createBufferSolver : IO (Solver × IO.Ref IO.FS.Stream.Buffer) := do
  let buffer ← IO.mkRef {}
  let solver ← Solver.bufferWriter buffer
  return (solver, buffer)

end Strata.B3.Verifier

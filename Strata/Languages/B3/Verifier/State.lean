/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Expression
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

/-- Verification outcome when check fails -/
inductive VerificationError where
  | counterexample : VerificationError  -- Possibly wrong (sat)
  | unknown : VerificationError  -- Couldn't determine
  | refuted : VerificationError  -- Proved false/unreachable (unsat)

/-- Verification outcome when check succeeds -/
inductive VerificationSuccess where
  | verified : VerificationSuccess  -- Proved
  | reachable : VerificationSuccess  -- Reachability confirmed
  | reachabilityUnknown : VerificationSuccess  -- Couldn't determine, but not an error

/-- Unified verification result -/
inductive VerificationResult where
  | error : VerificationError → VerificationResult
  | success : VerificationSuccess → VerificationResult

def VerificationResult.isError : VerificationResult → Bool
  | .error _ => true
  | .success _ => false

def VerificationResult.fromDecisionForProve (d : Decision) : VerificationResult :=
  match d with
  | .unsat => .success .verified
  | .sat => .error .counterexample
  | .unknown => .error .unknown

def VerificationResult.fromDecisionForReach (d : Decision) : VerificationResult :=
  match d with
  | .unsat => .error .refuted
  | .sat => .success .reachable
  | .unknown => .success .reachabilityUnknown

---------------------------------------------------------------------
-- Verification Context and Results
---------------------------------------------------------------------

/-- Context for a verification check (where in the program and what we know) -/
structure VerificationContext where
  decl : B3AST.Decl SourceRange
  stmt : B3AST.Statement SourceRange
  pathCondition : List (B3AST.Expression SourceRange)  -- Accumulated assertions

/-- VerificationReport combines VerificationResult with source context.
Top-level result type returned to users, containing:
- The verification result (proved/counterexample/reachable/etc.)
- Source context (declaration, statement, and path condition)
- Optional model/counterexample information (TODO: use structured Model type instead of String)
-/
structure VerificationReport where
  context : VerificationContext
  result : VerificationResult
  model : Option String := none  -- TODO: Replace with structured Model type (Map String Term)

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
def prove (state : B3VerificationState) (term : Term) (ctx : VerificationContext) : IO VerificationReport := do
  let _ ← push state
  let runCheck : SolverM (Decision × Option String) := do
    Solver.assert s!"(not {formatTermDirect term})"
    let decision ← Solver.checkSat []
    let model := if decision == .sat then some "model available" else none
    return (decision, model)
  let (decision, model) ← runCheck.run state.smtState.solver
  let _ ← pop state
  return {
    context := ctx
    result := VerificationResult.fromDecisionForProve decision
    model := model
  }

/-- Check if a property is reachable (reach statement) -/
def reach (state : B3VerificationState) (term : Term) (ctx : VerificationContext) : IO VerificationReport := do
  let _ ← push state
  let runCheck : SolverM (Decision × Option String) := do
    Solver.assert (formatTermDirect term)
    let decision ← Solver.checkSat []
    let model := if decision == .sat then some "reachable" else none
    return (decision, model)
  let (decision, model) ← runCheck.run state.smtState.solver
  let _ ← pop state
  return {
    context := ctx
    result := VerificationResult.fromDecisionForReach decision
    model := model
  }

def closeVerificationState (state : B3VerificationState) : IO Unit := do
  let _ ← (Solver.exit).run state.smtState.solver
  pure ()

---------------------------------------------------------------------
-- Solver Creation Helpers
---------------------------------------------------------------------

/-- Create an interactive solver (Z3/CVC5) -/
def createInteractiveSolver (solverPath : String := "z3") : IO Solver :=
  let args := if solverPath.endsWith "cvc5" || solverPath == "cvc5"
    then #["--lang", "smt2", "--incremental"]
    else #["-smt2", "-in"]  -- Z3 flags
  Solver.spawn solverPath args

/-- Create a buffer solver for SMT command generation -/
def createBufferSolver : IO (Solver × IO.Ref IO.FS.Stream.Buffer) := do
  let buffer ← IO.mkRef {}
  let solver ← Solver.bufferWriter buffer
  return (solver, buffer)

---------------------------------------------------------------------
-- Verification Results
---------------------------------------------------------------------

structure DiagnosedFailure where
  expression : B3AST.Expression SourceRange
  report : VerificationReport  -- Contains context (with pathCondition), result (refuted if provably false), model

structure DiagnosisResult where
  originalCheck : VerificationReport
  diagnosedFailures : List DiagnosedFailure

end Strata.B3.Verifier

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Solver
import Strata.DL.SMT.Term
import Strata.DL.SMT.TermType
import Strata.DL.SMT.DDMTransform.Translate
import Strata.Languages.Core.Options

/-!
# SMT Solver Interface

Abstract interface for SMT solvers using `Strata.SMT.Term` and `Strata.SMT.TermType`.
Converts to SMT-LIB strings via `SMTDDM.toString` when communicating with solvers.

The interface is a structure (not a type class) to allow runtime selection of
different solver backends.
-/

namespace Strata.SMT

open Strata.SMT

/-- Abstract interface for SMT solvers.
    Uses Strata.SMT.Term which can be converted to SMT-LIB strings via SMTDDM.toString -/
structure SolverInterface where
  /-- Push a new scope onto the solver stack -/
  push : IO Unit
  /-- Pop the top scope from the solver stack -/
  pop : IO Unit
  /-- Declare an uninterpreted sort -/
  declareSort : String → Nat → IO Unit
  /-- Declare an uninterpreted function -/
  declareFun : String → List TermType → TermType → IO Unit
  /-- Define a function with a body -/
  defineFun : String → List (String × TermType) → TermType → Term → IO Unit
  /-- Assert a term -/
  assert : Term → IO Unit
  /-- Check satisfiability -/
  checkSat : IO Decision
  /-- Check satisfiability with assumptions (check-sat-assuming) -/
  checkSatAssuming : List Term → IO Decision
  /-- Get model values for variables -/
  getModel : List String → IO (List (String × String))
  /-- Reset the solver state -/
  reset : IO Unit

/-- Helper to convert Term to SMT-LIB string using SMTDDM.toString -/
private def termToString (t : Term) : Except String String :=
  SMTDDM.toString t

/-- Helper to create an SMTSolverInterface from an initialized Solver -/
def mkSolverInterfaceFromSolver (solver : Solver) : IO SolverInterface := do
  let solverRef ← IO.mkRef solver
  return {
    push := do
      let s ← solverRef.get
      s.smtLibInput.putStr "(push 1)\n"
      s.smtLibInput.flush
    pop := do
      let s ← solverRef.get
      s.smtLibInput.putStr "(pop 1)\n"
      s.smtLibInput.flush
    declareSort := fun name arity => do
      (Solver.declareSort name arity).run (← solverRef.get)
    declareFun := fun name argTypes retType => do
      let argStrs := argTypes.map TermType.toSMTString
      let retStr := TermType.toSMTString retType
      (Solver.declareFun name argStrs retStr).run (← solverRef.get)
    defineFun := fun name args retType body => do
      let argStrs := args.map fun (n, ty) => (n, TermType.toSMTString ty)
      let retStr := TermType.toSMTString retType
      match termToString body with
      | .ok bodyStr => (Solver.defineFun name argStrs retStr bodyStr).run (← solverRef.get)
      | .error e => throw (IO.userError s!"Failed to convert term to string: {e}")
    assert := fun term => do
      match termToString term with
      | .ok termStr => (Solver.assert termStr).run (← solverRef.get)
      | .error e => throw (IO.userError s!"Failed to convert term to string: {e}")
    checkSat := do
      (Solver.checkSat []).run (← solverRef.get)
    checkSatAssuming := fun assumptions => do
      let s ← solverRef.get
      let assumptionStrs ← assumptions.mapM fun a =>
        match termToString a with
        | .ok str => pure str
        | .error e => throw (IO.userError s!"Failed to convert term to string: {e}")
      let assumptionsStr := String.intercalate " " assumptionStrs
      s.smtLibInput.putStr s!"(check-sat-assuming ({assumptionsStr}))\n"
      s.smtLibInput.flush
      match s.smtLibOutput with
      | .some stdout =>
        let result := (← stdout.getLine).trimAscii.toString
        match result with
        | "sat"     => return .sat
        | "unsat"   => return .unsat
        | "unknown" => return .unknown
        | other     => throw (IO.userError s!"Unrecognized solver output: {other}")
      | .none => return .unsat  -- Buffer solver: assume proved (no diagnosis)
    getModel := fun vars => do
      let s ← solverRef.get
      let varsStr := String.intercalate " " vars
      s.smtLibInput.putStr s!"(get-value ({varsStr}))\n"
      s.smtLibInput.flush
      match s.smtLibOutput with
      | .some stdout =>
        let response ← stdout.getLine
        return vars.map fun v => (v, response)
      | .none => return []
    reset := do
      (Solver.reset).run (← solverRef.get)
      (Solver.setLogic "ALL").run (← solverRef.get)
  : SolverInterface }

/-- Initialize a solver with standard settings -/
private def initializeSolver (solver : Solver) : IO Unit := do
  (Solver.setLogic "ALL").run solver

/-- Create an SMTSolverInterface backed by cvc5 (default solver). -/
def mkCvc5Solver : IO SolverInterface := do
  let solver ← Solver.spawn Core.defaultSolver #["--quiet", "--lang", "smt", "--incremental", "--produce-models"]
  initializeSolver solver
  mkSolverInterfaceFromSolver solver

/-- Create a SolverInterface from a specific solver path -/
def mkSolverFromPath (path : String) : IO SolverInterface := do
  let solver ← Solver.spawn path #["--quiet", "--lang", "smt", "--incremental", "--produce-models"]
  initializeSolver solver
  mkSolverInterfaceFromSolver solver

/-- Create a SolverInterface from the SOLVER environment variable -/
def mkSolverFromEnv : IO SolverInterface := do
  match (← IO.getEnv "SOLVER") with
  | .some path => mkSolverFromPath path
  | .none => throw (IO.userError "SOLVER environment variable not defined.")

end Strata.SMT

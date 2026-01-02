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

def addAxiom (state : B3VerificationState) (term : Term) : IO B3VerificationState := do
  let _ ← (Solver.assert (formatTermDirect term)).run state.solver
  return { state with assertions := term :: state.assertions }

def push (state : B3VerificationState) : IO B3VerificationState := do
  let solver := state.solver
  solver.smtLibInput.putStr "(push 1)\n"
  solver.smtLibInput.flush
  return state

def pop (state : B3VerificationState) : IO B3VerificationState := do
  let solver := state.solver
  solver.smtLibInput.putStr "(pop 1)\n"
  solver.smtLibInput.flush
  return state

def checkProperty (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO CheckResult := do
  -- Just assert negation and check (caller manages push/pop)
  let runCheck : SolverM (Decision × Option String) := do
    Solver.assert s!"(not {formatTermDirect term})"
    let decision ← Solver.checkSat []
    let model := if decision == .sat then some "model available" else none
    return (decision, model)

  let (decision, model) ← runCheck.run state.solver
  return {
    decl := sourceDecl
    sourceStmt := sourceStmt
    decision := decision
    model := model
  }

def prove (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO CheckResult := do
  let _ ← push state
  let result ← checkProperty state term sourceDecl sourceStmt
  let _ ← pop state
  return result

def closeVerificationState (state : B3VerificationState) : IO Unit := do
  let _ ← (Solver.exit).run state.solver
  pure ()

/-- Check if a property is reachable (reach statement) -/
def reach (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) : IO CheckResult := do
  let _ ← push state
  let runCheck : SolverM (Decision × Option String) := do
    -- Assert the property itself (not negation)
    -- sat = reachable, unsat = provably unreachable
    Solver.assert (formatTermDirect term)
    let decision ← Solver.checkSat []
    let model := if decision == .sat then some "reachable" else none
    return (decision, model)
  let (decision, model) ← runCheck.run state.solver
  let _ ← pop state
  return {
    decl := sourceDecl
    sourceStmt := sourceStmt
    decision := decision
    model := model
  }

end Strata.B3.Verifier


---------------------------------------------------------------------
-- Higher-level API (works with B3AST types)
---------------------------------------------------------------------

/-- Add a B3 function declaration to the verification state -/
def addFunction (state : B3VerificationState) (decl : B3AST.Decl SourceRange) : IO B3VerificationState := do
  match decl with
  | .function _ name params _ _ _ =>
      let argTypes := params.val.toList.map (fun _ => "Int")  -- TODO: proper type conversion
      addFunctionDecl state name.val argTypes "Int"
  | _ => return state

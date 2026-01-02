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

---------------------------------------------------------------------
-- B3 Verification Results
---------------------------------------------------------------------

inductive B3CheckResult where
  | proved : B3CheckResult
  | provedWrong : B3CheckResult
  | proofUnknown : B3CheckResult  -- Solver timeout/incomplete

inductive B3ReachResult where
  | unreachable : B3ReachResult
  | reachable : B3ReachResult
  | reachabilityUnknown : B3ReachResult  -- Conservative: might be reachable

inductive B3Result where
  | checkResult : B3CheckResult → B3Result
  | reachResult : B3ReachResult → B3Result

def B3Result.fromDecisionForProve (d : Decision) : B3Result :=
  match d with
  | .unsat => .checkResult .proved
  | .sat => .checkResult .provedWrong
  | .unknown => .checkResult .proofUnknown

def B3Result.fromDecisionForReach (d : Decision) : B3Result :=
  match d with
  | .unsat => .reachResult .unreachable
  | .sat => .reachResult .reachable
  | .unknown => .reachResult .reachabilityUnknown

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
  result : B3Result  -- B3-level result
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


/-- Add a B3 declaration (function or axiom) to the verification state -/
def addDeclaration (state : B3VerificationState) (decl : B3AST.Decl SourceRange) : IO B3VerificationState := do
  match decl with
  | .function _ name params _ _ body =>
      -- Declare function signature
      let argTypes := params.val.toList.map (fun _ => "Int")
      let mut state' ← addFunctionDecl state name.val argTypes "Int"

      -- Add function definition as axiom if body exists
      match body.val with
      | some (.functionBody _ whens bodyExpr) =>
          let paramNames := params.val.toList.map (fun p => match p with | .fParameter _ _ n _ => n.val)
          let ctx' := paramNames.foldl (fun acc n => acc.push n) ConversionContext.empty
          match expressionToSMT ctx' bodyExpr with
          | some bodyTerm =>
              let paramVars := paramNames.map (fun n => Term.var ⟨n, .int⟩)
              let uf : UF := { id := name.val, args := paramVars.map (fun t => ⟨"_", t.typeOf⟩), out := .int }
              let funcCall := Term.app (.uf uf) paramVars .int
              let equality := Term.app .eq [funcCall, bodyTerm] .bool
              let axiomBody := if whens.val.isEmpty then
                equality
              else
                let whenTerms := whens.val.toList.filterMap (fun w =>
                  match w with | .when _ e => expressionToSMT ctx' e
                )
                let antecedent := whenTerms.foldl (fun acc t => Term.app .and [acc, t] .bool) (Term.bool true)
                Term.app .or [Term.app .not [antecedent] .bool, equality] .bool
              let trigger := Term.app .triggers [funcCall] .trigger
              let axiomTerm := if paramNames.isEmpty then
                axiomBody
              else
                paramNames.foldl (fun body pname =>
                  Factory.quant .all pname .int trigger body
                ) axiomBody
              addAxiom state' axiomTerm
          | none => return state'
      | none => return state'
  | .axiom _ _ expr =>
      match expressionToSMT ConversionContext.empty expr with
      | some term => addAxiom state term
      | none => return state
  | _ => return state

end Strata.B3.Verifier

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.Statements

/-!
# B3 Verifier

Main entry point for B3 program verification.
Provides both batch and incremental verification APIs.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.SMT
open Strata.B3AST

---------------------------------------------------------------------
-- Batch Verification API
---------------------------------------------------------------------

/-- Verify a B3 program with a given solver -/
def verifyProgramWithSolver (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String CheckResult)) := do
  let mut state ← initVerificationState solver
  let mut results := []

  match prog with
  | .program _ decls =>
      -- First pass: declare all functions
      for decl in decls.val.toList do
        match decl with
        | .function _ name params _ _ _ =>
            let argTypes := params.val.toList.map (fun _ => "Int")
            state ← addFunctionDecl state name.val argTypes "Int"
        | _ => pure ()

      -- Second pass: add axioms and check properties
      for decl in decls.val.toList do
        match decl with
        | .function _ name params _ _ body =>
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
                    state ← addAxiom state axiomTerm
                | none => pure ()
            | none => pure ()
        | .axiom _ _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term => state ← addAxiom state term
            | none => pure ()
        | .procedure m name params specs body =>
            -- Only verify parameter-free procedures
            if params.val.isEmpty && body.val.isSome then
              let bodyStmt := body.val.get!
              let execResult ← executeStatements ConversionContext.empty state decl bodyStmt
              -- Convert StatementResult to Except String CheckResult
              let converted := execResult.results.map (fun r =>
                match r with
                | .verified checkResult => .ok checkResult
                | .conversionError msg => .error msg
              )
              results := results ++ converted
            else
              pure ()  -- Skip procedures with parameters for now
        | _ => pure ()

      closeVerificationState state
      return results

---------------------------------------------------------------------
-- SMT Command Generation (for debugging/inspection)
---------------------------------------------------------------------

---------------------------------------------------------------------
-- State Building Utilities
---------------------------------------------------------------------

/-- Build verification state from B3 program (functions and axioms only, no procedures) -/
def buildProgramState (prog : Strata.B3AST.Program SourceRange) (solver : Solver) : IO B3VerificationState := do
  let mut state ← initVerificationState solver
  match prog with
  | .program _ decls =>
      for decl in decls.val.toList do
        match decl with
        | .function _ name params _ _ _ =>
            let argTypes := params.val.toList.map (fun _ => "Int")
            state ← addFunctionDecl state name.val argTypes "Int"
        | _ => pure ()

      for decl in decls.val.toList do
        match decl with
        | .function _ name params _ _ body =>
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
                    state ← addAxiom state axiomTerm
                | none => pure ()
            | none => pure ()
        | .axiom _ _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term => state ← addAxiom state term
            | none => pure ()
        | _ => pure ()

      return state

/-- Verify a B3 program (convenience wrapper with interactive solver) -/
def verifyProgram (prog : Strata.B3AST.Program SourceRange) (solverPath : String := "z3") : IO (List (Except String CheckResult)) := do
  let solver ← createInteractiveSolver solverPath
  let results ← verifyProgramWithSolver prog solver
  let _ ← (Solver.exit).run solver
  return results

/-- Generate SMT commands for a B3 program -/
def programToSMTCommands (prog : Strata.B3AST.Program SourceRange) : IO String := do
  let (solver, buffer) ← createBufferSolver
  let _ ← (Solver.setLogic "ALL").run solver
  let _ ← verifyProgramWithSolver prog solver
  let contents ← buffer.get
  if h: contents.data.IsValidUTF8
  then return String.fromUTF8 contents.data h
  else return "Error: Invalid UTF-8 in SMT output"

end Strata.B3.Verifier

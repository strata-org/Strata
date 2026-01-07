/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.Statements
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.Transform.FunctionToAxiom

/-!
# B3 Batch Verifier

Batch verification API for B3 programs.
Verifies entire programs in one pass.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.SMT
open Strata.B3AST

---------------------------------------------------------------------
-- Batch Verification API
---------------------------------------------------------------------

/-- Add declarations and axioms from a transformed B3 program to the verification state -/
private def addDeclarationsAndAxioms (state : B3VerificationState) (prog : B3AST.Program SourceRange) : IO (B3VerificationState × List String) := do
  let mut state := state
  let mut errors := []

  match prog with
  | .program _ decls =>
      -- First pass: declare all functions
      for decl in decls.val.toList do
        match decl with
        | .function _ name params resultType _ body =>
            -- After transformation, functions should have no body
            if body.val.isNone then
              let argTypes := params.val.toList.map (fun p =>
                match p with
                | .fParameter _ _ _ ty => b3TypeToSMT ty.val
              )
              let retType := b3TypeToSMT resultType.val
              state ← addFunctionDecl state name.val argTypes retType
        | _ => pure ()

      -- Second pass: add axioms
      for decl in decls.val.toList do
        match decl with
        | .axiom _ _ expr =>
            let convResult := expressionToSMT ConversionContext.empty expr
            state ← addPathCondition state expr convResult.term
            errors := errors ++ convResult.errors.map toString
        | _ => pure ()

  return (state, errors)

/-- Verify a B3 program with a given solver -/
def verifyProgramWithSolver (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String VerificationReport)) := do
  let mut state ← initVerificationState solver
  let mut results := []

  -- Transform: split functions into declarations + axioms
  let transformedProg := Transform.functionToAxiom prog

  -- Add function declarations and axioms
  let (newState, conversionErrors) ← addDeclarationsAndAxioms state transformedProg
  state := newState

  -- Report conversion errors
  for err in conversionErrors do
    results := results ++ [.error err]

  match prog with
  | .program _ decls =>
      -- Check procedures
      for decl in decls.val.toList do
        match decl with
        | .procedure _m _name params _specs body =>
            -- Only verify parameter-free procedures
            if params.val.isEmpty && body.val.isSome then
              let bodyStmt := body.val.get!
              let execResult ← symbolicExecuteStatements ConversionContext.empty state decl bodyStmt
              -- Convert StatementResult to Except String VerificationReport
              let converted := execResult.results.map (fun r =>
                match r with
                | .verified report => .ok report
                | .conversionError msg => .error msg
              )
              results := results ++ converted
            else
              pure ()  -- Skip procedures with parameters for now
        | _ => pure ()

  closeVerificationState state
  return results

---------------------------------------------------------------------
-- Convenience Wrappers
---------------------------------------------------------------------

/-- Build verification state from B3 program (functions and axioms only, no procedures) -/
def buildProgramState (prog : Strata.B3AST.Program SourceRange) (solver : Solver) : IO B3VerificationState := do
  let state ← initVerificationState solver
  let transformedProg := Transform.functionToAxiom prog
  let (newState, errors) ← addDeclarationsAndAxioms state transformedProg
  -- Log errors if any
  for err in errors do
    IO.eprintln s!"Warning: {err}"
  return newState

/-- Verify a B3 program (convenience wrapper with interactive solver) -/
def verifyProgram (prog : Strata.B3AST.Program SourceRange) (solverPath : String := "z3") : IO (List (Except String VerificationReport)) := do
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

---------------------------------------------------------------------
-- Batch Verification with Automatic Diagnosis
---------------------------------------------------------------------

structure ProcedureReport where
  procedureName : String
  results : List (VerificationReport × Option DiagnosisResult)

/-- Verify a B3 program with automatic diagnosis.

Main entry point for verification with automatic debugging.

Workflow:
1. Build program state (functions, axioms)
2. For each parameter-free procedure:
   - Generate VCs from body
   - Check each VC
   - If failed, automatically diagnose to find root cause
3. Report all results with diagnosements
-/
def verifyWithDiagnosis (prog : Strata.B3AST.Program SourceRange) (solverPath : String := "z3") : IO (List ProcedureReport) := do
  let solver ← createInteractiveSolver solverPath
  let state ← buildProgramState prog solver
  let mut reports := []

  match prog with
  | .program _ decls =>
      for decl in decls.val.toList do
        match decl with
        | .procedure _ name params _ body =>
            if params.val.isEmpty && body.val.isSome then
              let bodyStmt := body.val.get!
              let (results, _finalState) ← symbolicExecuteStatementsWithDiagnosis ConversionContext.empty state decl bodyStmt

              reports := reports ++ [{
                procedureName := name.val
                results := results
              }]
            else
              pure ()
        | _ => pure ()

  closeVerificationState state
  return reports

end Strata.B3.Verifier

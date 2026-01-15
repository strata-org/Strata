/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Expression
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.Statements
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.Transform.FunctionToAxiom
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Program Verification

Program-level verification API for B3 programs.
Verifies entire programs with automatic diagnosis.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.SMT
open Strata.B3AST

---------------------------------------------------------------------
-- Batch Verification API
---------------------------------------------------------------------

/-- Extract function declarations from a B3 program -/
def extractFunctionDeclarations (prog : B3AST.Program SourceRange) : List (String × List String × String) :=
  match prog with
  | .program _ decls =>
      decls.val.toList.filterMap (fun decl =>
        match decl with
        | .function _ name params resultType _ body =>
            if body.val.isNone then
              let argTypes := params.val.toList.map (fun p =>
                match p with
                | .fParameter _ _ _ ty => b3TypeToSMT ty.val
              )
              let retType := b3TypeToSMT resultType.val
              some (name.val, argTypes, retType)
            else
              none
        | _ => none
      )

/-- Extract axiom expressions from a B3 program -/
def extractAxioms (prog : B3AST.Program SourceRange) : List (B3AST.Expression SourceRange) :=
  match prog with
  | .program _ decls =>
      decls.val.toList.filterMap (fun decl =>
        match decl with
        | .axiom _ _ expr => some expr
        | _ => none
      )

/-- Add declarations and axioms from a transformed B3 program to the verification state -/
private def addDeclarationsAndAxioms (state : B3VerificationState) (prog : B3AST.Program SourceRange) : IO (B3VerificationState × List String) := do
  let mut state := state
  let mut errors := []

  -- Add function declarations
  for (name, argTypes, retType) in extractFunctionDeclarations prog do
    state ← addFunctionDecl state name argTypes retType

  -- Add axioms
  for expr in extractAxioms prog do
    let convResult := expressionToSMT ConversionContext.empty expr
    state ← addPathCondition state expr convResult.term
    errors := errors ++ convResult.errors.map toString

  return (state, errors)

/-- Extract parameter-free procedures with bodies from a B3 program -/
def extractVerifiableProcedures (prog : B3AST.Program SourceRange) : List (String × B3AST.Decl SourceRange × B3AST.Statement SourceRange) :=
  match prog with
  | .program _ decls =>
      decls.val.toList.filterMap (fun decl =>
        match decl with
        | .procedure _ name params _ body =>
            if params.val.isEmpty && body.val.isSome then
              some (name.val, decl, body.val.get!)
            else
              none
        | _ => none
      )

/-- Translate a B3 program to SMT without automatic diagnosis (faster, less detailed errors) -/
def programToSMTWithoutDiagnosis (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String VerificationReport)) := do
  let initialState ← initVerificationState solver
  let mut results := []

  -- Transform: split functions into declarations + axioms
  let transformedProg := Transform.functionToAxiom prog

  -- Add function declarations and axioms
  let (state, conversionErrors) ← addDeclarationsAndAxioms initialState transformedProg

  -- Report conversion errors
  results := results ++ conversionErrors.map .error

  -- Verify parameter-free procedures
  for (_name, decl, bodyStmt) in extractVerifiableProcedures prog do
    let execResult ← statementToSMTWithoutDiagnosis ConversionContext.empty state decl bodyStmt
    -- Extract just the StatementResults (no diagnosis)
    let stmtResults := execResult.results.map (·.1)
    results := results ++ stmtResults.map StatementResult.toExcept

  closeVerificationState state
  return results

---------------------------------------------------------------------
-- Convenience Wrappers
---------------------------------------------------------------------

/-- Convert DDM Program to B3 AST with error handling -/
def programToB3AST (prog : Program) : Except String (B3AST.Program SourceRange) := do
  let [op] ← pure prog.commands.toList
    | .error "Expected single program command"

  if op.name.name != "command_program" then
    .error s!"Expected command_program, got {op.name.name}"

  let [ArgF.op progOp] ← pure op.args.toList
    | .error "Expected single program argument"

  let cstProg ← B3CST.Program.ofAst progOp

  let (ast, errors) := B3.programFromCST B3.FromCSTContext.empty cstProg
  if !errors.isEmpty then
    .error s!"CST to AST conversion errors: {errors}"
  else
    .ok ast

/-- Build verification state from B3 program (functions and axioms only, no procedures) -/
def buildProgramState (prog : Strata.B3AST.Program SourceRange) (solver : Solver) : IO B3VerificationState := do
  let state ← initVerificationState solver
  let transformedProg := Transform.functionToAxiom prog
  let (newState, errors) ← addDeclarationsAndAxioms state transformedProg
  -- Log errors if any
  for err in errors do
    IO.eprintln s!"Warning: {err}"
  return newState

/-- Generate SMT commands for a B3 program -/
def programToSMTCommands (prog : Strata.B3AST.Program SourceRange) : IO String := do
  let (solver, buffer) ← createBufferSolver
  let _ ← (Solver.setLogic "ALL").run solver
  let _ ← programToSMTWithoutDiagnosis prog solver
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

/-- Translate a B3 program to SMT and verify with automatic diagnosis.

Main entry point for verification.

Workflow:
1. Build program state (functions, axioms)
2. For each parameter-free procedure:
   - Translate statements to SMT
   - Check each VC
   - If failed, automatically diagnose to find root cause
3. Report all results with diagnosis

The solver is reset at the beginning to ensure clean state.
-/
def programToSMT (prog : Strata.B3AST.Program SourceRange) (solver : Solver) : IO (List ProcedureReport) := do
  -- Reset solver to clean state
  let _ ← (Solver.reset).run solver
  let state ← buildProgramState prog solver
  let mut reportsRev := []

  -- Verify parameter-free procedures
  for (name, decl, bodyStmt) in extractVerifiableProcedures prog do
    let execResult ← statementToSMT ConversionContext.empty state decl bodyStmt
    -- Extract VerificationReports with diagnosis
    let resultsWithDiag := execResult.results.filterMap (fun (stmtResult, diag) =>
      match stmtResult with
      | .verified report => some (report, diag)
      | .conversionError _ => none
    )
    reportsRev := {
      procedureName := name
      results := resultsWithDiag
    } :: reportsRev

  closeVerificationState state
  return reportsRev.reverse

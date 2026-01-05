/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.DDMTransform.DefinitionAST

/-!
# B3 Verifier High-Level API

High-level functions for adding declarations and managing verification state.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.SMT
open Strata.B3AST

---------------------------------------------------------------------
-- High-Level API Functions
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
      let argTypes := params.val.toList.map (fun _ => "Int")
      let mut state' ← addFunctionDecl state name.val argTypes "Int"

      match body.val with
      | some (.functionBody _ whens bodyExpr) =>
          let paramNames := params.val.toList.map (fun p => match p with | .fParameter _ _ n _ => n.val)
          let ctx' := paramNames.foldl (fun acc n => acc.push n) ConversionContext.empty
          match expressionToSMT ctx' bodyExpr with
          | .ok bodyTerm =>
              let paramVars := paramNames.map (fun n => Term.var ⟨n, .int⟩)
              let uf : UF := { id := name.val, args := paramVars.map (fun t => ⟨UF_ARG_PLACEHOLDER, t.typeOf⟩), out := .int }
              let funcCall := Term.app (.uf uf) paramVars .int
              let equality := Term.app .eq [funcCall, bodyTerm] .bool
              let axiomBody := if whens.val.isEmpty then
                equality
              else
                let whenTerms := whens.val.toList.filterMap (fun w =>
                  match w with
                  | .when _ e =>
                      match expressionToSMT ctx' e with
                      | .ok term => some term
                      | .error _ => none
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
          | .error _ => return state'
      | none => return state'
  | .axiom _ _ expr =>
      match expressionToSMT ConversionContext.empty expr with
      | .ok term => addAxiom state term
      | .error _ => return state
  | _ => return state

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

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter

/-!
# B3 Verifier

Main entry point for B3 program verification.
Provides both batch and incremental verification APIs.
-/

namespace Strata.B3.Verifier

open Strata.SMT

---------------------------------------------------------------------
-- Batch Verification API
---------------------------------------------------------------------

/-- Verify a B3 program using incremental API -/
def verifyProgram (prog : B3AST.Program Unit) (solverPath : String := "z3") : IO (List CheckResult) := do
  let mut state := initVerificationState
  let mut results := []

  match prog with
  | .program _ decls =>
      -- First pass: declare all functions
      for decl in decls.val.toList do
        match decl with
        | .function _ name params _ _ _ =>
            let argTypes := params.val.toList.map (fun _ => "Int")
            state := addFunctionDecl state name.val argTypes "Int"
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
                    state := addAssertion state axiomTerm
                | none => pure ()
            | none => pure ()
        | .axiom _ _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term => state := addAssertion state term
            | none => pure ()
        | .checkDecl _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term =>
                let result ← checkProperty state term decl solverPath
                results := results ++ [result]
            | none => pure ()
        | _ => pure ()

      return results

---------------------------------------------------------------------
-- SMT Command Generation (for debugging/inspection)
---------------------------------------------------------------------

/-- Generate SMT-LIB commands for a B3 program (without running solver) -/
def programToSMTCommands (prog : B3AST.Program M) : List String :=
  match prog with
  | .program _ decls =>
      let declList := decls.val.toList
      let functionDecls := declList.filterMap (fun d =>
        match d with
        | .function _ name params _ _ _ =>
            let argTypes := params.val.toList.map (fun _ => "Int")
            let argTypeStr := String.intercalate " " argTypes
            some s!"(declare-fun {name.val} ({argTypeStr}) Int)"
        | _ => none
      )
      let axioms := declList.flatMap (fun d =>
        match d with
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
                    [s!"(assert {formatTermDirect axiomTerm})"]
                | none => []
            | none => []
        | .axiom _ _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term => [s!"(assert {formatTermDirect term})"]
            | none => []
        | .checkDecl _ expr =>
            match expressionToSMT ConversionContext.empty expr with
            | some term =>
                [ "(push 1)"
                , s!"(assert (not {formatTermDirect term}))"
                , "(check-sat)"
                , "(pop 1)"
                ]
            | none => []
        | _ => []
      )
      functionDecls ++ axioms

end Strata.B3.Verifier

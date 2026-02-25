/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreSMT.State
import Strata.Languages.Core.CoreSMT.ExprTranslator

/-!
# CoreSMT Diagnosis Engine

When a verification check fails, this module diagnoses the failure by splitting
conjunction expressions and checking each conjunct individually. This helps
identify which specific sub-conditions are responsible for the failure.
-/

namespace Strata.Core.CoreSMT

open Core
open Strata.SMT
open Lambda

/-- Verification result for diagnosis -/
inductive DiagnosisResultType
  | refuted
  | counterexample
  | unknown
  deriving Repr, Inhabited

/-- Context for a diagnosed failure -/
structure DiagnosisContext where
  pathCondition : List Core.Expression.Expr := []
  deriving Repr, Inhabited

/-- Report for a diagnosed failure -/
structure DiagnosisReport where
  result : Except DiagnosisResultType Unit
  context : DiagnosisContext
  deriving Repr, Inhabited

/-- Result of diagnosing a single sub-expression -/
structure DiagnosedFailure where
  expression : Core.Expression.Expr
  isRefuted : Bool
  label : String
  report : DiagnosisReport
  deriving Repr, Inhabited

/-- Full diagnosis result -/
structure DiagnosisResult where
  originalLabel : String
  diagnosedFailures : List DiagnosedFailure
  deriving Repr, Inhabited

/-- Split a conjunction expression (And operator) into left and right.
    Matches the pattern: `app _ (app _ (op _ "Bool.And" _) lhs) rhs` -/
def splitConjunction (e : Core.Expression.Expr) : Option (Core.Expression.Expr × Core.Expression.Expr) :=
  match e with
  | .app _ (.app _ (.op _ name _) lhs) rhs =>
    if name.name == "Bool.And" then some (lhs, rhs)
    else none
  | _ => none

/-- Check if an expression is provably false (refuted) using push/pop -/
def checkRefuted (state : CoreSMTState) (E : Core.Env) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) : IO Bool := do
  match translateExpr E expr smtCtx with
  | Except.error _ => return false
  | Except.ok (term, _) =>
    state.solver.push
    state.solver.assert term
    let decision ← state.solver.checkSat
    state.solver.pop
    return decision == .unsat

/-- Diagnose a failed verification check by splitting conjunctions -/
partial def diagnoseFailure (state : CoreSMTState) (E : Core.Env)
    (expr : Core.Expression.Expr) (isReachCheck : Bool)
    (smtCtx : Core.SMT.Context) : IO DiagnosisResult := do
  match splitConjunction expr with
  | none =>
    let refuted ← checkRefuted state E expr smtCtx
    let resultType := if refuted then DiagnosisResultType.refuted else DiagnosisResultType.unknown
    let report : DiagnosisReport := { result := .error resultType, context := { pathCondition := [] } }
    return { originalLabel := "", diagnosedFailures := [{ expression := expr, isRefuted := refuted, label := "", report }] }
  | some (lhs, rhs) =>
    -- Diagnose left conjunct
    let leftResult ← diagnoseFailure state E lhs isReachCheck smtCtx
    -- For cover (reachability) checks, stop if left is refuted
    if isReachCheck then
      let leftRefuted := leftResult.diagnosedFailures.any (·.isRefuted)
      if leftRefuted then
        return { originalLabel := "", diagnosedFailures := leftResult.diagnosedFailures }
    -- Push, assert left as context, diagnose right conjunct, pop
    match translateExpr E lhs smtCtx with
    | Except.error _ =>
      return { originalLabel := "", diagnosedFailures := leftResult.diagnosedFailures }
    | Except.ok (lhsTerm, _) =>
      state.solver.push
      state.solver.assert lhsTerm
      let rightResult ← diagnoseFailure state E rhs isReachCheck smtCtx
      state.solver.pop
      return { originalLabel := ""
               diagnosedFailures := leftResult.diagnosedFailures ++ rightResult.diagnosedFailures }

end Strata.Core.CoreSMT

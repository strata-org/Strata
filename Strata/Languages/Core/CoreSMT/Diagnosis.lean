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
  report : DiagnosisReport
  deriving Repr, Inhabited

/-- Full diagnosis result -/
structure DiagnosisResult where
  diagnosedFailures : List DiagnosedFailure
  statePathCondition : List Core.Expression.Expr := []
  deriving Repr, Inhabited

/-- Split a conjunction expression (And operator) into left and right.
    Matches the pattern: `app _ (app _ (op _ "Bool.And" _) lhs) rhs` -/
def splitConjunction (e : Core.Expression.Expr) : Option (Core.Expression.Expr × Core.Expression.Expr) :=
  match e with
  | .app _ (.app _ (.op _ name _) lhs) rhs =>
    if name.name == "Bool.And" then some (lhs, rhs)
    else none
  | _ => none

/-- Diagnose a failed verification check by splitting conjunctions -/
partial def diagnoseFailure (state : CoreSMTState) (E : Core.Env)
    (expr : Core.Expression.Expr) (isReachCheck : Bool)
    (smtCtx : Core.SMT.Context)
    (pathCondition : List Core.Expression.Expr := []) : IO DiagnosisResult := do
  match splitConjunction expr with
  | none =>
    match translateExpr E expr smtCtx with
    | Except.error _ => return { diagnosedFailures := [] }
    | Except.ok (term, _) =>
      if isReachCheck then
        -- Reach: check if expr is refuted (always false)
        let decision ← state.solver.checkSatAssuming [term]
        if decision == .unsat then
          let report : DiagnosisReport := { result := .error .refuted, context := { pathCondition } }
          return { diagnosedFailures := [{ expression := expr, isRefuted := true, report }] }
        else
          return { diagnosedFailures := [] }
      else
        let provedDecision ← state.solver.checkSatAssuming [Factory.not term]
        if provedDecision == .unsat then
          return { diagnosedFailures := [] }
        let refutedDecision ← state.solver.checkSatAssuming [term]
        let isRefuted := refutedDecision == .unsat
        let resultType := if isRefuted then DiagnosisResultType.refuted else DiagnosisResultType.unknown
        let report : DiagnosisReport := { result := .error resultType, context := { pathCondition } }
        return { diagnosedFailures := [{ expression := expr, isRefuted, report }] }
  | some (lhs, rhs) =>
    let leftResult ← diagnoseFailure state E lhs isReachCheck smtCtx pathCondition
    if isReachCheck then
      let leftRefuted := leftResult.diagnosedFailures.any (·.isRefuted)
      if leftRefuted then
        return { diagnosedFailures := leftResult.diagnosedFailures }
    match translateExpr E lhs smtCtx with
    | Except.error _ =>
      return { diagnosedFailures := leftResult.diagnosedFailures }
    | Except.ok (lhsTerm, _) =>
      state.solver.push
      state.solver.assert lhsTerm
      let rightResult ← diagnoseFailure state E rhs isReachCheck smtCtx (lhs :: pathCondition)
      state.solver.pop
      return { diagnosedFailures := leftResult.diagnosedFailures ++ rightResult.diagnosedFailures }

end Strata.Core.CoreSMT

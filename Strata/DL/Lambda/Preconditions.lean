/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.IntBoolFactory
public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.LExprWF

/-! # Function Precondition Obligation Collection

This module provides infrastructure for collecting well-formedness obligations
from expressions that call functions with preconditions.
-/

namespace Lambda
open Std (ToFormat Format format)

public section

variable {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]

/-- A well-formedness obligation generated from a function call -/
structure WFObligation (T : LExprParams) where
  /-- Name of the function whose precondition must be satisfied -/
  funcName : String
  /-- The precondition with actual arguments substituted for formal parameters -/
  obligation : LExpr T.mono
  /-- Metadata from the call site for error reporting -/
  callSiteMetadata : T.Metadata
  /-- Metadata from the precondition definition -/
  precondMetadata : T.Metadata

instance [ToFormat T.Metadata] [ToFormat T.IDMeta] : ToFormat (WFObligation T) where
  format ob := f!"WFObligation({ob.funcName}, {ob.obligation}, {ob.callSiteMetadata})"

instance [ToFormat T.Metadata] [ToFormat T.IDMeta] : ToString (WFObligation T) where
  toString ob := toString (ToFormat.format ob)

/--
Substitute actual arguments for formal parameters in a precondition.
Given a precondition expression with free variables matching the function's
formal parameter names, and a list of actual argument expressions,
returns the precondition with formals replaced by actuals.
-/
def substitutePrecondition
    (precond : LExpr T.mono)
    (formals : List (Identifier T.IDMeta × LMonoTy))
    (actuals : List (LExpr T.mono))
    : LExpr T.mono :=
  let substitution := formals.zip actuals |>.map fun ((name, _), actual) => (name, actual)
  LExpr.substFvarsLifting precond substitution

/--
Collect all WF obligations from an expression by traversing it and finding
all calls to functions with preconditions.

For each call to a function with preconditions:
1. Get the function's preconditions from the Factory
2. Substitute actual arguments for formal parameters
3. Create a WFObligation with the call-site metadata
4. Wrap in enclosing quantifiers and implications
-/
def collectWFObligations [Coe String (T.Identifier)]  [Inhabited T.Metadata] (F : Factory T) (e : LExpr T.mono) : List (WFObligation T) :=
  go F e []
where
  go (F : Factory T) (e : LExpr T.mono)
      (implications : List (T.Metadata × LExpr T.mono)) : List (WFObligation T) :=
    -- A function call generates an obligation that the precondition is
    -- satisfied under the current assumptions
    let callObligations := match Factory.callOfLFunc F e with
      | some (_op, args, func) =>
        if func.preconditions.isEmpty then []
        else
          let md := e.metadata
          func.preconditions.map fun precond =>
            let substedPrecond := substitutePrecondition precond.expr func.inputs args
            { funcName := func.name.name
              obligation := wrapImplications implications substedPrecond
              callSiteMetadata := md
              precondMetadata := precond.md : WFObligation T }
      | none => []
    let subObligations := match e with
      | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ => []
      -- Need to quantify over bound variable
      -- e.g. λ x => 2 / x gives precondition ∀ x, x != 0
      | .abs md name ty body =>
        (go F body implications).map fun ob =>
          { ob with obligation := .quant md .all name ty (.bvar md 0) ob.obligation }
      | .quant md _ name ty trigger body =>
        (go F body implications).map fun ob =>
          { ob with obligation := .quant md .all name ty trigger ob.obligation }
      /- If we are on the RHS of an implication, add assumption
        E.g. y > 0 ==> x / y = 1 should produce
        y > 0 ==> y != 0 -/
      | .app md (.app _ (.op _ opName _) lhs) rhs =>
        if opName == (@boolImpliesFunc T).name then
          let lhsObs := go F lhs implications
          let rhsObs := go F rhs ((md, lhs) :: implications)
          lhsObs ++ rhsObs
        else
          go F lhs implications ++ go F rhs implications
      /- Let-binding encoded as (λ x. body) arg:
         obligations from body are wrapped as let x := arg in ob,
         obligations from arg are collected directly -/
      | .app md (.abs amd name ty body) arg =>
        let argObs := go F arg implications
        let bodyObs := (go F body implications).map fun ob =>
          { ob with obligation := .app md (.abs amd name ty ob.obligation) arg }
        argObs ++ bodyObs
      | .app _ fn arg => go F fn implications ++ go F arg implications
      | .ite md c t f =>
        /- Similarly, if-then-else adds assumption in each branch
        E.g. if y > 0 then x / y else 0 produces
        y > 0 ==> y != 0-/
        let cObs := go F c implications
        let tObs := go F t ((md, c) :: implications)
        let fObs := go F f ((md, .app md (@boolNotFunc T).opExpr c) :: implications)
        cObs ++ tObs ++ fObs
      | .eq _ e1 e2 => go F e1 implications ++ go F e2 implications
    -- Output subObligations first, so that e.g. (x / (y / z)) first outputs
    -- z ≠ 0, and then (y / z ≠ 0)
    subObligations ++ callObligations

end -- public section
end Lambda

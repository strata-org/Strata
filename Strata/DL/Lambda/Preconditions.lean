/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LExprWF

/-! # Function Precondition Obligation Collection

This module provides infrastructure for collecting well-formedness obligations
from expressions that call functions with preconditions.
-/

namespace Lambda
open Std (ToFormat Format format)

variable {T : LExprParams} [DecidableEq T.IDMeta] [BEq T.IDMeta]

/-- A well-formedness obligation generated from a function call -/
structure WFObligation (T : LExprParams) where
  /-- Name of the function whose precondition must be satisfied -/
  funcName : String
  /-- The precondition with actual arguments substituted for formal parameters -/
  obligation : LExpr T.mono
  /-- Metadata from the call site for error reporting -/
  callSiteMetadata : T.Metadata

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
  LExpr.substFvars precond substitution

/--
Collect all WF obligations from an expression by traversing it and finding
all calls to functions with preconditions.

For each call to a function with preconditions:
1. Get the function's preconditions from the Factory
2. Substitute actual arguments for formal parameters
3. Create a WFObligation with the call-site metadata
-/
def collectWFObligations (F : Factory T) (e : LExpr T.mono) : List (WFObligation T) :=
  -- First, check if this expression is a function call with preconditions
  let callObligations := match Factory.callOfLFunc F e with
    | some (_op, args, func) =>
      if func.preconditions.isEmpty then []
      else
        let md := e.metadata
        func.preconditions.map fun precond =>
          { funcName := func.name.name
            obligation := substitutePrecondition precond func.inputs args
            callSiteMetadata := md : WFObligation T }
    | none => []
  -- Then recursively collect from subexpressions
  let subObligations := match e with
    | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ => []
    | .abs _ _ body => collectWFObligations F body
    | .quant _ _ _ trigger body => collectWFObligations F trigger ++ collectWFObligations F body
    | .app _ fn arg => collectWFObligations F fn ++ collectWFObligations F arg
    | .ite _ c t f => collectWFObligations F c ++ collectWFObligations F t ++ collectWFObligations F f
    | .eq _ e1 e2 => collectWFObligations F e1 ++ collectWFObligations F e2
  callObligations ++ subObligations

end Lambda

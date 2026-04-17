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
  /-- Internal bookkeeping: whether this obligation was propagated from a let-bound argument.
      Always `false` in the list returned by `collectWFObligations` (reset on output). -/
  fromLetArg : Bool := false

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

The evaluation semantics of functions with preconditions are only defined
if the precondition holds e.g. for `f(x) requires P(x) = b(x)`, we have that
`.app f y --> b(y)` only when `P(y)` holds. Otherwise, evaluation is stuck.

`collectWFObligations e` creates a set of proof obligations such that, if
all generated obligations are valid, then the evaluation of `e` is not stuck
due to an invalid precondition:
for any function call `f` inside `e` with preconditions, either the precondition
of `f` is valid at the call site or there is an evaluation sequence that does
not use the `.app` rule on `f`.
-/
def collectWFObligations [Coe String (T.Identifier)]  [Inhabited T.Metadata] (F : Factory T) (e : LExpr T.mono) : List (WFObligation T) :=
  go F e [] {}
where
  /-- Wrap an obligation with accumulated implications -/
  wrapImplications (implications : List (T.Metadata × LExpr T.mono))
      (ob : LExpr T.mono) : LExpr T.mono :=
    implications.foldr (fun (md, lhs) acc =>
      .app md (.app md (@boolImpliesFunc T).opExpr lhs) acc) ob

  /-- Shift all keys in the let-obligations map up by 1 (for entering a binder).
      The keys of `m` are De Bruijn indices. -/
  shiftLetObs (m : Std.HashMap Nat (List (WFObligation T))) : Std.HashMap Nat (List (WFObligation T)) :=
    m.fold (fun acc k v => acc.insert (k + 1) v) {}

  go (F : Factory T) (e : LExpr T.mono)
      (implications : List (T.Metadata × LExpr T.mono))
      (letObs : Std.HashMap Nat (List (WFObligation T))) : List (WFObligation T) :=
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
      | .const _ _ | .op _ _ _ | .fvar _ _ _ => []
      /- Bound variable: emit any let-bound obligations at current implications -/
      | .bvar _ i =>
        match letObs.get? i with
        | none => []
        | some obs => obs.map fun ob =>
            { ob with obligation := wrapImplications implications ob.obligation
                      fromLetArg := true }
      -- Need to quantify over bound variable
      -- e.g. λ x => 2 / x gives precondition ∀ x, x != 0
      | .abs md name ty body =>
        (go F body implications (shiftLetObs letObs)).map fun ob =>
          { ob with obligation := .quant md .all name ty (.bvar md 0) ob.obligation }
      | .quant md _ name ty trigger body =>
        (go F body implications (shiftLetObs letObs)).map fun ob =>
          { ob with obligation := .quant md .all name ty trigger ob.obligation }
      | .app md (.app _ (.op _ opName _) lhs) rhs =>
        /- p ==> e: preconditions in e can assume p
           E.g. y > 0 ==> x / y > 0 should produce
           y > 0 ==> y != 0 -/
        if opName == (@boolImpliesFunc T).name then
          let lhsObs := go F lhs implications letObs
          let rhsObs := go F rhs ((md, lhs) :: implications) letObs
          lhsObs ++ rhsObs
        /- p || e: preconditions in e can assume ¬p
           E.g. y == 0 || x / y > 0 should produce
           ¬(y == 0) ==> y != 0 -/
        else if opName == (@boolOrFunc T).name then
          let lhsObs := go F lhs implications letObs
          let rhsObs := go F rhs ((md, .app md (@boolNotFunc T).opExpr lhs) :: implications) letObs
          lhsObs ++ rhsObs
        /- p && e: preconditions in e can assume p
           E.g. y != 0 && x / y > 0 should produce
           y != 0 ==> y != 0 -/
        else if opName == (@boolAndFunc T).name then
          let lhsObs := go F lhs implications letObs
          let rhsObs := go F rhs ((md, lhs) :: implications) letObs
          lhsObs ++ rhsObs
        else
          go F lhs implications letObs ++ go F rhs implications letObs
      /- Let-binding encoded as (λ x. body) arg:
         - Arg obligations are stored in the map at index 0 for the body,
           so they are emitted at usage sites with local assumptions.
           These are tagged fromLetArg and NOT wrapped in the let.
           E.g. `let x := safeDiv(a, b) in p ==> x > 0` produces
           `p ==> b != 0` (the arg obligation `b != 0` inherits the
           implication context at the usage site of `x`).
         - Body obligations from calls in the body are wrapped in the let.
           E.g. `let x := safeDiv(a, b) in safeDiv(c, x)` produces
           `(let x := safeDiv(a, b) in x != 0)` since the body call
           `safeDiv(c, x)` generates `x != 0` which references `x`.
       -/
      | .app md (.abs amd name ty body) arg =>
        -- Fresh context (no implications/letObs): arg obligations are collected
        -- independently and re-emitted at usage sites with local assumptions.
        let argObs := collectWFObligations F arg
        let letObs' := (shiftLetObs letObs).insert 0 argObs
        let bodyObs := go F body implications letObs'
        let (fromLet, regular) := bodyObs.partition (·.fromLetArg)
        let wrappedRegular := regular.map fun ob =>
          { ob with obligation := .app md (.abs amd name ty ob.obligation) arg }
        let resetFromLet := fromLet.map ({ · with fromLetArg := false })
        resetFromLet ++ wrappedRegular
      | .app _ fn arg => go F fn implications letObs ++ go F arg implications letObs
      | .ite md c t f =>
        /- Similarly, if-then-else adds assumption in each branch
        E.g. if y > 0 then x / y else 0 produces
        y > 0 ==> y != 0-/
        let cObs := go F c implications letObs
        let tObs := go F t ((md, c) :: implications) letObs
        let fObs := go F f ((md, .app md (@boolNotFunc T).opExpr c) :: implications) letObs
        cObs ++ tObs ++ fObs
      | .eq _ e1 e2 => go F e1 implications letObs ++ go F e2 implications letObs
    -- Output subObligations first, so that e.g. (x / (y / z)) first outputs
    -- z ≠ 0, and then (y / z ≠ 0)
    subObligations ++ callObligations

end -- public section
end Lambda

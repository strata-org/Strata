/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform

/-! # Expression Simplification

Algebraic simplification rules for boolean operations that the Factory's
`concreteEval` / function body inlining cannot optimize further (e.g., when
one operand is symbolic).

The main entry point is `simplifyExpr`, which alternates between
`LExpr.eval` (partial evaluation via the Factory) and pattern-based
boolean simplification until a fixed point or fuel exhaustion. -/

public section

namespace Core
namespace SimplifyExpr

open Core.Transform Lambda

/-- Try to simplify a boolean expression by one step using algebraic laws.
    Uses `Factory.callOfLFunc` to decompose factory function calls.
    Only handles cases where `LExpr.eval` cannot reduce further, i.e., when
    one operand is symbolic. Returns `some simplified` if a rule fires. -/
def simplifyBoolOp (F : Lambda.Factory CoreLParams) (e : Expression.Expr)
    : Option Expression.Expr :=
  match Factory.callOfLFunc F e with
  | some (_, args, func) =>
    match func.name.name, args with
    -- Bool.And: identity (true) and annihilation (false)
    | "Bool.And", [a, b] =>
      match a, b with
      | .true _,  _        => some b          -- true && x  = x
      | _,        .true _  => some a          -- x && true  = x
      | .false m, _        => some (.false m) -- false && x = false
      | _,        .false m => some (.false m) -- x && false = false
      | _, _ => none
    -- Bool.Or: identity (false) and annihilation (true)
    | "Bool.Or", [a, b] =>
      match a, b with
      | .false _, _        => some b          -- false || x = x
      | _,        .false _ => some a          -- x || false = x
      | .true m,  _        => some (.true m)  -- true || x  = true
      | _,        .true m  => some (.true m)  -- x || true  = true
      | _, _ => none
    -- Bool.Not: double negation
    | "Bool.Not", [a] =>
      -- !!x = x
      match Factory.callOfLFunc F a with
      | some (_, [inner], innerFunc) =>
        if innerFunc.name.name == "Bool.Not" then some inner else none
      | _ => none
    -- Bool.Implies: absorption by false/true
    | "Bool.Implies", [a, b] =>
      match a, b with
      | .false m, _        => some (.true m)  -- false ==> x = true
      | _,        .true m  => some (.true m)  -- x ==> true = true
      | .true _,  _        => some b          -- true ==> x = x
      | _, _ => none
    -- Bool.Equiv: identity (true)
    | "Bool.Equiv", [a, b] =>
      match a, b with
      | .true _,  _        => some b          -- true <==> x = x
      | _,        .true _  => some a          -- x <==> true = x
      | _, _ => none
    | _, _ => none
  | none => none

/-- Bottom-up traversal of an expression. Recursively processes sub-expressions
    of `app`, `ite`, and `eq` nodes, then applies `f` once to the rebuilt node.
    Skips `.abs` and `.quant` (bound-variable binders).
    Returns `some e'` if `f` fired anywhere, `none` if nothing changed. -/
def traverseExpr (f : Expression.Expr → Option Expression.Expr) (e : Expression.Expr)
    : Option Expression.Expr :=
  match e with
  | .app m fn arg =>
    let fn'  := traverseExpr f fn
    let arg' := traverseExpr f arg
    let e' := .app m (fn'.getD fn) (arg'.getD arg)
    match f e' with
    | some e'' => some e''
    | none => if fn'.isSome || arg'.isSome then some e' else none
  | .ite m c t el =>
    let c'  := traverseExpr f c
    let t'  := traverseExpr f t
    let el' := traverseExpr f el
    let e' := .ite m (c'.getD c) (t'.getD t) (el'.getD el)
    match f e' with
    | some e'' => some e''
    | none => if c'.isSome || t'.isSome || el'.isSome then some e' else none
  | .eq m e1 e2 =>
    let e1' := traverseExpr f e1
    let e2' := traverseExpr f e2
    let e' := .eq m (e1'.getD e1) (e2'.getD e2)
    match f e' with
    | some e'' => some e''
    | none => if e1'.isSome || e2'.isSome then some e' else none
  | .const _ _         => f e
  | .op _ _ _          => f e
  | .bvar _ _          => f e
  | .fvar _ _ _        => f e
  | .abs _ _ _ _       => f e
  | .quant _ _ _ _ _ _ => f e

/-- Partially evaluate and simplify `e`. Alternates between `LExpr.eval`
    (Factory-based partial evaluation) and `simplifyBoolOp` (algebraic
    boolean rules applied bottom-up) until a fixed point or fuel exhaustion. -/
def simplifyExpr (fuel : Nat) (σ : LState CoreLParams) (e : Expression.Expr)
    : Expression.Expr :=
  let e' := LExpr.eval σ.config.fuel σ e
  match fuel with
  | 0 => e'
  | n + 1 =>
    match traverseExpr (simplifyBoolOp σ.config.factory) e' with
    | none => e'  -- nothing changed, fixed point reached
    | some e'' =>
      -- Re-run the full pipeline after boolean simplification in case
      -- it unlocks further reductions.
      simplifyExpr n σ e''

end SimplifyExpr
end Core

end -- public section

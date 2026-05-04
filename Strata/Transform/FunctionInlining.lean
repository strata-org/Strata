/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions
import Strata.DL.Lambda.LExprWF

namespace Strata

/-! ## Function Inlining

Core-to-Core transforms that replace function calls with their bodies.

Uses the same inlining logic as `LExprEval.eval`: `Factory.callOfLFunc`
to decompose applications, `LFunc.computeTypeSubst` + `LExpr.applySubst`
for polymorphic type instantiation, and `substFvarsLifting` for
capture-safe substitution under binders.
-/

public section

/-- Try to inline a single function call. Returns `some result` if the
    function has a body and is fully applied; `none` otherwise.
    Handles polymorphic functions via type substitution, matching
    the inlining path in `LExprEval.eval`. -/
private def tryInlineCall
    (factory : Lambda.Factory Core.CoreLParams)
    (e : Lambda.LExpr Core.CoreLParams.mono)
    : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  match factory.callOfLFunc e with
  | some (op_expr, args, lfunc) =>
    match lfunc.body with
    | none => none
    | some body =>
      match Lambda.LFunc.computeTypeSubst lfunc op_expr args with
      | some tySubst =>
        let body := body.applySubst tySubst
        let input_map := lfunc.inputs.keys.zip args
        some (Lambda.LExpr.substFvarsLifting body input_map)
      | none => none
  | none => none

/--
Inline non-recursive function bodies in an expression. For each fully-applied
call `f(a₁, ..., aₙ)` where `f` has a known body in the factory, replace it
with `body[a₁/x₁, ..., aₙ/xₙ]` (with polymorphic type instantiation).
-/
partial def inlineFuncDefs
    (factory : Lambda.Factory Core.CoreLParams)
    (postProcess : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono := id)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  let rec go (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
    -- First recurse into subexpressions
    let e' := match e with
      | .app m f a => .app m (go f) (go a)
      | .ite m c t el => .ite m (go c) (go t) (go el)
      | .abs m n ty b => .abs m n ty (go b)
      | .quant m k n ty tr b => .quant m k n ty (go tr) (go b)
      | .eq m l r => .eq m (go l) (go r)
      | other => other
    -- Then try to inline the (possibly rebuilt) application
    match tryInlineCall factory e' with
    | some inlined => go (postProcess inlined)
    | none => postProcess e'
  go e

/-- Inline recursive function calls with bounded unrolling.
    At depth 0, recursive calls are left as-is (uninterpreted).
    Uses the factory for function lookup and type substitution. -/
partial def inlineRecFuncDefs
    (factory : Lambda.Factory Core.CoreLParams)
    (maxDepth : Nat)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  go maxDepth e
where
  go (depth : Nat) (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono :=
    if depth == 0 then e
    else
      let e' := match e with
        | .app m f a => .app m (go depth f) (go depth a)
        | .ite m c t el => .ite m (go depth c) (go depth t) (go depth el)
        | .abs m n ty b => .abs m n ty (go depth b)
        | .quant m k n ty tr b => .quant m k n ty (go depth tr) (go depth b)
        | .eq m l r => .eq m (go depth l) (go depth r)
        | other => other
      match tryInlineCall factory e' with
      | some inlined => go (depth - 1) inlined
      | none => e'

end -- public section

end Strata

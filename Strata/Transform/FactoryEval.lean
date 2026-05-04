/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LExprEval

namespace Strata

open Lambda.LExpr (isCanonicalValue isConstrApp)
open Strata.DL.Util (FuncAttr)

/-! ## Factory Concrete Evaluation

A Core-to-Core transform that fires `concreteEval` for factory functions
with all-concrete arguments. Uses the same evaluation criteria as
`LExprEval.eval` (`isCanonicalValue`, `isConstrApp`, and the
`evalIfConstr`/`evalIfCanonical` function attributes).

The `tryConcreteEval` helper mirrors the guard logic in `LExprEval.eval`.
Ideally it would be defined once in `LExprEval.lean` and called from both
places, but refactoring `eval` to use it requires updating the Semantics
proofs (which depend on the exact code structure of `eval`). This is
tracked as a follow-up.
-/

public section

/-- Try to concretely evaluate a factory function application.
    Checks the same criteria as `LExprEval.eval`: all args canonical,
    or the designated constructor/canonical argument is present.
    Returns `some result` on success, `none` otherwise. -/
private def tryConcreteEval
    (factory : Lambda.Factory Core.CoreLParams)
    (e : Lambda.LExpr Core.CoreLParams.mono)
    (args : List (Lambda.LExpr Core.CoreLParams.mono))
    (lfunc : Lambda.LFunc Core.CoreLParams)
    : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  let constrArgAt (idx : Option Nat) :=
    match idx with
    | some i => (args[i]? |>.map (isConstrApp factory)).getD false
    | none => false
  let canonicalArgAt (idx : Option Nat) :=
    match idx with
    | some i => (args[i]? |>.map (isCanonicalValue factory)).getD false
    | none => false
  if args.all (isCanonicalValue factory) ||
    constrArgAt (FuncAttr.findEvalIfConstr lfunc.attr) ||
    canonicalArgAt (FuncAttr.findEvalIfCanonical lfunc.attr) then
    match lfunc.concreteEval with
    | none => none
    | some ceval => ceval e.metadata args
  else
    none

/-- Evaluate factory functions with all-concrete arguments.
    Recurses into all subexpressions, rebuilds applications, and fires
    `tryConcreteEval` when available. -/
partial def evalConcreteFactoryApps
    (factory : Lambda.Factory Core.CoreLParams)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  let go := evalConcreteFactoryApps factory
  match e with
  | .app m f a =>
    let rebuilt := Lambda.LExpr.app m (go f) (go a)
    match Lambda.Factory.callOfLFunc factory rebuilt with
    | some (_, args, lfunc) =>
      match tryConcreteEval factory rebuilt args lfunc with
      | some e' => go e'
      | none => rebuilt
    | none => rebuilt
  | .ite m c t el => .ite m (go c) (go t) (go el)
  | .abs m n ty b => .abs m n ty (go b)
  | .quant m k n ty tr b => .quant m k n ty (go tr) (go b)
  | .eq m e1 e2 => .eq m (go e1) (go e2)
  | _ => e

end -- public section

end Strata

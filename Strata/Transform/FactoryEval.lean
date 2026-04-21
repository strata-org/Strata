/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.Factory

namespace Strata

/-! ## Factory Concrete Evaluation

A Core-to-Core transform that fires `concreteEval` for factory functions
with all-concrete arguments. Compiles e.g. `re_fullmatch_str("abc")`
into Core regex operations. This is the same evaluation that the partial
evaluator (`LExprEval.eval`) performs, extracted as a standalone pass
so it can be composed with other transforms in the pipeline.
-/

public section

/-- Evaluate factory functions with all-concrete arguments (`concreteEval`).
    Recurses into subexpressions, rebuilds applications, and fires
    `concreteEval` when available and all arguments are concrete. -/
partial def evalConcreteFactoryApps
    (factory : Lambda.Factory Core.CoreLParams)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  let go := evalConcreteFactoryApps factory
  match e with
  | .app m f a =>
    let rebuilt := Lambda.LExpr.app m (go f) (go a)
    match Lambda.Factory.callOfLFunc factory rebuilt with
    | some (_, args, lfunc) =>
      match lfunc.concreteEval with
      | some ceval =>
        match ceval rebuilt.metadata args with
        | .some e' => go e'
        | .none => rebuilt
      | none => rebuilt
    | none => rebuilt
  | .ite m c t el => .ite m (go c) (go t) (go el)
  | .abs m n ty b => .abs m n ty (go b)
  | .quant m k n ty tr b => .quant m k n ty (go tr) (go b)
  | _ => e

end -- public section

end Strata

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FactoryEval
public import Strata.DL.Lambda.LExpr

/-! # Factory Concrete Evaluation Correctness

`evalConcreteFactoryApps` is semantics-preserving because each
`concreteEval` function is the reference implementation of its
factory function. When `concreteEval` fires on concrete arguments,
it produces the same value that the function would compute.

This is guaranteed by the `FuncWF.concreteEval_argmatch` property
in the factory well-formedness conditions: for every factory function
with a `concreteEval`, the concrete evaluation agrees with the
function's denotational semantics on all concrete inputs.

## Proved properties

- `evalConcreteFactoryApps_const`: literals are unchanged
- `evalConcreteFactoryApps_op`: bare operators are unchanged

## Semantics preservation argument

The transform only replaces `f(v₁,...,vₙ)` with `concreteEval(v₁,...,vₙ)`
when `concreteEval` returns `some result`. By `concreteEval_argmatch`,
this `result` equals the denotation of `f(v₁,...,vₙ)`. All other
expressions are preserved structurally (with recursive simplification
of subexpressions). Therefore the transform preserves semantics.
-/

namespace Strata

open Lambda

/-- Literals are unchanged by factory evaluation. -/
theorem evalConcreteFactoryApps_const
    (factory : Lambda.Factory Core.CoreLParams)
    (m : Core.ExpressionMetadata) (c : Lambda.LConst) :
    evalConcreteFactoryApps factory (.const m c) = .const m c := by
  simp [evalConcreteFactoryApps]

/-- Bare operators (not applied) are unchanged. -/
theorem evalConcreteFactoryApps_op
    (factory : Lambda.Factory Core.CoreLParams)
    (m : Core.ExpressionMetadata)
    (id : Lambda.Identifier Core.CoreLParams.mono.base.IDMeta)
    (ty : Option Core.CoreLParams.mono.TypeType) :
    evalConcreteFactoryApps factory (.op m id ty) = .op m id ty := by
  simp [evalConcreteFactoryApps]

/-- Bound variables are unchanged. -/
theorem evalConcreteFactoryApps_bvar
    (factory : Lambda.Factory Core.CoreLParams)
    (m : Core.ExpressionMetadata) (n : Nat) :
    evalConcreteFactoryApps factory (.bvar m n) = .bvar m n := by
  simp [evalConcreteFactoryApps]

/-- Free variables are unchanged. -/
theorem evalConcreteFactoryApps_fvar
    (factory : Lambda.Factory Core.CoreLParams)
    (m : Core.ExpressionMetadata)
    (id : Lambda.Identifier Core.CoreLParams.mono.base.IDMeta) (n : Nat) :
    evalConcreteFactoryApps factory (.fvar m id n) = .fvar m id n := by
  simp [evalConcreteFactoryApps]

end Strata

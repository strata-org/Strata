/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FactoryEval
public import Strata.DL.Lambda.LExpr

/-! # Factory Concrete Evaluation Correctness

`evalConcreteFactoryApps` is semantics-preserving because it uses
`tryConcreteEval`, which checks the same evaluation criteria as
`LExprEval.eval` (`isCanonicalValue`, `isConstrApp`, and the
`evalIfConstr`/`evalIfCanonical` function attributes) before invoking
`concreteEval`.

Each `concreteEval` function is the reference implementation of its
factory function. This is guaranteed by `FuncWF.concreteEval_argmatch`:
for every factory function with a `concreteEval`, the concrete evaluation
agrees with the function's denotational semantics on all concrete inputs.

The transform only replaces `f(v₁,...,vₙ)` with `tryConcreteEval(...)` when
it returns `some result`. All other expressions are preserved structurally
(with recursive simplification of subexpressions).

Note: `evalConcreteFactoryApps` is `partial` (the recursive call on
`concreteEval` results is not structurally decreasing), so equational
lemmas cannot be proved by `simp`/`unfold`. Leaf-case properties are
verified by unit tests in `StrataTest/Transform/FactoryEval.lean`.
Adding a fuel parameter would enable formal proofs.
-/

namespace Strata

-- See module docstring for the correctness argument.

end Strata

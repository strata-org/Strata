/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTraversal
import all Strata.DL.Lambda.LExprTraversal

/-! # Correctness of the memoized `LExpr.Traversal` traversals

Each pointer-address-memoized traversal in `LExprTraversal.lean` is a
*transparent* optimization: it computes exactly the pure reference, on the nose,
for every expression and from any starting cache.  Each proof is a one-line
corollary of the generic `Strata.PtrCache.run'_output_eq` — the `Result` every
cache entry carries already pins the value, so no bespoke induction is needed.

Key results:

- `applyOnceDFSPtrCache_run'_eq` — threading any cache through
  `applyOnceDFSPtrCache` yields exactly `applyOnceDFS`.
- `applyOnceDFSPtrCached_eq` — the fresh-cache wrapper computes exactly
  `applyOnceDFS`.
- `visitDFSPtrCache_run'_eq` — threading any cache through `visitDFSPtrCache`
  yields exactly `visitDFS`.
- `visitDFSPtrCached_eq` — the fresh-cache wrapper computes exactly `visitDFS`.
-/

namespace Lambda
namespace LExpr
namespace Traversal

public section

open Strata.PtrCache

/-- Running the pointer-memoized depth-first rewrite from any starting cache
    produces the same (rewritten tree, accumulated writer) pair as the uncached
    pure traversal — the memoization is a transparent optimization. -/
theorem applyOnceDFSPtrCache_run'_eq {T : LExprParamsT} {ω : Type} [Append ω]
    (order : Order) (f : LExpr T → Option (LExpr T) × ω) (e : LExpr T)
    (c : PtrCache (applyOnceDFS order f)) :
    ((applyOnceDFSPtrCache order f e).run' c).output = applyOnceDFS order f e :=
  run'_output_eq (applyOnceDFSPtrCache order f e) c

/-- Running the pointer-memoized depth-first rewrite with a fresh cache produces
    the same result as the uncached pure traversal. -/
theorem applyOnceDFSPtrCached_eq {T : LExprParamsT} {ω : Type} [Append ω]
    (order : Order) (f : LExpr T → Option (LExpr T) × ω) (e : LExpr T) :
    applyOnceDFSPtrCached order f e = applyOnceDFS order f e :=
  run'_output_eq (applyOnceDFSPtrCache order f e) PtrCache.empty

/-- Running the pointer-memoized depth-first fold from any starting cache
    produces the same accumulated writer as the uncached pure fold. -/
theorem visitDFSPtrCache_run'_eq {T : LExprParamsT} {ω : Type} [Append ω]
    (order : Order) (f : LExpr T → ω) (e : LExpr T) (c : PtrCache (visitDFS order f)) :
    ((visitDFSPtrCache order f e).run' c).output = visitDFS order f e :=
  run'_output_eq (visitDFSPtrCache order f e) c

/-- Running the pointer-memoized depth-first fold with a fresh cache produces the
    same accumulated writer as the uncached pure fold. -/
theorem visitDFSPtrCached_eq {T : LExprParamsT} {ω : Type} [Append ω]
    (order : Order) (f : LExpr T → ω) (e : LExpr T) :
    visitDFSPtrCached order f e = visitDFS order f e :=
  run'_output_eq (visitDFSPtrCache order f e) PtrCache.empty

end -- public section

end Traversal
end LExpr
end Lambda

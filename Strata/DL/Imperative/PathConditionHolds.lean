/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext
public import Strata.DL.Imperative.Store

/-!
## When a path condition holds

The meaning of a path condition in a store: what a back end that is given an obligation's
path condition may assume about the values of its variables.

- `PathConditionEntry.Holds` — one entry holds in a store
- `PathConditions.Holds` — every entry of a list of path conditions holds in a store
-/

namespace Imperative

public section

/-- The path-condition entry `entry` holds in the store `σ` under the factory `f`: an
    assumption evaluates to `true`; a deterministic definition's variable holds the value its
    right-hand side evaluates to; the expressions of a distinctness fact evaluate to pairwise
    distinct values; a declaration without a value constrains nothing. -/
@[expose] def PathConditionEntry.Holds {P : PureExpr} [HasBool P] (f : P.Factory)
    (σ : SemanticStore P) : PathConditionEntry P → Prop
  | .assumption _ e => P.eval f σ e = some (HasBool.ttVal f)
  | .varDecl x _ (.det e) => ∃ v, P.eval f σ e = some v ∧ σ x = some v
  | .varDecl _ _ .nondet => True
  | .distinct _ es => ∃ vs, es.mapM (P.eval f σ) = some vs ∧ vs.Nodup

/-- Every entry of every path condition in `pcs` holds in the store `σ` under the factory
    `f`. -/
@[expose] def PathConditions.Holds {P : PureExpr} [HasBool P] (f : P.Factory)
    (σ : SemanticStore P) (pcs : PathConditions P) : Prop :=
  ∀ pc ∈ pcs, ∀ entry ∈ pc, PathConditionEntry.Holds f σ entry

end -- public section

end Imperative

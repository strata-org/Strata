/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Store

---------------------------------------------------------------------

namespace Imperative

/-! # Store relations

Store-to-store comparison relations for the Imperative dialect's
`SemanticStore`. Core store definitions and predicates live in `Store`; event
and trace relations build on the comparisons here through `CmdTrace` without
introducing a dependency on command or statement semantics.

- `StoreAgreement`: asymmetric agreement — wherever the source store is defined,
  the target store assigns the same value.
- `StoreProjected`: a store obtained by dropping bindings from a source store.
- `StoreAgreesOnFvars`: two stores agree on every free variable of an expression.
- `StoreExtendsWith`: a classified store extension — every source binding is
  preserved and every target-only binding satisfies an extra-register class.

The command-level metatheory of these relations lives in `StoreRelationsProps`;
the statement-level scope-projection laws live in `StmtSemanticsProps`.
-/

public section

/-! ### Store comparison relations -/

/-- Asymmetric agreement between two stores: wherever `σ_struct` is defined (per
`isDefined`), `σ_cfg` assigns the same value at that variable. -/
@[expose] def StoreAgreement {P : PureExpr}
    (σ_struct σ_cfg : SemanticStore P) : Prop :=
  ∀ x, isDefined σ_struct [x] → σ_struct x = σ_cfg x

/-- `projected` is obtained from `source` by dropping zero or more bindings:
every binding retained by `projected` has the same value in `source`. -/
@[expose] def StoreProjected {P : PureExpr}
    (source projected : SemanticStore P) : Prop :=
  StoreAgreement projected source

/-- Two stores agree at every free variable of `expr`. -/
@[expose] def StoreAgreesOnFvars {P : PureExpr} [HasFvars P]
    (source target : SemanticStore P) (expr : P.Expr) : Prop :=
  ∀ ident ∈ HasFvars.getFvars expr, source ident = target ident

/-- A target store extends a source store with bindings classified by `Extra`.
Every source binding is preserved, and every target binding absent from the
source satisfies `Extra`. -/
@[expose] def StoreExtendsWith {P : PureExpr} (Extra : P.Ident → Prop)
    (source target : SemanticStore P) : Prop :=
  StoreAgreement source target ∧
  ∀ ident, (target ident).isSome = true →
    (source ident).isSome = true ∨ Extra ident

end -- public section

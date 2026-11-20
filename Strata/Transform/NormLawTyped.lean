/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics

/-! # Normalizations that keep values in typed stores

A rewrite of an expression may keep its value only where the expression has one: deciding the
equality `e == e` to `true` keeps the value of `e == e` in a store where `e` evaluates, and in no
other.  `StoreTypes F σ e` says that the store `σ` holds, for every annotated free-variable
occurrence `(x, ty)` of `e`, a value of `x` of type `ty`; `NormLawT F norm` says that `norm`
keeps the value of every expression in every well-formed store of the factory `F` that types the
expression's annotated occurrences in this way.

Key definitions: `StoreTypes`, `NormLawT`. -/

namespace Imperative

public section

variable {P : PureExpr} [HasVal P] [HasFvars P]

/-- The store `σ` holds, for every annotated free-variable occurrence `(x, ty)` of `e`, a value
    of `x` of type `ty` under the factory `F`. -/
@[expose] def StoreTypes (F : P.Factory) (σ : SemanticStore P) (e : P.Expr) : Prop :=
  ∀ x ty, (x, ty) ∈ HasFvars.getTypedFvars e → ∃ v, σ x = some v ∧ HasVal.valueOfTy F v ty

/-- The normalization `norm` keeps the value of every expression `e` (both have none, or the
    same one) in every well-formed store of the factory `F` that holds, at each annotated
    free-variable occurrence of `e`, a value of the annotated type (`StoreTypes`). -/
@[expose] def NormLawT (F : P.Factory) (norm : P.Expr → P.Expr) : Prop :=
  ∀ {σ : SemanticStore P} (e : P.Expr), WellFormedStore σ F → StoreTypes F σ e →
    P.eval F σ (norm e) = P.eval F σ e

/-- A store typing the annotated occurrences of `e` types those of every expression whose
    annotated occurrences are among them. -/
theorem StoreTypes.mono {F : P.Factory} {σ : SemanticStore P} {e e' : P.Expr}
    (h : StoreTypes F σ e)
    (hs : ∀ p, p ∈ HasFvars.getTypedFvars e' → p ∈ HasFvars.getTypedFvars e) :
    StoreTypes F σ e' :=
  fun x ty hx => h x ty (hs _ hx)

/-- A store typing the annotated occurrences of `e` keeps doing so once it grows: every value it
    holds is kept. -/
theorem StoreTypes.grow {F : P.Factory} {σ σ' : SemanticStore P} {e : P.Expr}
    (h : StoreTypes F σ e) (hg : ∀ x v, σ x = some v → σ' x = some v) :
    StoreTypes F σ' e :=
  fun x ty hx => (h x ty hx).elim fun v ⟨hv, ht⟩ => ⟨v, hg x v hv, ht⟩

/-- Normalizations that keep values in every well-formed store keep them in typed ones. -/
theorem NormLawT.of_forall {F : P.Factory} {norm : P.Expr → P.Expr}
    (h : ∀ {σ : SemanticStore P} (e : P.Expr), WellFormedStore σ F →
      P.eval F σ (norm e) = P.eval F σ e) :
    NormLawT F norm :=
  fun e hC _ => h e hC

end -- public section

end Imperative

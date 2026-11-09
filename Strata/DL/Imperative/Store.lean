/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Util.StringGen
public import Strata.Util.ListUtils

---------------------------------------------------------------------

namespace Imperative

/-! # Semantic stores

Core definitions and predicates for Imperative semantic stores. Store comparison
relations live in `StoreRelations`.
-/

public section

section

variable (P : PureExpr)

/-- A semantic store maps every identifier to an optional runtime value. -/
abbrev SemanticStore := P.Ident → Option P.Val

/-- A semantic store with no bindings. -/
@[expose] def emptyStore {P : PureExpr} : SemanticStore P := fun _ => none

end

/-! ## Defined and reserved variables -/

/-- Every `Q`-classified name not yet allocated by `state` is undefined in
`store`. -/
@[expose] def SemanticStore.isReserved {P : PureExpr} [HasIdent P]
    (Q : String → Prop) (state : StringGenState) (store : SemanticStore P) : Prop :=
  ∀ name, Q name → name ∉ state.stringGens →
    store (HasIdent.ident (P := P) name) = none

/-- Every `Q`-classified slot is undefined in `store`. For a list `vs` of
variables, use `Q := (· ∈ vs)`. -/
@[expose] def SemanticStore.varsUndefined {P : PureExpr}
    (Q : P.Ident → Prop) (store : SemanticStore P) : Prop :=
  ∀ ident, Q ident → store ident = none

/-- Every `Q`-classified slot is defined in `store`. For a list `vs` of
variables, use `Q := (· ∈ vs)`. -/
@[expose] def SemanticStore.varsDefined {P : PureExpr}
    (Q : P.Ident → Prop) (store : SemanticStore P) : Prop :=
  ∀ ident, Q ident → (store ident).isSome = true

/-- The store `σ'` binds only names of `D`. -/
@[expose] def SemanticStore.DomIn {P : PureExpr} (σ' : SemanticStore P) (D : List P.Ident) : Prop :=
  ∀ x, (σ' x).isSome → x ∈ D

/-- Define `ident := value`, leaving every other variable untouched. -/
@[expose] def SemanticStore.update {P : PureExpr} [DecidableEq P.Ident]
    (store : SemanticStore P) (ident : P.Ident) (value : P.Val) : SemanticStore P :=
  fun other => if other = ident then some value else store other

/-- Every variable selected from `value` by `getVars` is defined in `store`. -/
@[expose] def SemanticStore.isDefinedOver {P : PureExpr}
    (getVars : α → List P.Ident) (store : SemanticStore P) (value : α) : Prop :=
  SemanticStore.varsDefined (· ∈ getVars value) store

/-! ## Block scoping -/

/-- Project an inner store through a parent store: keep the inner value only
    for variables that were already defined in the parent. Variables that were
    not defined in the parent (i.e., init'd inside the block) become `none`. -/
@[expose] def projectStore {P : PureExpr} (σ_parent σ_inner : SemanticStore P) :
    SemanticStore P :=
  fun x => if (σ_parent x).isSome then σ_inner x else none

/-- Drop a set of names from a store, sending each to `none`. -/
@[expose] def dropVars {P : PureExpr} [DecidableEq P.Ident] (D : List P.Ident)
    (σ : SemanticStore P) : SemanticStore P :=
  fun x => if x ∈ D then none else σ x

/-! ## Store substitution -/

/-- The stores agree at every identifier pair in `substs`. -/
@[expose] def substStores {P : PureExpr}
    (source target : SemanticStore P) (substs : List (P.Ident × P.Ident)) : Prop :=
  ∀ sourceIdent targetIdent, (sourceIdent, targetIdent) ∈ substs →
    source sourceIdent = target targetIdent

/-- Both stores define every corresponding identifier pair in `substs`. -/
@[expose] def substDefined {P : PureExpr}
    (source target : SemanticStore P) (substs : List (P.Ident × P.Ident)) : Prop :=
  ∀ sourceIdent targetIdent, (sourceIdent, targetIdent) ∈ substs →
    (source sourceIdent).isSome = true ∧ (target targetIdent).isSome = true

/-- No identifier occurs twice across either side of `substs`. -/
@[expose] def substNodup {P : PureExpr}
    (substs : List (P.Ident × P.Ident)) : Prop :=
  (substs.unzip.1 ++ substs.unzip.2).Nodup

/-- Reverse every identifier pair in `substs`. -/
@[expose] def substSwap {P : PureExpr}
    (substs : List (P.Ident × P.Ident)) : List (P.Ident × P.Ident) :=
  substs.map Prod.swap

/-- The stores agree on every identifier in `vs`. -/
@[expose] def invStores {P : PureExpr}
    (source target : SemanticStore P) (vs : List P.Ident) : Prop :=
  substStores source target (vs.zip vs)

/-- The stores agree on every list disjoint from `vs`. -/
@[expose] def invStoresExcept {P : PureExpr}
    (source target : SemanticStore P) (vs : List P.Ident) : Prop :=
  ∀ other : List P.Ident, other.Disj vs → invStores source target other

end -- public section

end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterTypes
import all Strata.DL.Imperative.InterpreterTypes

/-! # Properties of the replay vocabulary types: typed stores

Lemmas about `StoreTyped` and `ReplayValueOps.TypedSound` of `InterpreterTypes.lean`. Key
theorems: `StoreTyped.update` and `StoreTyped.projectStore` (point updates with typed values
and scope projection keep a store typed), `evalCmdE_storeTyped` (`EvalCmdE` preserves typed
stores), and `ReplayValueOps.TypedSound.storedTy` (the reference `set` premise from the
executable `sameType` check). -/

namespace Imperative
public section

/-- A point update with a typed value keeps a store typed. -/
theorem StoreTyped.update [HasVal P] [DecidableEq P.Ident] {f : P.Factory}
    {σ : SemanticStore P} (h : StoreTyped f σ) (x : P.Ident) {v : P.Val} {ty : P.Ty}
    (hv : HasVal.valueOfTy f v ty) : StoreTyped f (SemanticStore.update σ x v) := by
  grind [StoreTyped, SemanticStore.update]

/-- On a typed store, a runtime value that passes the executable `isValue` and `sameType` checks
    against the runtime value `old` denoting the value stored in the target slot denotes a value
    satisfying the reference `set` rule's typed-value premise (`HasVal.valueOfStoredTy`), when
    the checks are sound (`TypedSound`). -/
theorem ReplayValueOps.TypedSound.storedTy [HasVal P] {RF : Type} {ops : ReplayValueOps P RF}
    {rf : P.Factory → RF} {den : P.Factory → P.Expr → Option P.Val}
    (hops : ops.TypedSound rf den) {f : P.Factory} {σ : SemanticStore P} (hσ : StoreTyped f σ)
    {x : P.Ident} {old r : P.Expr} {vo : P.Val} (hold : σ x = some vo) (hdo : den f old = some vo)
    (hv : ops.isValue (rf f) r = true) (hs : ops.sameType (rf f) old r = true) :
    ∃ v, den f r = some v ∧ HasVal.valueOfStoredTy (P := P) f σ x v := by
  obtain ⟨ty, hty⟩ := hσ x vo hold
  obtain ⟨v, hd, hvt⟩ := hops.sameType f old r vo ty hdo hty hv hs
  exact ⟨v, hd, vo, ty, hold, hty, hvt⟩

end
end Imperative

namespace Imperative
public section
variable {P : PureExpr}

/-- A projected store is typed when both the parent and the inner store are. -/
theorem StoreTyped.projectStore [HasVal P] {f : P.Factory} {σp σ : SemanticStore P}
    (h : StoreTyped f σ) : StoreTyped f (projectStore σp σ) := by grind [StoreTyped, projectStore]

/-- A reference command evaluation (`EvalCmdE`) keeps a typed store typed: every value it
    writes carries a type premise (the typed `init`/`set` rules). -/
theorem evalCmdE_storeTyped [HasFvar P] [HasBool P] [HasBoolOps P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {evs : List (Event P)}
    (hev : EvalCmdE (P := P) f σ c σ' evs) (h : StoreTyped f σ) : StoreTyped f σ' := by
  cases hev <;> rename_i h <;> cases h <;> grind [StoreTyped, HasVal.valueOfStoredTy]

end
end Imperative

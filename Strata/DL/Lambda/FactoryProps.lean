/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Factory

/-!
## Properties of `Lambda.Factory`

Theorems about `Factory.callOfLFunc`, `getLFuncCall`, and related definitions.

Note: several theorems currently live in `Strata.DL.Lambda.Factory` itself
(e.g. `callOfLFunc_eq_some`, `callOfLFunc_getLFuncCall`, `callOfLFunc_smaller`).
They will be migrated here in a future cleanup.
-/

namespace Lambda

/-- `callOfLFunc` returns `none` for free-variable expressions. -/
theorem callOfLFunc_fvar_none {Tbase : LExprParams} {GenericTy} (F : @Factory Tbase)
    (m : Tbase.Metadata) (v : Tbase.Identifier) (ty : Option GenericTy) :
    Factory.callOfLFunc F (.fvar m v ty : LExpr ⟨Tbase, GenericTy⟩) = none := by
  cases h : Factory.callOfLFunc F (.fvar m v ty : LExpr ⟨Tbase, GenericTy⟩) with
  | none => rfl
  | some val =>
    obtain ⟨callee, args, fn⟩ := val
    have hgl := callOfLFunc_getLFuncCall h
    have hfvar : getLFuncCall (.fvar m v ty : LExpr ⟨Tbase, GenericTy⟩) = (.fvar m v ty, []) := by
      unfold getLFuncCall getLFuncCall.go; rfl
    rw [hfvar] at hgl
    have ⟨_, _, _, hop, _, _⟩ := callOfLFunc_eq_some h
    rw [← (Prod.mk.inj hgl).1] at hop
    exact absurd hop (by simp)

end Lambda

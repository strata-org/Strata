/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.AggregateTypesFactory
import all Strata.Languages.Core.AggregateTypesFactory
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprProps

/-! # Properties of Core's factory functions over aggregate types

Properties of the chain `AggregateLitEval.selectChain` that `select` returns on a map literal at a
key sort that is not canonical: an induction principle over its nodes
(`AggregateLitEval.selectChain_ind`), it has no operators (`AggregateLitEval.selectChain_getOps`),
and it has the type naming the value sort (`AggregateLitEval.selectChain_hasType`).
-/

namespace Core
open Lambda

public section

namespace AggregateLitEval

/-- A property of expressions that holds of every constant, every equality and every `ite` of
    expressions that have it holds of every `selectChain`. -/
theorem selectChain_ind (P : Expression.Expr → Prop) (hc : ∀ m c, P (.const m c))
    (heq : ∀ m a b, P a → P b → P (.eq m a b))
    (hite : ∀ m c t e, P c → P t → P e → P (.ite m c t e)) (md : CoreExprMetadata)
    (key d : LConst) : ∀ es, P (selectChain md key d es)
  | [] => hc _ _
  | (k, v) :: rest => by
    simp only [selectChain]
    split
    · exact hc _ _
    · exact hite _ _ _ _ (heq _ _ _ (hc _ _) (hc _ _)) (hc _ _) (selectChain_ind P hc heq hite md key d rest)

/-- `selectChain` has no operators. -/
theorem selectChain_getOps (md : CoreExprMetadata) (key d : LConst) :
    ∀ es, LExpr.getOps (selectChain md key d es) = []
  | [] => rfl
  | (k, v) :: rest => by
    simp only [selectChain]
    split
    · rfl
    · simp [LExpr.getOps, selectChain_getOps md key d rest]

/-- The `selectChain` of a well-typed key of the key sort and a well-typed map literal has the
    type naming the value sort. -/
theorem selectChain_hasType (md : CoreExprMetadata) {key d : LConst} {k v : LSort}
    (hkw : key.wt = true) (hks : key.sort = k) :
    ∀ {es : List (LConst × LConst)}, (LConst.mapConst k v d ⟨es⟩).wt = true →
      LExpr.HasTypeA [] (selectChain md key d es) v.toMonoTy
  | [], hw => by
    simp only [LConst.wt, LConst.wtEntries, Bool.and_eq_true, decide_eq_true_eq] at hw
    have : d.ty = v.toMonoTy := by rw [LConst.ty_of_wt hw.1.1, hw.1.2]
    exact this ▸ .const hw.1.1
  | (k', v') :: rest, hw => by
    simp only [LConst.wt, LConst.wtEntries, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨hd, hds⟩, ⟨⟨⟨⟨hk', hk's⟩, hv'⟩, hv's⟩, hr⟩⟩ := hw
    have hrw : (LConst.mapConst k v d ⟨rest⟩).wt = true := by
      simp [LConst.wt, hd, hds, hr]
    have hv : v'.ty = v.toMonoTy := by rw [LConst.ty_of_wt hv', hv's]
    have hk : key.ty = k.toMonoTy := by rw [LConst.ty_of_wt hkw, hks]
    have hk'' : k'.ty = k.toMonoTy := by rw [LConst.ty_of_wt hk', hk's]
    simp only [selectChain]
    split
    · exact hv ▸ .const hv'
    · have h₁ : LExpr.HasTypeA (T := CoreLParams) [] (.const md key) k.toMonoTy :=
        hk ▸ .const hkw
      have h₂ : LExpr.HasTypeA (T := CoreLParams) [] (.const md k') k.toMonoTy :=
        hk'' ▸ .const hk'
      exact .ite (.eq h₁ h₂) (hv ▸ .const hv') (selectChain_hasType md hkw hks hrw)

end AggregateLitEval

end -- public section
end Core

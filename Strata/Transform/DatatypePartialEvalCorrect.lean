/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DatatypePartialEval
public import Strata.DL.Lambda.LExpr

/-! # Datatype Partial Evaluation Correctness -/

namespace Strata

open Lambda

/-- Two expressions are equivalent under the datatype axioms. -/
inductive DtEquiv (dtInfo : DatatypeInfo) :
    LExpr Core.CoreLParams.mono → LExpr Core.CoreLParams.mono → Prop where
  | refl (e) : DtEquiv dtInfo e e
  | symm {e₁ e₂} : DtEquiv dtInfo e₁ e₂ → DtEquiv dtInfo e₂ e₁
  | trans {e₁ e₂ e₃} : DtEquiv dtInfo e₁ e₂ → DtEquiv dtInfo e₂ e₃ → DtEquiv dtInfo e₁ e₃
  | app_congr {f₁ f₂ a₁ a₂} (m : Core.ExpressionMetadata) :
    DtEquiv dtInfo f₁ f₂ → DtEquiv dtInfo a₁ a₂ →
    DtEquiv dtInfo (.app m f₁ a₁) (.app m f₂ a₂)
  | ite_congr {c₁ c₂ t₁ t₂ e₁ e₂} (m : Core.ExpressionMetadata) :
    DtEquiv dtInfo c₁ c₂ → DtEquiv dtInfo t₁ t₂ → DtEquiv dtInfo e₁ e₂ →
    DtEquiv dtInfo (.ite m c₁ t₁ e₁) (.ite m c₂ t₂ e₂)
  | quant_congr {tr₁ tr₂ b₁ b₂} (m : Core.ExpressionMetadata) k name ty :
    DtEquiv dtInfo tr₁ tr₂ → DtEquiv dtInfo b₁ b₂ →
    DtEquiv dtInfo (.quant m k name ty tr₁ b₁) (.quant m k name ty tr₂ b₂)
  /-- Tester on matching constructor -/
  | tester_pos (testerName : String) (e : LExpr Core.CoreLParams.mono)
    (constrName : String) (args : List (LExpr Core.CoreLParams.mono))
    (appMd opMd : Core.ExpressionMetadata) (opTy : Option Core.CoreLParams.mono.TypeType) :
    dtInfo.testerToConstr.get? testerName = some constrName →
    matchConstrApp dtInfo e = some (constrName, args) →
    DtEquiv dtInfo (.app appMd (.op opMd ⟨testerName, ()⟩ opTy) e) (.const default (.boolConst true))
  /-- Tester on non-matching constructor -/
  | tester_neg (testerName : String) (e : LExpr Core.CoreLParams.mono)
    (constrName actualConstr : String) (args : List (LExpr Core.CoreLParams.mono))
    (appMd opMd : Core.ExpressionMetadata) (opTy : Option Core.CoreLParams.mono.TypeType) :
    dtInfo.testerToConstr.get? testerName = some constrName →
    matchConstrApp dtInfo e = some (actualConstr, args) →
    actualConstr ≠ constrName →
    DtEquiv dtInfo (.app appMd (.op opMd ⟨testerName, ()⟩ opTy) e) (.const default (.boolConst false))
  /-- Selector on matching constructor -/
  | selector_proj (selName : String) (e : LExpr Core.CoreLParams.mono)
    (constrName : String) (fieldIdx : Nat) (args : List (LExpr Core.CoreLParams.mono))
    (fieldVal : LExpr Core.CoreLParams.mono)
    (appMd opMd : Core.ExpressionMetadata) (opTy : Option Core.CoreLParams.mono.TypeType) :
    dtInfo.selectorInfo.get? selName = some (constrName, fieldIdx) →
    matchConstrApp dtInfo e = some (constrName, args) →
    args[fieldIdx]? = some fieldVal →
    DtEquiv dtInfo (.app appMd (.op opMd ⟨selName, ()⟩ opTy) e) fieldVal

/-! ## Leaf preservation -/

theorem partialEvalDatatypesCore_const
    (dtInfo : DatatypeInfo) (m : Core.ExpressionMetadata) (c : Lambda.LConst) :
    partialEvalDatatypesCore dtInfo (.const m c) = .const m c := by
  simp [partialEvalDatatypesCore]

theorem partialEvalDatatypesCore_op
    (dtInfo : DatatypeInfo) (m : Core.ExpressionMetadata)
    (id : Identifier Core.CoreLParams.mono.base.IDMeta)
    (ty : Option Core.CoreLParams.mono.TypeType) :
    partialEvalDatatypesCore dtInfo (.op m id ty) = .op m id ty := by
  simp [partialEvalDatatypesCore]

theorem partialEvalDatatypesCore_fvar
    (dtInfo : DatatypeInfo) (m : Core.ExpressionMetadata) (x : Core.CoreLParams.mono.base.IDMeta) (n : Nat) :
    partialEvalDatatypesCore dtInfo (.fvar m x n) = .fvar m x n := by
  simp [partialEvalDatatypesCore]

theorem partialEvalDatatypesCore_bvar
    (dtInfo : DatatypeInfo) (m : Core.ExpressionMetadata) (n : Nat) :
    partialEvalDatatypesCore dtInfo (.bvar m n) = .bvar m n := by
  simp [partialEvalDatatypesCore]

/-! ## Main theorem -/

theorem partialEvalDatatypesCore_correct
    (dtInfo : DatatypeInfo)
    (e : LExpr Core.CoreLParams.mono) :
    DtEquiv dtInfo (partialEvalDatatypesCore dtInfo e) e := by
  induction e with
  | const _ _ => simp [partialEvalDatatypesCore]; exact .refl _
  | op _ _ _ => simp [partialEvalDatatypesCore]; exact .refl _
  | fvar _ _ _ => simp [partialEvalDatatypesCore]; exact .refl _
  | bvar _ _ => simp [partialEvalDatatypesCore]; exact .refl _
  | ite m c t e ihc iht ihe =>
    simp only [partialEvalDatatypesCore]
    exact .symm (.ite_congr m (.symm ihc) (.symm iht) (.symm ihe))
  | quant m k name ty trigger body iht ihb =>
    simp only [partialEvalDatatypesCore]
    exact .symm (.quant_congr m k name ty (.symm iht) (.symm ihb))
  | app m f a ihf iha =>
    -- Case split on f to match partialEvalDatatypesCore's pattern matching
    match hf : f with
    | .op opMd fn opTy =>
      -- Unary app: tester/selector case
      simp only [partialEvalDatatypesCore]
      -- Case split on tester lookup + matchConstrApp
      match ht : dtInfo.testerToConstr.get? fn.1, hmc : matchConstrApp dtInfo (partialEvalDatatypesCore dtInfo a) with
      | some expectedConstr, some (actualConstr, cargs) =>
        simp [ht, hmc]
        by_cases heq : actualConstr == expectedConstr
        · -- Tester matches → true
          simp [heq]
          have heq' : actualConstr = expectedConstr := by
            cases actualConstr; cases expectedConstr; simp_all [BEq.beq, decide_eq_true_eq] at heq ⊢
          subst heq'
          -- Apply tester_pos axiom to the SIMPLIFIED arg'
          have hax : DtEquiv dtInfo (.app m (.op opMd ⟨fn.1, ()⟩ opTy) (partialEvalDatatypesCore dtInfo a)) (.const default (.boolConst true)) :=
            .tester_pos fn.1 (partialEvalDatatypesCore dtInfo a) expectedConstr cargs m opMd opTy ht hmc
          -- Relate app(tester, arg') to app(tester, arg) by congruence
          have hcong : DtEquiv dtInfo (.app m (.op opMd ⟨fn.1, ()⟩ opTy) (partialEvalDatatypesCore dtInfo a)) (.app m (.op opMd fn opTy) a) :=
            .app_congr m (.refl _) iha
          exact .symm (.trans hcong (.symm hax))
        · -- Tester doesn't match → false
          simp [heq]
          have hneq : actualConstr ≠ expectedConstr := by
            intro h; simp [h, BEq.beq, decide_eq_true_eq] at heq
          have hax : DtEquiv dtInfo (.app m (.op opMd ⟨fn.1, ()⟩ opTy) (partialEvalDatatypesCore dtInfo a)) (.const default (.boolConst false)) :=
            .tester_neg fn.1 (partialEvalDatatypesCore dtInfo a) expectedConstr actualConstr cargs m opMd opTy ht hmc hneq
          have hcong : DtEquiv dtInfo (.app m (.op opMd ⟨fn.1, ()⟩ opTy) (partialEvalDatatypesCore dtInfo a)) (.app m (.op opMd fn opTy) a) :=
            .app_congr m (.refl _) iha
          exact .symm (.trans hcong (.symm hax))
      | _, _ =>
        -- No tester match, check selector
        simp [ht, hmc]
        match hs : dtInfo.selectorInfo.get? fn.1, hmc2 : matchConstrApp dtInfo (partialEvalDatatypesCore dtInfo a) with
        | some (expectedConstr, fieldIdx), some (actualConstr2, cargs2) =>
          simp [hs, hmc2]
          by_cases heq2 : actualConstr2 == expectedConstr
          · simp [heq2]
            match hfi : cargs2[fieldIdx]? with
            | some fieldVal =>
              simp [hfi]
              -- Selector matches → extract field from simplified arg'
              have hax : DtEquiv dtInfo (.app m (.op opMd ⟨fn.1, ()⟩ opTy) (partialEvalDatatypesCore dtInfo a)) fieldVal :=
                .selector_proj fn.1 (partialEvalDatatypesCore dtInfo a) expectedConstr fieldIdx cargs2 fieldVal m opMd opTy hs (by rw [hmc2]; congr 1; cases actualConstr2; cases expectedConstr; simp_all [BEq.beq, decide_eq_true_eq]) hfi
              have hcong : DtEquiv dtInfo (.app m (.op opMd ⟨fn.1, ()⟩ opTy) (partialEvalDatatypesCore dtInfo a)) (.app m (.op opMd fn opTy) a) :=
                .app_congr m (.refl _) iha
              exact .symm (.trans hcong (.symm hax))
            | none =>
              simp [hfi]
              exact .symm (.app_congr m (.refl _) (.symm iha))
          · simp [heq2]
            exact .symm (.app_congr m (.refl _) (.symm iha))
        | _, _ =>
          simp [hs, hmc2]
          exact .symm (.app_congr m (.refl _) (.symm iha))
    | .app m2 op l =>
      -- Binary app: recurse on both sides, no eq simplification
      -- (The eq(C(a),C(b))→true rewrite was unsound; removed.)
      simp only [partialEvalDatatypesCore]
      exact .symm (.app_congr m (.symm ihf) (.symm iha))
    | _ =>
      -- General app: just recurse
      simp only [partialEvalDatatypesCore]
      exact .symm (.app_congr m (.symm ihf) (.symm iha))

theorem partialEvalDatatypes_correct
    (dtInfo : DatatypeInfo)
    (e : LExpr Core.CoreLParams.mono) :
    DtEquiv dtInfo (partialEvalDatatypes dtInfo e) e := by
  unfold partialEvalDatatypes
  exact partialEvalDatatypesCore_correct dtInfo e

end Strata

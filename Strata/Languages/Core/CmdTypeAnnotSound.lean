/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.CmdTypeSpec
import Strata.Languages.Core.CmdType
import all Strata.Languages.Core.CmdTypeSound
import Strata.DL.Imperative.CmdType
import Strata.DL.Lambda.Denote.ResolveHasTypeAStub
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst

/-! ## Annotated Soundness of Command Typechecker

Proves that if the executable command typechecker succeeds, then the output
command satisfies the declarative `CmdHasTypeA` relation (annotated, monomorphic).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

private theorem replaceUserProvidedType_getVars (e : LExpr T) (f : T.TypeType → T.TypeType) :
    LExpr.getVars (LExpr.replaceUserProvidedType e f) = LExpr.getVars e := by
  induction e with
  | const | bvar | op => simp [LExpr.replaceUserProvidedType, LExpr.getVars]
  | fvar => simp [LExpr.replaceUserProvidedType, LExpr.getVars]
  | app _ _ _ ih1 ih2 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2]
  | abs _ _ _ _ ih => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih]
  | quant _ _ _ _ _ _ ih1 ih2 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2]

private theorem applySubst_getVars_eq (e : LExpr CoreLParams.mono) (S : Subst) :
    LExpr.getVars (e.applySubst S) = LExpr.getVars e := by
  rw [LExpr.applySubst_eq_replaceUserProvidedType]
  exact replaceUserProvidedType_getVars e _

private theorem eqModuloAnnotations_getVars
    {e₁ : LExpr ⟨⟨M₁, IDMeta⟩, Ty₁⟩} {e₂ : LExpr ⟨⟨M₂, IDMeta⟩, Ty₂⟩}
    (h : EqModuloAnnotations e₁ e₂) :
    LExpr.getVars e₁ = LExpr.getVars e₂ := by
  induction e₁ generalizing e₂ <;>
  cases e₂ <;> simp [EqModuloAnnotations, LExpr.getVars] at h ⊢ <;>
  grind


/-- Apply a type substitution to all expressions in a command. -/
def Cmd.applySubst (c : Cmd Expression) (S : Subst) : Cmd Expression :=
  match c with
  | .init x xty (.det e) md => .init x xty (.det (e.applySubst S)) md
  | .init x xty .nondet md => .init x xty .nondet md
  | .set x (.det e) md => .set x (.det (e.applySubst S)) md
  | .set x .nondet md => .set x .nondet md
  | .assert l e md => .assert l (e.applySubst S) md
  | .assume l e md => .assume l (e.applySubst S) md
  | .cover l e md => .cover l (e.applySubst S) md

/-- `inferType` produces an expression satisfying `HasTypeA`. -/
theorem CmdType.inferType_HasTypeA (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∃ mty, ety = .forAll [] mty ∧ LExpr.HasTypeA [] e' mty := by
  obtain ⟨ea, h_resolve, h_e'_eq, h_ety⟩ := CmdType.inferType_decompose C Env c e e' ety Env' h
  subst h_e'_eq
  exact ⟨ea.toLMonoTy, h_ety, resolve_HasTypeA e ea C Env Env' h_resolve h_wf h_fwf h_resolved⟩

/--
Common proof for assert/assume/cover: if `inferType` succeeds and the result
is bool-typed, then `HasTypeA` holds for the substituted expression at type bool,
and the context is preserved.
-/
private theorem inferType_bool_HasTypeA (C : LContext CoreLParams) (Env Env_out : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h_infer : CmdType.inferType C Env c e = .ok (e', ety, Env_out))
    (h_isbool : CmdType.isBoolType ety = true)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] (e'.applySubst Env_out.stateSubstInfo.subst) .bool ∧
    Env_out.context = Env.context := by
  obtain ⟨mty, h_ety, h_hta⟩ := CmdType.inferType_HasTypeA C Env Env_out c e e' ety
    h_infer h_wf h_fwf h_resolved
  have h_bool_mty : mty = .bool := by
    have := CmdType.isBoolType_eq _ h_isbool
    rw [h_ety] at this; cases this; rfl
  subst h_bool_mty
  have h_ctx := CmdType.inferType_preserves_context C Env Env_out c e e' ety h_infer h_wf h_ne h_fwf
  have h_hta_subst := applySubst_typeCheck Env_out.stateSubstInfo.subst h_hta
  simp [LMonoTy.subst_bool] at h_hta_subst
  exact ⟨h_hta_subst, h_ctx⟩

/--
Annotated soundness of the command typechecker: if `Cmd.typeCheck` succeeds,
the output command satisfies `CmdHasTypeA` between the substituted contexts.

The substitution is needed because variable types in `Env.context` may contain
unresolved type variables. After applying the final substitution, the context
types become ground and match the expression types from `resolve` (which already
applies the substitution internally).
-/
theorem Cmd.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context) :
    CmdHasTypeA C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (TypeSpec.Cmd.applySubst cmd' Env'.stateSubstInfo.subst)
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · -- x fresh
      rename_i h_lookup_none
      split at h
      · -- det case
        rename_i expr heq_det
        split at h
        · contradiction
        · rename_i h_not_in_fv
          split at h
          · contradiction
          · rename_i v1 h_preprocess
            split at h
            · contradiction
            · rename_i v2 h_infer
              split at h
              · contradiction
              · rename_i Env_unified h_unify
                split at h
                · contradiction
                · rename_i v3 h_postprocess
                  cases h
                  simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
                    TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
                    TypeContext.freeVars] at *
                  have h_find_none := (CmdType.lookup_none_iff_find_none Env x).mp h_lookup_none
                  obtain ⟨h_ctx_eq, h_wf_pre, mty_pre, h_mty_pre, mty, h_mty, h_mty_eq, h_v3_eq⟩ :=
                    init_det_context_setup C Env x xty heq_det md v1 v2 Env_unified v3
                      h_preprocess h_infer h_unify h_postprocess h_wf h_fwf h_ne
                  have h_fresh_v3 : v3.snd.context.types.find? x = none :=
                    h_ctx_eq ▸ h_find_none
                  have h_update_ctx := CmdType.update_subst_context v3.snd x v3.fst
                    (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst h_fresh_v3
                  rw [h_update_ctx, h_ctx_eq, h_mty]
                  have h_ctx_pre := CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess
                  have h_resolved_pre : TContext.AliasesResolved v1.snd.context :=
                    h_ctx_pre ▸ h_resolved
                  obtain ⟨mty_infer, h_ety_eq, h_hta⟩ := CmdType.inferType_HasTypeA C v1.snd v2.2.snd
                    (Cmd.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst
                    h_infer h_wf_pre h_fwf h_resolved_pre
                  have h_subst_eq : (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst =
                      Env_unified.stateSubstInfo.subst := by
                    rw [CmdType.update_preserves_subst, h_v3_eq]
                  have h_hta_subst := applySubst_typeCheck
                    (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst h_hta
                  simp at h_hta_subst
                  have h_unify_eq : LMonoTy.subst
                      (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst mty_infer = mty := by
                    rw [h_subst_eq, h_mty_eq]
                    rw [h_mty_pre, h_ety_eq] at h_unify
                    exact (CmdType.unifyTypes_eq v2.2.snd Env_unified mty_pre mty_infer h_unify).symm
                  rw [h_unify_eq] at h_hta_subst
                  have h_not_in_vars : x ∉ HasVarsPure.getVars (P := Expression) heq_det :=
                    fun hv => h_not_in_fv ((CmdType.freeVars_eq_getVars heq_det x).mpr hv)
                  have h_resolve_eq := CmdType.inferType_decompose C v1.snd
                    (Cmd.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst v2.2.snd h_infer
                  obtain ⟨ea, h_resolve, h_v2_eq, _⟩ := h_resolve_eq
                  have h_eqmod := resolve_eqModuloAnnotations heq_det ea C v1.snd v2.2.snd h_resolve
                  have h_vars_eq : LExpr.getVars v2.1 = LExpr.getVars heq_det := by
                    rw [h_v2_eq]
                    exact eqModuloAnnotations_getVars h_eqmod
                  have h_not_in_v2 : x ∉ HasVarsPure.getVars (P := Expression)
                      (v2.1.applySubst (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst) := by
                    simp only [HasVarsPure.getVars, Imperative.HasVarsPure.getVars]
                    rw [applySubst_getVars_eq]
                    simp only [HasVarsPure.getVars, Imperative.HasVarsPure.getVars] at h_not_in_vars
                    rw [h_vars_eq]
                    exact h_not_in_vars
                  simp only [Cmd.applySubst]
                  have h_find_none_subst := Lambda.TContext.subst_find_none Env.context
                    (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst x h_find_none
                  exact CmdHasType'.init_det _ x v3.fst _ _ md
                    h_find_none_subst h_not_in_v2 h_hta_subst
      · -- nondet case
        rename_i heq_nondet
        split at h
        · contradiction
        · rename_i v1 h_preprocess
          split at h
          · contradiction
          · rename_i v2 h_postprocess
            cases h
            simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
              TypeContext.postprocess] at *
            have h_find_none := (CmdType.lookup_none_iff_find_none Env x).mp h_lookup_none
            obtain ⟨h_ctx_eq, h_find_none_subst, mty, h_mty⟩ :=
              init_nondet_context_setup C Env x xty v1 v2 h_preprocess h_postprocess h_find_none
            have h_fresh_v2 : v2.snd.context.types.find? x = none :=
              h_ctx_eq ▸ h_find_none
            have h_update_ctx := CmdType.update_subst_context v2.snd x v2.fst
              (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst h_fresh_v2
            rw [h_update_ctx, h_ctx_eq, h_mty]
            simp only [Cmd.applySubst]
            exact CmdHasType'.init_nondet _ x v2.fst mty md h_find_none_subst
    · contradiction
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i xty h_lookup
      cases e with
      | det expr =>
        simp only [] at h
        split at h
        · contradiction
        · rename_i v heq
          split at h
          · contradiction
          · rename_i Env_unified h_unify
            cases h
            obtain ⟨e', ety, Env_infer⟩ := v
            simp at heq h_unify ⊢
            have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
            have h_xty_bv := h_mono x xty h_find
            obtain ⟨xs, mty_x⟩ := xty
            simp [LTy.boundVars] at h_xty_bv
            subst h_xty_bv
            have h_find_subst := Lambda.TContext.subst_find_some Env.context
              Env'.stateSubstInfo.subst x (.forAll [] mty_x) h_find
            rw [LTy.subst_forAll_nil] at h_find_subst
            obtain ⟨mty_infer, h_ety_eq, h_hta⟩ := CmdType.inferType_HasTypeA C Env _
              (.set x (.det expr) md) expr _ _ heq h_wf h_fwf h_resolved
            have h_ctx_infer := CmdType.inferType_preserves_context C Env Env_infer
              (.set x (.det expr) md) expr e' ety heq h_wf h_ne h_fwf
            have h_ctx_unify := CmdType.unifyTypes_preserves_context Env_infer Env'
              [(.forAll [] mty_x, ety)] h_unify
            have h_ctx : Env'.context = Env.context := by rw [h_ctx_unify, h_ctx_infer]
            rw [h_ctx]
            have h_unify_eq : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
                LMonoTy.subst Env'.stateSubstInfo.subst mty_x := by
              rw [h_ety_eq] at h_unify
              exact (CmdType.unifyTypes_eq Env_infer Env' mty_x mty_infer h_unify).symm
            have h_hta_subst := applySubst_typeCheck Env'.stateSubstInfo.subst h_hta
            simp at h_hta_subst
            rw [h_unify_eq] at h_hta_subst
            simp only [Cmd.applySubst]
            exact CmdHasType'.set_det _ x (LMonoTy.subst Env'.stateSubstInfo.subst mty_x) _ md
              h_find_subst h_hta_subst
      | nondet =>
        simp at h
        cases h
        obtain ⟨mty, h_find_subst⟩ := set_nondet_sound Env x xty h_lookup h_mono
        exact CmdHasType'.set_nondet _ x mty md h_find_subst
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i v heq
      split at h
      · rename_i h_bool
        cases h
        obtain ⟨e', ety, Env_out⟩ := v
        simp at heq
        obtain ⟨h_hta, h_ctx⟩ := inferType_bool_HasTypeA C Env Env_out
          (.assert label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_resolved
        rw [h_ctx]
        exact CmdHasType'.assert _ label _ md h_hta
      · contradiction
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i v heq
      split at h
      · rename_i h_bool
        cases h
        obtain ⟨e', ety, Env_out⟩ := v
        simp at heq
        obtain ⟨h_hta, h_ctx⟩ := inferType_bool_HasTypeA C Env Env_out
          (.assume label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_resolved
        rw [h_ctx]
        exact CmdHasType'.assume _ label _ md h_hta
      · contradiction
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i v heq
      split at h
      · rename_i h_bool
        cases h
        obtain ⟨e', ety, Env_out⟩ := v
        simp at heq
        obtain ⟨h_hta, h_ctx⟩ := inferType_bool_HasTypeA C Env Env_out
          (.cover label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_resolved
        rw [h_ctx]
        exact CmdHasType'.cover _ label _ md h_hta
      · contradiction

end TypeSpec
end Core

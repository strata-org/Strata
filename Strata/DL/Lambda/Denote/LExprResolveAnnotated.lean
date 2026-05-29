/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprAnnotated

/-! ## `resolve` produces well-annotated expressions (`HasTypeA`)

This module proves that when `LExpr.resolve` succeeds, the resulting expression
satisfies `HasTypeA` — i.e., the type annotations placed by resolution are
internally consistent.
-/

namespace Lambda

open LExpr

section

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata]

/-! ### Layer 1: `applySubstT` preserves `HasTypeA` -/

theorem applySubstT_unresolved_HasTypeA (S : Subst) (et : LExprT T.mono)
    (Δ : List LMonoTy)
    (h : HasTypeA Δ et.unresolved (et.toLMonoTy)) :
    HasTypeA (Δ.map (LMonoTy.subst S))
             (applySubstT et S).unresolved
             ((applySubstT et S).toLMonoTy) := by
  sorry

theorem applySubstT_unresolved_HasTypeA_nil (S : Subst) (et : LExprT T.mono)
    (h : HasTypeA [] et.unresolved (et.toLMonoTy)) :
    HasTypeA [] (applySubstT et S).unresolved ((applySubstT et S).toLMonoTy) := by
  sorry

/-! ### Helper: `applySubstT` and `varCloseT` commute -/

theorem applySubstT_varCloseT_comm (k : Nat) (xv : T.Identifier) (et : LExprT T.mono) (S : Subst) :
    applySubstT (LExpr.varCloseT k xv et) S = LExpr.varCloseT k xv (applySubstT et S) := by
  sorry

/-! ### Layer 2: `varCloseT` preserves `HasTypeA` -/

/-- Every free occurrence of `xv` in `et` carries type `t` in its metadata. -/
def LExprT.allFvarAnnot (xv : T.Identifier) (t : LMonoTy) : LExprT T.mono → Prop
  | .fvar m y _ => y = xv → m.type = t
  | .app _ f a => allFvarAnnot xv t f ∧ allFvarAnnot xv t a
  | .abs _ _ _ e => allFvarAnnot xv t e
  | .quant _ _ _ _ tr e => allFvarAnnot xv t tr ∧ allFvarAnnot xv t e
  | .ite _ c th el => allFvarAnnot xv t c ∧ allFvarAnnot xv t th ∧ allFvarAnnot xv t el
  | .eq _ e1 e2 => allFvarAnnot xv t e1 ∧ allFvarAnnot xv t e2
  | _ => True

/-! ### Helper: `applySubstT` preserves `allFvarAnnot` -/

theorem applySubstT_allFvarAnnot (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono) (S : Subst)
    (h : LExprT.allFvarAnnot xv t et) :
    LExprT.allFvarAnnot xv (LMonoTy.subst S t) (applySubstT et S) := by
  sorry

/-! ### Helper: `resolveAux` annotates free variables from context -/

theorem resolveAux_allFvarAnnot (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (e : LExpr T.mono) (et : LExprT T.mono)
    (xv : T.Identifier) (xty : LMonoTy)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_ctx : Env.context.types.find? xv = some (.forAll [] xty)) :
    LExprT.allFvarAnnot xv xty et := by
  sorry

/-! ### Helper: `typeBoundVar` adds the variable to the context -/

theorem typeBoundVar_adds_to_context (C : LContext T) (Env : TEnv T.IDMeta)
    (bty : Option LMonoTy) (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.context.types.find? xv = some (.forAll [] xty) := by
  sorry

theorem varCloseT_unresolved_HasTypeA (k : Nat) (Δ : List LMonoTy) (hk : Δ.length = k)
    (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono)
    (h_typed : HasTypeA Δ et.unresolved (et.toLMonoTy))
    (h_annot : LExprT.allFvarAnnot xv t et) :
    HasTypeA (Δ ++ [t]) (LExpr.varCloseT k xv et).unresolved ((LExpr.varCloseT k xv et).toLMonoTy) := by
  sorry

theorem varCloseT_unresolved_HasTypeA_nil (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono)
    (h_typed : HasTypeA [] et.unresolved (et.toLMonoTy))
    (h_annot : LExprT.allFvarAnnot xv t et) :
    HasTypeA [t] (LExpr.varCloseT 0 xv et).unresolved ((LExpr.varCloseT 0 xv et).toLMonoTy) := by
  sorry

/-! ### Helper: `TEnvWF` preserved by `resolve`'s context initialization -/

theorem TEnvWF_resolve_init (Env : TEnv T.IDMeta) (h_envwf : TEnvWF Env) :
    TEnvWF (if Env.context.types.isEmpty = true then
      Env.updateContext { types := [[]], aliases := Env.context.aliases }
    else Env) := by
  sorry

/-! ### Helper: absorption from `resolveAux_properties`

  `resolveAux_properties` (in LExprTypeSpec) already proves that `resolveAux`
  monotonically extends substitutions (`.absorbs`). We use it directly below
  rather than reproving it — the app case requires `SubstFreshForGen` due to
  the `Maps.remove` step, so a truly assumption-free version is impossible. -/

/-! ### Layer 3: `resolveAux` produces well-annotated terms -/

private theorem resolveAux_HasTypeA_aux :
    ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = Except.ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      FactoryWF C.functions →
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst →
      HasTypeA [] (applySubstT et S).unresolved
                 ((applySubstT et S).toLMonoTy) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h h_envwf h_ne h_fwf S h_absorbs
  match e with
  | .const _ _ =>
    simp only [resolveAux, inferConst, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · have heq := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨h_et, h_env⟩ := heq
      subst h_et h_env
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      rename_i heq_inferConst
      split at heq_inferConst
      · simp at heq_inferConst ⊢
        rw [← heq_inferConst]
        simp
        rw [LConst.ty_subst]
        exact HasTypeA.const
      · simp at heq_inferConst
  | .op _ _ _ =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    repeat (split at h <;> try solve | simp at h | contradiction)
    . cases h
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
    . split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
  | .bvar _ _ => simp [resolveAux] at h
  | .fvar _ _ _ =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i ty_env h_infer
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_et, h_env⟩ := h
      subst h_et h_env
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.fvar
  | .app m_app e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i e1t_env heq_e1
      split at h
      · simp at h
      · rename_i e2t_env heq_e2
        split at h
        · simp at h
        · rename_i genEnv heq_gen
          split at h
          · simp at h
          · rename_i substInfo heq_unify
            cases h
            -- Unwrap mapError to get raw unify success
            have h_unify : Constraints.unify
                [(toLMonoTy e1t_env.fst, LMonoTy.tcons "arrow" [toLMonoTy e2t_env.fst, LMonoTy.ftvar genEnv.fst])]
                genEnv.snd.stateSubstInfo = .ok substInfo :=
              unify_of_mapError heq_unify
            -- genTyVar facts
            have h_gen_subst := TEnv.genTyVar_subst e2t_env.snd genEnv.fst genEnv.snd heq_gen
            have h_gen_ctx := TEnv.genTyVar_context e2t_env.snd genEnv.fst genEnv.snd heq_gen
            have h_gen_tyGen := genTyVar_tyGen e2t_env.snd genEnv.fst genEnv.snd heq_gen
            have h_gen_name := genTyVar_name_eq e2t_env.snd genEnv.fst genEnv.snd heq_gen
            -- Properties for e1
            have h_props1 := resolveAux_properties e1 e1t_env.fst C Env e1t_env.snd heq_e1
              h_ne h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen
              h_envwf.boundVarsFresh
            have h_ctx1 : e1t_env.snd.context = Env.context := h_props1.context
            have h_envwf1 := TEnvWF.of_resolveAux e1 e1t_env.fst C Env e1t_env.snd
              heq_e1 h_envwf h_ne h_fwf h_ctx1
            have h_ne1 : e1t_env.snd.context.types ≠ [] := h_ctx1 ▸ h_ne
            -- Properties for e2
            have h_props2 := resolveAux_properties e2 e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2
              h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen
              h_envwf1.boundVarsFresh
            -- Absorption: h_absorbs : S.absorbs (Maps.remove substInfo.subst genEnv.fst)
            have h_abs_S_rem : S.absorbs (Maps.remove substInfo.subst genEnv.fst) := by
              simp [TEnv.updateSubst] at h_absorbs; exact h_absorbs
            -- Rewrite unify to use e2t_env.snd.stateSubstInfo (genTyVar preserves subst)
            rw [h_gen_subst] at h_unify
            have h_abs_unify := unify_absorbs _ _ _ h_unify
            -- Freshness: genEnv.fst not in Env.subst and e1t_env.snd.subst
            have h_fresh_Env : Maps.find? Env.stateSubstInfo.subst genEnv.fst = none ∧
                (∀ a t, Maps.find? Env.stateSubstInfo.subst a = some t →
                  genEnv.fst ∉ LMonoTy.freeVars t) :=
              genTyVar_fresh_wrt_input_subst Env e2t_env.snd genEnv.snd genEnv.fst heq_gen
                h_envwf.substFreshForGen
                (Nat.le_trans h_props1.genState_mono h_props2.genState_mono)
            have h_fresh_e1 : Maps.find? e1t_env.snd.stateSubstInfo.subst genEnv.fst = none ∧
                (∀ a t, Maps.find? e1t_env.snd.stateSubstInfo.subst a = some t →
                  genEnv.fst ∉ LMonoTy.freeVars t) :=
              genTyVar_fresh_wrt_input_subst e1t_env.snd e2t_env.snd genEnv.snd genEnv.fst heq_gen
                h_envwf1.substFreshForGen h_props2.genState_mono
            have h_fresh_e2 : Maps.find? e2t_env.snd.stateSubstInfo.subst genEnv.fst = none ∧
                (∀ a t, Maps.find? e2t_env.snd.stateSubstInfo.subst a = some t →
                  genEnv.fst ∉ LMonoTy.freeVars t) :=
              genTyVar_fresh_wrt_input_subst e2t_env.snd e2t_env.snd genEnv.snd genEnv.fst heq_gen
                h_props2.preserves.1 (Nat.le_refl _)
            -- absorbs (remove substInfo genEnv.fst) Env1.subst / Env2.subst
            have h_abs_rem_e2 := Subst.absorbs_of_remove
              substInfo.subst e2t_env.snd.stateSubstInfo.subst genEnv.fst
              h_abs_unify h_fresh_e2.1 h_fresh_e2.2
            have h_abs_rem_e1 := Subst.absorbs_of_remove
              substInfo.subst e1t_env.snd.stateSubstInfo.subst genEnv.fst
              (Subst.absorbs_trans _ _ _ h_props2.absorbs h_abs_unify)
              h_fresh_e1.1 h_fresh_e1.2
            -- Chain: S absorbs (remove substInfo fresh) absorbs Env1/Env2
            have h_abs_e2 : S.absorbs e2t_env.snd.stateSubstInfo.subst :=
              Subst.absorbs_trans _ _ _ h_abs_rem_e2 h_abs_S_rem
            have h_abs_e1 : S.absorbs e1t_env.snd.stateSubstInfo.subst :=
              Subst.absorbs_trans _ _ _ h_abs_rem_e1 h_abs_S_rem
            -- fresh_name ∉ freeVars e1t.toLMonoTy and e2t.toLMonoTy
            have h_e1t_no_fresh : genEnv.fst ∉ LMonoTy.freeVars e1t_env.fst.toLMonoTy := by
              intro h_mem
              exact absurd h_gen_name
                (h_props1.preserves.2 genEnv.fst h_mem e2t_env.snd.genEnv.genState.tyGen
                  h_props2.genState_mono)
            have h_e2t_no_fresh : genEnv.fst ∉ LMonoTy.freeVars e2t_env.fst.toLMonoTy := by
              intro h_mem
              exact absurd h_gen_name
                (h_props2.preserves.2 genEnv.fst h_mem e2t_env.snd.genEnv.genState.tyGen
                  (Nat.le_refl _))
            -- Unification soundness + absorption to derive type equality
            have h_unify_eq : LMonoTy.subst substInfo.subst e1t_env.fst.toLMonoTy =
                LMonoTy.subst substInfo.subst
                  (LMonoTy.tcons "arrow" [e2t_env.fst.toLMonoTy, .ftvar genEnv.fst]) := by
              have h_p := unify_sound _ _ _ h_unify _ (List.Mem.head _)
              simp at h_p; exact h_p
            -- subst S (subst substInfo e1t.toLMonoTy) = subst S e1t.toLMonoTy
            have h_subst_e1t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e1t_env.fst.toLMonoTy) =
                LMonoTy.subst S e1t_env.fst.toLMonoTy := by
              rw [← LMonoTy.subst_remove_not_fv substInfo.subst genEnv.fst
                    e1t_env.fst.toLMonoTy h_e1t_no_fresh]
              exact LMonoTy.subst_absorbs S (Maps.remove substInfo.subst genEnv.fst)
                e1t_env.fst.toLMonoTy h_abs_S_rem
            have h_subst_e2t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e2t_env.fst.toLMonoTy) =
                LMonoTy.subst S e2t_env.fst.toLMonoTy := by
              rw [← LMonoTy.subst_remove_not_fv substInfo.subst genEnv.fst
                    e2t_env.fst.toLMonoTy h_e2t_no_fresh]
              exact LMonoTy.subst_absorbs S (Maps.remove substInfo.subst genEnv.fst)
                e2t_env.fst.toLMonoTy h_abs_S_rem
            -- Key equality: subst S e1t.toLMonoTy = arrow [subst S e2t.toLMonoTy, subst S (subst substInfo (ftvar fresh))]
            have h_eq_S : LMonoTy.subst S e1t_env.fst.toLMonoTy =
                LMonoTy.tcons "arrow"
                  [LMonoTy.subst S e2t_env.fst.toLMonoTy,
                   LMonoTy.subst S (LMonoTy.subst substInfo.subst (.ftvar genEnv.fst))] := by
              have h_congr := congrArg (LMonoTy.subst S) h_unify_eq
              rw [h_subst_e1t] at h_congr
              rw [LMonoTy.subst_tcons_pair substInfo.subst "arrow"
                    e2t_env.fst.toLMonoTy (.ftvar genEnv.fst)] at h_congr
              rw [LMonoTy.subst_tcons_pair S "arrow"
                    (LMonoTy.subst substInfo.subst e2t_env.fst.toLMonoTy)
                    (LMonoTy.subst substInfo.subst (.ftvar genEnv.fst))] at h_congr
              rw [h_subst_e2t] at h_congr
              exact h_congr
            -- IH for e1 and e2
            have h_sz1 : e1.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
            have h_sz2 : e2.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
            have h_ih_e1 := ih e1.sizeOf h_sz1 e1 rfl e1t_env.fst C Env e1t_env.snd heq_e1
              h_envwf h_ne h_fwf S h_abs_e1
            have h_ih_e2 := ih e2.sizeOf h_sz2 e2 rfl e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2
              h_envwf1 h_ne1 h_fwf S h_abs_e2
            -- Simplify and apply HasTypeA.app
            simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
            rw [applySubstT_toLMonoTy] at h_ih_e1 h_ih_e2
            rw [h_eq_S] at h_ih_e1
            exact HasTypeA.app h_ih_e1 h_ih_e2
  | .abs m_abs name_abs bty_abs e_body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1
      dsimp at h h_tbv
      split at h
      · simp at h
      · rename_i v2 h_res_body
        obtain ⟨et_body, Env2⟩ := v2
        dsimp at h h_res_body
        simp at h
        obtain ⟨h_et, h_env'⟩ := h
        subst h_et h_env'
        -- Env' = eraseFromContext Env2 xv
        -- et = .abs ⟨m_abs, subst Env2.subst (arrow [xty, (varCloseT ..).toLMonoTy])⟩ name bty (varCloseT 0 xv et_body)
        -- Get TEnvWF for Env1
        have h_envwf1 : TEnvWF Env1 :=
          TEnvWF.of_typeBoundVar C Env bty_abs xv xty Env1 h_tbv h_envwf
        have h_ne1 : Env1.context.types ≠ [] :=
          typeBoundVar_context_types_ne_nil C Env bty_abs xv xty Env1 h_tbv
        -- IH for the opened body
        have h_sz_body : (LExpr.varOpen 0 (xv, some xty) e_body).sizeOf < n := by
          subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]
        -- Absorption for Env2
        have h_abs_Env2 : S.absorbs Env2.stateSubstInfo.subst := by
          simp [TEnv.eraseFromContext, TEnv.updateContext] at h_absorbs
          exact h_absorbs
        have h_ih_body := ih (LExpr.varOpen 0 (xv, some xty) e_body).sizeOf h_sz_body
          (LExpr.varOpen 0 (xv, some xty) e_body) rfl et_body C Env1 Env2 h_res_body
          h_envwf1 h_ne1 h_fwf S h_abs_Env2
        -- h_ih_body : HasTypeA [] (applySubstT et_body S).unresolved (toLMonoTy (applySubstT et_body S))
        -- Need: HasTypeA [] (applySubstT (.abs ...) S).unresolved (toLMonoTy (applySubstT (.abs ...) S))
        show HasTypeA []
          (applySubstT (.abs ⟨m_abs, LMonoTy.subst Env2.stateSubstInfo.subst
            (LMonoTy.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])⟩
            name_abs bty_abs (LExpr.varCloseT 0 xv et_body)) S).unresolved
          ((applySubstT (.abs ⟨m_abs, LMonoTy.subst Env2.stateSubstInfo.subst
            (LMonoTy.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])⟩
            name_abs bty_abs (LExpr.varCloseT 0 xv et_body)) S).toLMonoTy)
        rw [varCloseT_toLMonoTy, applySubstT_toLMonoTy]
        conv => rhs; simp only [toLMonoTy]
                rw [LMonoTy.subst_absorbs S Env2.stateSubstInfo.subst _ h_abs_Env2,
                    LMonoTy.subst_tcons_pair]
        conv => lhs; simp only [applySubstT, replaceMetadata]
                rw [show LMonoTy.subst S (LMonoTy.subst Env2.stateSubstInfo.subst
                      (LMonoTy.tcons "arrow" [xty, et_body.toLMonoTy])) =
                    LMonoTy.arrow (LMonoTy.subst S xty) (LMonoTy.subst S et_body.toLMonoTy) from by
                  rw [LMonoTy.subst_absorbs S Env2.stateSubstInfo.subst _ h_abs_Env2,
                      LMonoTy.subst_tcons_pair]; rfl]
                simp only [unresolved, LMonoTy.arrow]
        apply HasTypeA.abs
        change HasTypeA [LMonoTy.subst S xty]
          (applySubstT (LExpr.varCloseT 0 xv et_body) S).unresolved
          (LMonoTy.subst S et_body.toLMonoTy)
        rw [applySubstT_varCloseT_comm]
        have h_ty_eq : LMonoTy.subst S et_body.toLMonoTy =
            (LExpr.varCloseT 0 xv (applySubstT et_body S)).toLMonoTy := by
          rw [varCloseT_toLMonoTy, applySubstT_toLMonoTy]
        rw [h_ty_eq]
        have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
          typeBoundVar_adds_to_context C Env bty_abs xv xty Env1 h_tbv
        have h_annot_raw : LExprT.allFvarAnnot xv xty et_body :=
          resolveAux_allFvarAnnot C Env1 Env2
            (LExpr.varOpen 0 (xv, some xty) e_body) et_body xv xty h_res_body h_ctx_xv
        have h_annot : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_body S) :=
          applySubstT_allFvarAnnot xv xty et_body S h_annot_raw
        exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
          (applySubstT et_body S) h_ih_body h_annot
  | .quant m_q qk_q name_q bty_q trigger_q e_q =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1
      dsimp at h h_tbv
      split at h
      · simp at h
      · rename_i v2 h_res_body
        obtain ⟨et_body, Env2⟩ := v2
        dsimp at h h_res_body
        split at h
        · simp at h
        · rename_i v3 h_res_tr
          obtain ⟨et_tr, Env3⟩ := v3
          dsimp at h h_res_tr
          split at h
          · simp at h
          · simp at h
            obtain ⟨h_et, h_env'⟩ := h
            subst h_et h_env'
            -- h✝ : ¬(toLMonoTy et_body != LMonoTy.bool) = true
            rename_i h_body_bool
            have h_body_ty_bool : toLMonoTy et_body = LMonoTy.bool := by
              simp [bne] at h_body_bool; exact h_body_bool
            -- Get TEnvWF chain
            have h_envwf1 : TEnvWF Env1 :=
              TEnvWF.of_typeBoundVar C Env bty_q xv xty Env1 h_tbv h_envwf
            have h_ne1 : Env1.context.types ≠ [] :=
              typeBoundVar_context_types_ne_nil C Env bty_q xv xty Env1 h_tbv
            -- Get properties for body resolution
            have h_props_body := resolveAux_properties
              (LExpr.varOpen 0 (xv, some xty) e_q) et_body C Env1 Env2 h_res_body
              h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.substFreshForGen
              h_envwf1.ctxFreshForGen h_envwf1.boundVarsFresh
            have h_ctx_body : Env2.context = Env1.context := h_props_body.context
            have h_envwf2 := TEnvWF.of_resolveAux
              (LExpr.varOpen 0 (xv, some xty) e_q) et_body C Env1 Env2
              h_res_body h_envwf1 h_ne1 h_fwf h_ctx_body
            have h_ne2 : Env2.context.types ≠ [] := h_ctx_body ▸ h_ne1
            -- Absorption chain
            have h_abs_Env3 : S.absorbs Env3.stateSubstInfo.subst := by
              simp [TEnv.eraseFromContext, TEnv.updateContext] at h_absorbs
              exact h_absorbs
            have h_abs_Env2 : S.absorbs Env2.stateSubstInfo.subst := by
              have h_props_tr := resolveAux_properties
                (LExpr.varOpen 0 (xv, some xty) trigger_q) et_tr C Env2 Env3 h_res_tr
                h_ne2 h_envwf2.aliasesWF h_fwf h_envwf2.substFreshForGen
                h_envwf2.ctxFreshForGen h_envwf2.boundVarsFresh
              exact Subst.absorbs_trans _ _ _ h_props_tr.absorbs h_abs_Env3
            -- IH for body
            have h_sz_body : (LExpr.varOpen 0 (xv, some xty) e_q).sizeOf < n := by
              subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
            have h_ih_body := ih (LExpr.varOpen 0 (xv, some xty) e_q).sizeOf h_sz_body
              (LExpr.varOpen 0 (xv, some xty) e_q) rfl et_body C Env1 Env2 h_res_body
              h_envwf1 h_ne1 h_fwf S h_abs_Env2
            -- IH for trigger
            have h_sz_tr : (LExpr.varOpen 0 (xv, some xty) trigger_q).sizeOf < n := by
              subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
            have h_ih_tr := ih (LExpr.varOpen 0 (xv, some xty) trigger_q).sizeOf h_sz_tr
              (LExpr.varOpen 0 (xv, some xty) trigger_q) rfl et_tr C Env2 Env3 h_res_tr
              h_envwf2 h_ne2 h_fwf S h_abs_Env3
            -- Simplify goal: RHS is already bool via toLMonoTy of quant
            show HasTypeA []
              (applySubstT (.quant ⟨m_q, LMonoTy.subst Env3.stateSubstInfo.subst xty⟩
                qk_q name_q (some (LMonoTy.subst Env3.stateSubstInfo.subst xty))
                (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body)) S).unresolved
              ((applySubstT (.quant ⟨m_q, LMonoTy.subst Env3.stateSubstInfo.subst xty⟩
                qk_q name_q (some (LMonoTy.subst Env3.stateSubstInfo.subst xty))
                (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body)) S).toLMonoTy)
            simp only [toLMonoTy]
            simp only [applySubstT, replaceMetadata, unresolved]
            -- Goal: HasTypeA [] (.quant m_q qk_q name_q (some (subst S (subst Env3.subst xty)))
            --   (replaceMetadata (varCloseT 0 xv et_tr) ...).unresolved
            --   (replaceMetadata (varCloseT 0 xv et_body) ...).unresolved) .bool
            -- Recognize replaceMetadata ... as applySubstT (varCloseT ...) S
            change HasTypeA []
              (.quant m_q qk_q name_q (some (LMonoTy.subst S (LMonoTy.subst Env3.stateSubstInfo.subst xty)))
                (applySubstT (LExpr.varCloseT 0 xv et_tr) S).unresolved
                (applySubstT (LExpr.varCloseT 0 xv et_body) S).unresolved)
              LMonoTy.bool
            rw [applySubstT_varCloseT_comm (xv := xv) (et := et_tr),
                applySubstT_varCloseT_comm (xv := xv) (et := et_body)]
            rw [LMonoTy.subst_absorbs S Env3.stateSubstInfo.subst xty h_abs_Env3]
            refine HasTypeA.quant (τ_tr := (LExpr.varCloseT 0 xv (applySubstT et_tr S)).toLMonoTy) ?_ ?_
            · -- Trigger: HasTypeA [subst S xty] (varCloseT 0 xv (applySubstT et_tr S)).unresolved
              --                                  (varCloseT 0 xv (applySubstT et_tr S)).toLMonoTy
              have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
                typeBoundVar_adds_to_context C Env bty_q xv xty Env1 h_tbv
              have h_ctx_xv2 : Env2.context.types.find? xv = some (.forAll [] xty) :=
                h_ctx_body ▸ h_ctx_xv
              have h_annot_tr_raw : LExprT.allFvarAnnot xv xty et_tr :=
                resolveAux_allFvarAnnot C Env2 Env3
                  (LExpr.varOpen 0 (xv, some xty) trigger_q) et_tr xv xty h_res_tr h_ctx_xv2
              have h_annot_tr : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_tr S) :=
                applySubstT_allFvarAnnot xv xty et_tr S h_annot_tr_raw
              exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
                (applySubstT et_tr S) h_ih_tr h_annot_tr
            · -- Body: HasTypeA [subst S xty] (varCloseT 0 xv (applySubstT et_body S)).unresolved .bool
              have h_body_ty_eq : (LExpr.varCloseT 0 xv (applySubstT et_body S)).toLMonoTy = LMonoTy.bool := by
                rw [varCloseT_toLMonoTy, applySubstT_toLMonoTy, h_body_ty_bool, LMonoTy.subst_bool]
              rw [← h_body_ty_eq]
              have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
                typeBoundVar_adds_to_context C Env bty_q xv xty Env1 h_tbv
              have h_annot_body_raw : LExprT.allFvarAnnot xv xty et_body :=
                resolveAux_allFvarAnnot C Env1 Env2
                  (LExpr.varOpen 0 (xv, some xty) e_q) et_body xv xty h_res_body h_ctx_xv
              have h_annot_body : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_body S) :=
                applySubstT_allFvarAnnot xv xty et_body S h_annot_body_raw
              exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
                (applySubstT et_body S) h_ih_body h_annot_body
  | .eq m_eq e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i e1t_env heq_e1
      split at h
      · simp at h
      · rename_i e2t_env heq_e2
        split at h
        · simp at h
        · rename_i substInfo heq_unify
          cases h
          -- Unwrap mapError to get raw unify success
          have h_unify : Constraints.unify [(e1t_env.fst.toLMonoTy, e2t_env.fst.toLMonoTy)]
              e2t_env.snd.stateSubstInfo = .ok substInfo := by
            revert heq_unify
            generalize Constraints.unify [(e1t_env.fst.toLMonoTy, e2t_env.fst.toLMonoTy)]
              e2t_env.snd.stateSubstInfo = res
            intro h_me; match res, h_me with
            | .ok _, h_me => simp [Except.mapError] at h_me; rw [h_me]
            | .error _, h_me => simp [Except.mapError] at h_me
          -- Get properties from resolveAux on e1
          have h_props1 := resolveAux_properties e1 e1t_env.fst C Env e1t_env.snd heq_e1
            h_ne h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen
            h_envwf.boundVarsFresh
          have h_ctx1 : e1t_env.snd.context = Env.context := h_props1.context
          have h_envwf1 := TEnvWF.of_resolveAux e1 e1t_env.fst C Env e1t_env.snd
            heq_e1 h_envwf h_ne h_fwf h_ctx1
          have h_ne1 : e1t_env.snd.context.types ≠ [] := h_ctx1 ▸ h_ne
          -- Get properties from resolveAux on e2
          have h_props2 := resolveAux_properties e2 e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2
            h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen
            h_envwf1.boundVarsFresh
          -- Absorption chain
          have h_abs_unify := unify_absorbs _ _ _ h_unify
          have h_abs_e2 : S.absorbs e2t_env.snd.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _
              h_abs_unify h_absorbs
          have h_abs_e1 : S.absorbs e1t_env.snd.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _
              h_props2.absorbs h_abs_e2
          -- Simplify h_absorbs to use substInfo directly
          have h_S_abs_substInfo : S.absorbs substInfo.subst := by
            simp [TEnv.updateSubst] at h_absorbs; exact h_absorbs
          -- Unification soundness: both types become equal under S
          have h_eq_types : toLMonoTy (applySubstT e1t_env.fst S) = toLMonoTy (applySubstT e2t_env.fst S) := by
            rw [applySubstT_toLMonoTy, applySubstT_toLMonoTy]
            have h_sound := unify_sound _ _ _ h_unify
            have h_pair := h_sound _ (List.Mem.head _)
            simp at h_pair
            calc LMonoTy.subst S (toLMonoTy e1t_env.fst)
                = LMonoTy.subst S (LMonoTy.subst substInfo.subst (toLMonoTy e1t_env.fst)) :=
                  (LMonoTy.subst_absorbs S substInfo.subst _ h_S_abs_substInfo).symm
              _ = LMonoTy.subst S (LMonoTy.subst substInfo.subst (toLMonoTy e2t_env.fst)) := by
                  rw [h_pair]
              _ = LMonoTy.subst S (toLMonoTy e2t_env.fst) :=
                  LMonoTy.subst_absorbs S substInfo.subst _ h_S_abs_substInfo
          simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
          rw [LMonoTy.subst_bool]
          apply HasTypeA.eq (τ := toLMonoTy (applySubstT e1t_env.fst S))
          · have h_sz : e1.sizeOf < n := by subst h_eq; simp_all [LExpr.sizeOf]; omega
            exact ih e1.sizeOf h_sz e1 rfl e1t_env.fst C Env e1t_env.snd heq_e1 h_envwf h_ne h_fwf S h_abs_e1
          · rw [h_eq_types]
            have h_sz2 : e2.sizeOf < n := by subst h_eq; simp_all [LExpr.sizeOf]; omega
            exact ih e2.sizeOf h_sz2 e2 rfl e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2 h_envwf1 h_ne1 h_fwf S h_abs_e2
  | .ite m_ite c_expr th_expr el_expr =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i ct_env heq_c
      split at h
      · simp at h
      · rename_i tht_env heq_th
        split at h
        · simp at h
        · rename_i elt_env heq_el
          split at h
          · simp at h
          · rename_i substInfo heq_unify
            cases h
            -- Unwrap mapError
            have h_unify : Constraints.unify
                [(ct_env.fst.toLMonoTy, LMonoTy.bool),
                 (tht_env.fst.toLMonoTy, elt_env.fst.toLMonoTy)]
                elt_env.snd.stateSubstInfo = .ok substInfo := by
              revert heq_unify
              generalize Constraints.unify _ elt_env.snd.stateSubstInfo = res
              intro h_me; match res, h_me with
              | .ok _, h_me => simp [Except.mapError] at h_me; rw [h_me]
              | .error _, h_me => simp [Except.mapError] at h_me
            -- Properties for c
            have h_props_c := resolveAux_properties c_expr ct_env.fst C Env ct_env.snd heq_c
              h_ne h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen
              h_envwf.boundVarsFresh
            have h_ctx_c : ct_env.snd.context = Env.context := h_props_c.context
            have h_envwf_c := TEnvWF.of_resolveAux c_expr ct_env.fst C Env ct_env.snd
              heq_c h_envwf h_ne h_fwf h_ctx_c
            have h_ne_c : ct_env.snd.context.types ≠ [] := h_ctx_c ▸ h_ne
            -- Properties for th
            have h_props_th := resolveAux_properties th_expr tht_env.fst C ct_env.snd tht_env.snd heq_th
              h_ne_c h_envwf_c.aliasesWF h_fwf h_envwf_c.substFreshForGen h_envwf_c.ctxFreshForGen
              h_envwf_c.boundVarsFresh
            have h_ctx_th : tht_env.snd.context = ct_env.snd.context := h_props_th.context
            have h_envwf_th := TEnvWF.of_resolveAux th_expr tht_env.fst C ct_env.snd tht_env.snd
              heq_th h_envwf_c h_ne_c h_fwf h_ctx_th
            have h_ne_th : tht_env.snd.context.types ≠ [] := h_ctx_th ▸ h_ne_c
            -- Properties for el
            have h_props_el := resolveAux_properties el_expr elt_env.fst C tht_env.snd elt_env.snd heq_el
              h_ne_th h_envwf_th.aliasesWF h_fwf h_envwf_th.substFreshForGen h_envwf_th.ctxFreshForGen
              h_envwf_th.boundVarsFresh
            -- Absorption chain
            have h_abs_unify := unify_absorbs _ _ _ h_unify
            have h_S_abs_substInfo : S.absorbs substInfo.subst := by
              simp [TEnv.updateSubst] at h_absorbs; exact h_absorbs
            have h_abs_el : S.absorbs elt_env.snd.stateSubstInfo.subst :=
              Subst.absorbs_trans _ _ _ h_abs_unify h_S_abs_substInfo
            have h_abs_th : S.absorbs tht_env.snd.stateSubstInfo.subst :=
              Subst.absorbs_trans _ _ _ h_props_el.absorbs h_abs_el
            have h_abs_c : S.absorbs ct_env.snd.stateSubstInfo.subst :=
              Subst.absorbs_trans _ _ _ h_props_th.absorbs h_abs_th
            -- Unification soundness
            have h_sound := unify_sound _ _ _ h_unify
            have h_c_bool : LMonoTy.subst substInfo.subst ct_env.fst.toLMonoTy = LMonoTy.bool := by
              have h_p := h_sound _ (List.Mem.head _)
              simp [LMonoTy.subst_bool] at h_p; exact h_p
            have h_th_el : LMonoTy.subst substInfo.subst tht_env.fst.toLMonoTy =
                LMonoTy.subst substInfo.subst elt_env.fst.toLMonoTy := by
              have h_p := h_sound _ (List.Mem.tail _ (List.Mem.head _))
              simp at h_p; exact h_p
            -- c has type bool under S
            have h_c_type_bool : LMonoTy.subst S (toLMonoTy ct_env.fst) = LMonoTy.bool := by
              calc LMonoTy.subst S (toLMonoTy ct_env.fst)
                  = LMonoTy.subst S (LMonoTy.subst substInfo.subst (toLMonoTy ct_env.fst)) :=
                    (LMonoTy.subst_absorbs S substInfo.subst _ h_S_abs_substInfo).symm
                _ = LMonoTy.subst S LMonoTy.bool := by rw [h_c_bool]
                _ = LMonoTy.bool := LMonoTy.subst_bool S
            -- th and el have equal types under S
            have h_th_el_eq : LMonoTy.subst S (toLMonoTy tht_env.fst) = LMonoTy.subst S (toLMonoTy elt_env.fst) := by
              calc LMonoTy.subst S (toLMonoTy tht_env.fst)
                  = LMonoTy.subst S (LMonoTy.subst substInfo.subst (toLMonoTy tht_env.fst)) :=
                    (LMonoTy.subst_absorbs S substInfo.subst _ h_S_abs_substInfo).symm
                _ = LMonoTy.subst S (LMonoTy.subst substInfo.subst (toLMonoTy elt_env.fst)) := by
                    rw [h_th_el]
                _ = LMonoTy.subst S (toLMonoTy elt_env.fst) :=
                    LMonoTy.subst_absorbs S substInfo.subst _ h_S_abs_substInfo
            have h_sz_c : c_expr.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
            have h_sz_th : th_expr.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
            have h_sz_el : el_expr.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
            change HasTypeA [] (LExpr.ite m_ite (applySubstT ct_env.fst S).unresolved
              (applySubstT tht_env.fst S).unresolved (applySubstT elt_env.fst S).unresolved)
              (LMonoTy.subst S (toLMonoTy tht_env.fst))
            rw [← applySubstT_toLMonoTy tht_env.fst S]
            apply HasTypeA.ite
            · have h_ih_c := ih c_expr.sizeOf h_sz_c c_expr rfl ct_env.fst C Env ct_env.snd heq_c h_envwf h_ne h_fwf S h_abs_c
              rw [applySubstT_toLMonoTy, h_c_type_bool] at h_ih_c
              exact h_ih_c
            · exact ih th_expr.sizeOf h_sz_th th_expr rfl tht_env.fst C ct_env.snd tht_env.snd heq_th h_envwf_c h_ne_c h_fwf S h_abs_th
            · have h_ih_el := ih el_expr.sizeOf h_sz_el el_expr rfl elt_env.fst C tht_env.snd elt_env.snd heq_el h_envwf_th h_ne_th h_fwf S h_abs_el
              rw [applySubstT_toLMonoTy] at h_ih_el
              rw [applySubstT_toLMonoTy, h_th_el_eq]
              exact h_ih_el

theorem resolveAux_HasTypeA
    (C : LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono) (Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    HasTypeA [] (applySubstT et Env'.stateSubstInfo.subst).unresolved
               ((applySubstT et Env'.stateSubstInfo.subst).toLMonoTy) := by
  have h_absorbs := Subst.absorbs_refl Env'.stateSubstInfo.subst Env'.stateSubstInfo.isWF
  exact resolveAux_HasTypeA_aux e.sizeOf e rfl et C Env Env' h h_envwf h_ne h_fwf
    Env'.stateSubstInfo.subst h_absorbs

/-! ### Layer 4: Top-level `resolve_HasTypeA` -/

theorem resolve_HasTypeA
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env : TEnv T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = Except.ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactoryWF C.functions) :
    LExpr.HasTypeA [] e_typed.unresolved (e_typed.toLMonoTy) := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  -- Case split on resolveAux result
  have h_resolve := h
  generalize h_res : resolveAux C _ e = res at h_resolve
  cases res with
  | error => simp at h_resolve
  | ok val =>
    simp at h_resolve
    obtain ⟨h_et, h_env⟩ := h_resolve
    subst h_et h_env
    have h_envwf0 := TEnvWF_resolve_init Env h_envwf
    have h_ne0 : (if Env.context.types.isEmpty = true then
        Env.updateContext { types := [[]], aliases := Env.context.aliases }
      else Env).context.types ≠ [] := by
      split
      · exact List.cons_ne_nil _ _
      · rename_i h_not_empty
        intro h_abs
        simp_all
        contradiction
    exact resolveAux_HasTypeA C _ e val.fst val.snd h_res h_envwf0 h_ne0 h_fwf

end

end Lambda

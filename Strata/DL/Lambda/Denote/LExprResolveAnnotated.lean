/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprAliasFree
import all Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Denote.LExprAnnotatedProps
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.LExprTProps
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.Denote.Assumptions

/-! # `resolve` produces well-annotated expressions (`HasTypeA`)

This module proves that when `LExpr.resolve` succeeds, the resulting expression
satisfies `HasTypeA` — i.e., the type annotations placed by resolution are
internally consistent. `resolve_HasTypeA_subst` gives the same under any
substitution absorbing the resolver's; `resolve_opsConsistentR`,
`resolve_opAnnots` and `resolve_binderAnnotations_known` give the operator and
binder annotation conditions; `resolve_fvarAnnots_agree` relates the
free-variable annotations to the input context; `resolve_fvars_annotated_by`
gives `fvars_annotated_by` for every type map the substituted context holds; and
`resolve_output_HasType` combines these with the bridge to `HasType` to type
the output.

### Comparison with `resolve_HasType`

`resolve_HasType` (in `LExprTypeSpec`) proves full polymorphic typing
(`HasType`) but requires `WellScoped` and `checkContextTypesClosed`.
`resolve_HasTypeA` here proves annotation-consistency (`HasTypeA`) under
different assumptions: `TEnvWF`, `FactorySigWF`, and `AliasesResolved`. It
drops the scoping and closure conditions but adds `AliasesResolved`, which
`resolve_HasType` does not need.

### Proof structure

The proof proceeds in layers:

1. **Alias-free infrastructure** (in `LExprAliasFree`):
`resolveAliases_aliasFree`,`resolveAliases_output_aliasFree`,
`instantiateWithCheck_aliasFree`,`typeBoundVar_xty_aliasFree`.
On a monomorphic scheme `∀[]. xty`, `inferFVar`
returns the alias resolution of `xty` (`SourceTyResolves`), which is `xty`
itself when `xty` is alias-free.

2. **`allFvarAnnot` and `varCloseT`** (`resolveAux_allFvarAnnot`,
`varCloseT_unresolved_HasTypeA`). The abs/quant cases of `resolveAux` open a
bound variable as a fresh fvar, recurse, then close it. To show the result is
well-annotated, we need (a) that `resolveAux` annotates every free occurrence of
the fresh variable with the alias resolution of its type, and (b) that closing
turns these into correctly-indexed bvars in the `HasTypeA` sense.

3. **Main induction** (`resolveAux_HasTypeA_aux`). Our result is generalized
 over an arbitrary substitution `S` absorbing the output, rather than fixing
`S` to be the final substitution. This generalization is essential:
`resolveAux` recurses on sub-expressions whose output substitutions are smaller
than the final one, and the IH must apply to each sub-result under the caller's
(larger) substitution.
-/

namespace Lambda

open LExpr
open Strata.Util (HMap HMaps)

section

variable {T : LExprParams} [Std.ToFormat T.IDMeta]

/-! ### `allFvarAnnot`, `varCloseT`, and structural helpers -/

/-- Every free occurrence of `xv` in `et` carries type `t` in its metadata. -/
def LExprT.allFvarAnnot (xv : T.Identifier) (t : LMonoTy) : LExprT T.mono → Prop
  | .fvar m y _ => y = xv → m.type = t
  | .app _ f a => allFvarAnnot xv t f ∧ allFvarAnnot xv t a
  | .abs _ _ _ e => allFvarAnnot xv t e
  | .quant _ _ _ _ tr e => allFvarAnnot xv t tr ∧ allFvarAnnot xv t e
  | .ite _ c th el => allFvarAnnot xv t c ∧ allFvarAnnot xv t th ∧ allFvarAnnot xv t el
  | .eq _ e1 e2 => allFvarAnnot xv t e1 ∧ allFvarAnnot xv t e2
  | _ => True

omit [Std.ToFormat T.IDMeta] in
/-- Applying a type substitution to metadata preserves `allFvarAnnot`,
    transforming the annotation type by the same substitution. -/
theorem applySubstT_allFvarAnnot (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono) (S : Subst)
    (h : LExprT.allFvarAnnot xv t et) :
    LExprT.allFvarAnnot xv (LMonoTy.subst S t) (applySubstT et S) := by
  induction et with
  | fvar m y yty =>
    simp only [LExprT.allFvarAnnot, applySubstT, LExpr.replaceMetadata] at *
    intro heq
    rw [h heq]
  | app m f a ih_f ih_a =>
    simp only [LExprT.allFvarAnnot, applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih_f h.1, ih_a h.2⟩
  | abs m name ty e ih_e =>
    simp only [LExprT.allFvarAnnot, applySubstT, LExpr.replaceMetadata] at *
    exact ih_e h
  | quant m qk name ty tr e ih_tr ih_e =>
    simp only [LExprT.allFvarAnnot, applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih_tr h.1, ih_e h.2⟩
  | ite m c th el ih_c ih_th ih_el =>
    simp only [LExprT.allFvarAnnot, applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih_c h.1, ih_th h.2.1, ih_el h.2.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExprT.allFvarAnnot, applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih1 h.1, ih2 h.2⟩
  | const m c => trivial
  | op m o ty => trivial
  | bvar m i => trivial


omit [Std.ToFormat T.IDMeta] in
/-- `varCloseT` preserves `allFvarAnnot`: if `y ≠ xv` the annotations are unchanged;
    if `y = xv` the property holds vacuously since all `xv` occurrences become bvars. -/
theorem allFvarAnnot_varCloseT_ne [DecidableEq T.IDMeta]
  (xv y : T.Identifier) (t : LMonoTy)
    (k : Nat) (et : LExprT T.mono)
    (h : LExprT.allFvarAnnot xv t et) :
    LExprT.allFvarAnnot xv t (LExpr.varCloseT k y et) := by
  induction et generalizing k with
  | fvar m z zty =>
    simp only [LExpr.varCloseT]
    split
    · -- z = y, result is .bvar m k
      simp [LExprT.allFvarAnnot]
    · -- z ≠ y, unchanged
      exact h
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.varCloseT, LExprT.allFvarAnnot] at *
    exact ⟨ih1 k h.1, ih2 k h.2⟩
  | abs m name ty body ih =>
    simp only [LExpr.varCloseT, LExprT.allFvarAnnot] at *
    exact ih (k + 1) h
  | quant m qk name ty tr body ih_tr ih_body =>
    simp only [LExpr.varCloseT, LExprT.allFvarAnnot] at *
    exact ⟨ih_tr (k + 1) h.1, ih_body (k + 1) h.2⟩
  | ite m c th el ih_c ih_th ih_el =>
    simp only [LExpr.varCloseT, LExprT.allFvarAnnot] at *
    exact ⟨ih_c k h.1, ih_th k h.2.1, ih_el k h.2.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.varCloseT, LExprT.allFvarAnnot] at *
    exact ⟨ih1 k h.1, ih2 k h.2⟩
  | const _ _ => trivial
  | op _ _ _ => trivial
  | bvar _ _ => trivial


/-- For a variable with a monomorphic scheme `∀[]. xty` in the context, `inferFVar` returns the
    alias resolution of `xty`. -/
private theorem inferFVar_mono_resolves [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (C : LContext T) (Env : TEnv T.IDMeta)
    (x : T.Identifier) (fty : Option LMonoTy) (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    {xty : LMonoTy}
    (h : inferFVar C Env x fty = .ok (ty_res, Env'))
    (h_ctx : Env.context.types.find? x = some (.forAll [] xty)) :
    SourceTyResolves Env.context.aliases xty ty_res := by
  simp only [inferFVar, Bind.bind, Except.bind, h_ctx] at h
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind,
             LTy.resolveAliases, LTy.instantiate] at h
  elim_err h
  rename_i v_iwc heq_iwc
  obtain ⟨mty, Env_iwc⟩ := v_iwc
  elim_err heq_iwc
  rename_i v_ra heq_ra
  obtain ⟨mty_ra, Env_ra⟩ := v_ra
  have h_src : SourceTyResolves Env.context.aliases xty mty_ra :=
    LMonoTy.resolveAliases_sourceTyResolves xty _ mty_ra Env_ra heq_ra
  simp only at heq_iwc
  split at heq_iwc
  · simp at heq_iwc
  · split at heq_iwc
    · simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at heq_iwc
      obtain ⟨rfl, -⟩ := heq_iwc
      split at h
      · cases h; exact h_src
      · elim_errs h
        cases h; exact h_src
    · simp at heq_iwc


/-- Bundled well-formedness invariants for the output environment of
    `resolveAux`: well-formedness holds, types are non-empty, and aliases
    remain resolved. Context preservation is stated separately at each use
    site. -/
private structure ResolveAuxWF [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  (Env' : TEnv T.IDMeta) where
  envwf : TEnvWF Env'
  ne : Env'.context.types ≠ []
  resolved : TContext.AliasesResolved Env'.context

/-- If `ResolveAuxWF Env` holds and `resolveAux` succeeds, then
    `ResolveAuxWF Env'` holds for the output environment. -/
private theorem ResolveAuxWF.mk_from_resolveAux
  [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_wf : ResolveAuxWF Env)
    (h_fwf : FactorySigWF C.functions) :
    ResolveAuxWF Env' ∧ Env'.context.Equiv Env.context := by
  have h_ctx : Env'.context.Equiv Env.context :=
    resolveAux_context_equiv C e Env Env' et h_res h_wf.ne
  have h_resolved' : TContext.AliasesResolved Env'.context := by
    have h_al : Env'.context.aliases = Env.context.aliases := h_ctx.2
    intro a ha; rw [h_al] at ha ⊢; exact h_wf.resolved a ha
  exact ⟨⟨TEnvWF.of_resolveAux e et C Env Env' h_res h_wf.envwf h_wf.ne h_fwf h_ctx,
    h_ctx.symm.types_ne_nil h_wf.ne,
    h_resolved'⟩, h_ctx⟩

omit [Std.ToFormat T.IDMeta] in
/-- Transport an alias-free fact through a context-preserving step. -/
private theorem ResolveAuxWF.aliasFree_preserved
  [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Env' Env : TEnv T.IDMeta} (h_ctx : Env'.context.Equiv Env.context)
    {xty : LMonoTy} (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LMonoTy.aliasFree Env'.context.aliases xty :=
  h_ctx.2 ▸ h_af


/-- `resolveAux` annotates every free occurrence of a context variable `xv` declared at `xty` with
    the alias resolution `r` of `xty`. -/
private theorem resolveAux_allFvarAnnot_resolves
  [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (e : LExpr T.mono) (et : LExprT T.mono)
    (xv : T.Identifier) (xty r : LMonoTy)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_ctx : Env.context.types.find? xv = some (.forAll [] xty))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions)
    (h_rt : SourceTyResolves Env.context.aliases xty r) :
    LExprT.allFvarAnnot xv r et := by
  revert h_rt h_ctx r xty xv
  apply resolveAux_ind
    (P := fun e et _ Env _ => ∀ (xv : T.Identifier) (xty r : LMonoTy),
      Env.context.types.find? xv = some (.forAll [] xty) →
      SourceTyResolves Env.context.aliases xty r →
      LExprT.allFvarAnnot xv r et)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res h_envwf h_ne h_fwf xv xty r h_ctx h_rt
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    rename_i v1 h_ic; obtain ⟨ty, Env1⟩ := v1; simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_et, _⟩ := h_res; subst h_et
    simp [LExprT.allFvarAnnot]
  case h_op =>
    intro m o oty et C Env Env' h_res h_envwf h_ne h_fwf xv xty r h_ctx h_rt
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_errs h_res
    split at h_res
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et; simp [LExprT.allFvarAnnot]
    · elim_errs h_res
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et; simp [LExprT.allFvarAnnot]
  case h_fvar =>
    intro m x fty et C Env Env' h_res h_envwf h_ne h_fwf xv xty r h_ctx h_rt
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    rename_i v1 h_infer
    obtain ⟨ty_res, Env_res⟩ := v1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_res h_infer
    obtain ⟨h_et, h_env'⟩ := h_res
    subst h_et h_env'
    simp only [LExprT.allFvarAnnot]
    intro h_xeq
    subst h_xeq
    exact SourceTyResolves.unique
      (inferFVar_mono_resolves C Env x fty ty_res Env_res h_infer h_ctx) h_rt
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      h_res h1 h2 h_gen h_unify h_et _ _ _ _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2 xv xty r h_ctx h_rt
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ctx1' : Env1.context.types.find? xv = some (.forAll [] xty) := (h_ctx1.find? xv).trans h_ctx
    have h_rt1 : SourceTyResolves Env1.context.aliases xty r := h_ctx1.2 ▸ h_rt
    exact ⟨h_ih1 xv xty r h_ctx h_rt, h_ih2 xv xty r h_ctx1' h_rt1⟩
  case h_abs =>
    intro m name bty body et C Env Env' xvb xtyb Env1 et_body Env2
      h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_ih xv xty r h_ctx h_rt
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ne_xv : xv ≠ xvb := by
      intro heq; subst heq
      have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xtyb Env1 h_tbv
      have h_none := HMaps.find?_of_all_none Env.context.types xv h_fresh
      rw [h_ctx] at h_none; exact absurd h_none (by simp)
    have h_ctx1 := typeBoundVar_preserves_find C Env bty xvb xtyb Env1 h_tbv xv (.forAll [] xty) h_ne_xv h_ctx
    have h_rt1 : SourceTyResolves Env1.context.aliases xty r := h_aliases_eq ▸ h_rt
    have h_ih_body := h_ih xv xty r h_ctx1 h_rt1
    exact allFvarAnnot_varCloseT_ne xv xvb r 0 et_body h_ih_body
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xvb xtyb Env1 et_body Env2 et_tr Env3 substInfo
      h_res h_tbv h_res_body h_res_tr _ h_et _ _ h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr xv xty r h_ctx h_rt
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ne_xv : xv ≠ xvb := by
      intro heq; subst heq
      have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xtyb Env1 h_tbv
      have h_none := HMaps.find?_of_all_none Env.context.types xv h_fresh
      rw [h_ctx] at h_none; exact absurd h_none (by simp)
    have h_ctx1 := typeBoundVar_preserves_find C Env bty xvb xtyb Env1 h_tbv xv (.forAll [] xty) h_ne_xv h_ctx
    have h_rt1 : SourceTyResolves Env1.context.aliases xty r := h_aliases_eq ▸ h_rt
    have h_ctx2' : Env2.context.types.find? xv = some (.forAll [] xty) := (h_ctx2.find? xv).trans h_ctx1
    have h_rt2 : SourceTyResolves Env2.context.aliases xty r := h_ctx2.2 ▸ h_rt1
    have h_ih_b := h_ih_body xv xty r h_ctx1 h_rt1
    have h_ih_t := h_ih_tr xv xty r h_ctx2' h_rt2
    exact ⟨allFvarAnnot_varCloseT_ne xv xvb r 0 et_tr h_ih_t,
           allFvarAnnot_varCloseT_ne xv xvb r 0 et_body h_ih_b⟩
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      h_res h1 h2 h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2 xv xty r h_ctx h_rt
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ctx1' : Env1.context.types.find? xv = some (.forAll [] xty) := (h_ctx1.find? xv).trans h_ctx
    have h_rt1 : SourceTyResolves Env1.context.aliases xty r := h_ctx1.2 ▸ h_rt
    exact ⟨h_ih1 xv xty r h_ctx h_rt, h_ih2 xv xty r h_ctx1' h_rt1⟩
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      h_res hc ht he h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_envwf3 h_ctx3 h_ihc h_iht h_ihe xv xty r h_ctx h_rt
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ctx1' : Env1.context.types.find? xv = some (.forAll [] xty) := (h_ctx1.find? xv).trans h_ctx
    have h_rt1 : SourceTyResolves Env1.context.aliases xty r := h_ctx1.2 ▸ h_rt
    have h_ctx2' : Env2.context.types.find? xv = some (.forAll [] xty) := (h_ctx2.find? xv).trans h_ctx
    have h_rt2 : SourceTyResolves Env2.context.aliases xty r := h_ctx2.2 ▸ h_rt
    exact ⟨h_ihc xv xty r h_ctx h_rt, h_iht xv xty r h_ctx1' h_rt1, h_ihe xv xty r h_ctx2' h_rt2⟩

/-- `resolveAux` annotates every free occurrence of a context variable with its
    context type, when that type is alias-free. -/
theorem resolveAux_allFvarAnnot [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
  (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (e : LExpr T.mono) (et : LExprT T.mono)
    (xv : T.Identifier) (xty : LMonoTy)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_ctx : Env.context.types.find? xv = some (.forAll [] xty))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions)
    (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LExprT.allFvarAnnot xv xty et :=
  resolveAux_allFvarAnnot_resolves C Env Env' e et xv xty xty
    h_res h_ctx h_envwf h_ne h_fwf
    (LMonoTy.resolveAliases_sourceTyResolves xty Env xty Env
      (resolveAliases_aliasFree xty Env h_af))

omit [Std.ToFormat T.IDMeta] in
/-- Generalized `varCloseT` typing: if `et` is well-typed in context `Δ` and every
    free occurrence of `xv` carries annotation `t`, then closing `xv` at depth `k`
    gives a well-typed expression in `Δ ++ [t]`. -/
private theorem varCloseT_unresolved_HasTypeA_gen [DecidableEq T.IDMeta] (k : Nat) (Δ : List LMonoTy) (hk : Δ.length = k)
    (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono) (τ : LMonoTy)
    (h_typed : HasTypeA Δ et.unresolved τ)
    (h_annot : LExprT.allFvarAnnot xv t et) :
    HasTypeA (Δ ++ [t]) (LExpr.varCloseT k xv et).unresolved τ := by
  induction et generalizing Δ k τ with
  | fvar m x fty =>
    simp only [LExpr.varCloseT, LExprT.allFvarAnnot] at h_annot ⊢
    split
    · rename_i h_xeq
      simp only [unresolved] at h_typed ⊢
      have h_xeq' : x = xv := by
        simp [BEq.beq] at h_xeq; exact h_xeq.symm
      have h_ty_eq := h_annot h_xeq'
      cases h_typed
      rw [← h_ty_eq]
      apply HasTypeA.bvar
      rw [List.getElem?_append_right (by omega)]
      simp [hk]
    · simp only [unresolved] at h_typed ⊢
      exact HasTypeA_append_right h_typed [t]
  | const m c =>
    simp only [LExpr.varCloseT, unresolved] at h_typed ⊢
    exact HasTypeA_append_right h_typed [t]
  | op m o ty =>
    simp only [LExpr.varCloseT, unresolved] at h_typed ⊢
    exact HasTypeA_append_right h_typed [t]
  | bvar m i =>
    simp only [LExpr.varCloseT, unresolved] at h_typed ⊢
    exact HasTypeA_append_right h_typed [t]
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.varCloseT, unresolved, LExprT.allFvarAnnot] at h_typed h_annot ⊢
    cases h_typed with
    | app h_fn h_arg =>
      exact HasTypeA.app (ih1 _ _ hk _ h_fn h_annot.1) (ih2 _ _ hk _ h_arg h_annot.2)
  | abs m name bty body ih_body =>
    simp only [LExprT.allFvarAnnot] at h_annot
    simp only [LExpr.varCloseT]
    match h_isA : m.type.isArrow with
    | some (aty, _) =>
      unfold unresolved at h_typed ⊢
      rw [h_isA] at h_typed ⊢
      cases h_typed with
      | abs h_body_typed =>
        apply HasTypeA.abs
        have h_len : (aty :: Δ).length = k + 1 := by simp [hk]
        exact ih_body (k + 1) (aty :: Δ) h_len _ h_body_typed h_annot
    | none =>
      unfold unresolved at h_typed ⊢
      rw [h_isA] at h_typed ⊢
      simp only at h_typed ⊢
      cases bty with
      | none => cases h_typed
      | some aty =>
        cases h_typed with
        | abs h_body_typed =>
          apply HasTypeA.abs
          have h_len : (aty :: Δ).length = k + 1 := by simp [hk]
          exact ih_body (k + 1) (aty :: Δ) h_len _ h_body_typed h_annot
  | quant m qk name bty tr body ih_tr ih_body =>
    simp only [LExprT.allFvarAnnot] at h_annot
    simp only [LExpr.varCloseT, unresolved] at h_typed ⊢
    cases h_typed with
    | quant h_tr h_body =>
      rename_i τ_tr
      refine HasTypeA.quant (τ_tr := τ_tr) ?_ ?_
      · have h_len : (m.type :: Δ).length = k + 1 := by simp [hk]
        exact ih_tr (k + 1) (m.type :: Δ) h_len _ h_tr h_annot.1
      · have h_len : (m.type :: Δ).length = k + 1 := by simp [hk]
        exact ih_body (k + 1) (m.type :: Δ) h_len _ h_body h_annot.2
  | ite m c_e t_e e_e ih_c ih_t ih_e =>
    simp only [LExpr.varCloseT, unresolved, LExprT.allFvarAnnot] at h_typed h_annot ⊢
    cases h_typed with
    | ite h_c h_t h_e =>
      exact HasTypeA.ite (ih_c _ _ hk _ h_c h_annot.1) (ih_t _ _ hk _ h_t h_annot.2.1) (ih_e _ _ hk _ h_e h_annot.2.2)
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.varCloseT, unresolved, LExprT.allFvarAnnot] at h_typed h_annot ⊢
    cases h_typed with
    | eq h1 h2 =>
      exact HasTypeA.eq (ih1 _ _ hk _ h1 h_annot.1) (ih2 _ _ hk _ h2 h_annot.2)

omit [Std.ToFormat T.IDMeta] in
/-- Closing `xv` at depth `k` preserves typing with `toLMonoTy` as the result type,
    extending the bound-variable context by `[t]`. -/
theorem varCloseT_unresolved_HasTypeA [DecidableEq T.IDMeta] (k : Nat) (Δ : List LMonoTy) (hk : Δ.length = k)
    (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono)
    (h_typed : HasTypeA Δ et.unresolved (et.toLMonoTy))
    (h_annot : LExprT.allFvarAnnot xv t et) :
    HasTypeA (Δ ++ [t]) (LExpr.varCloseT k xv et).unresolved ((LExpr.varCloseT k xv et).toLMonoTy) := by
  rw [varCloseT_toLMonoTy]
  exact varCloseT_unresolved_HasTypeA_gen k Δ hk xv t et _ h_typed h_annot

omit [Std.ToFormat T.IDMeta] in
/-- Closing `xv` in a closed expression (empty bound-var context) yields a
    well-typed expression in context `[t]`. Used for the abs/quant cases. -/
theorem varCloseT_unresolved_HasTypeA_nil [DecidableEq T.IDMeta] (xv : T.Identifier) (t : LMonoTy) (et : LExprT T.mono)
    (h_typed : HasTypeA [] et.unresolved (et.toLMonoTy))
    (h_annot : LExprT.allFvarAnnot xv t et) :
    HasTypeA [t] (LExpr.varCloseT 0 xv et).unresolved ((LExpr.varCloseT 0 xv et).toLMonoTy) := by
  exact varCloseT_unresolved_HasTypeA 0 [] rfl xv t et h_typed h_annot

omit [Std.ToFormat T.IDMeta] in
/-- The context initialization in `resolve` (pushing an empty scope if types is
    empty) preserves `TEnvWF`. -/
theorem TEnvWF_resolve_init [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  (Env : TEnv T.IDMeta) (h_envwf : TEnvWF Env) :
    TEnvWF (if Env.context.types.isEmpty = true then
      Env.updateContext { Env.context with types := [.empty] }
    else Env) := by
  split
  · exact TEnvWF.updateContext_emptyScope Env h_envwf
  · exact h_envwf

/-- `TEnvWF` is preserved through `resolveAux`: the output environment is
    well-formed whenever the input is. -/
theorem resolveAux_TEnvWF [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions) :
    TEnvWF Env' := by
  exact TEnvWF.of_resolveAux e et C Env Env' h_res h_envwf h_ne h_fwf
    (resolveAux_context_equiv C e Env Env' et h_res h_ne)

/-- `TEnvWF` is preserved through `resolve`: the output environment is
    well-formed whenever the input is. -/
theorem resolve_TEnvWF [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactorySigWF C.functions) :
    TEnvWF Env' := by
  obtain ⟨Env0, etAux, h_res, -, h_wf_init, h_ne0, -⟩ :=
    resolve_resolveAux_init e e_typed C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  exact resolveAux_TEnvWF e etAux C Env0 Env' h_res h_envwf0 h_ne0 h_fwf

/-! ### Main induction -/

/-- Core soundness lemma: for any substitution `S` absorbing the output substitution,
    the resolved and substituted expression satisfies `HasTypeA`. Proved by
    well-founded induction on expression size. -/
private theorem resolveAux_HasTypeA_aux [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (S : Subst) (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    HasTypeA [] (applySubstT et S).unresolved ((applySubstT et S).toLMonoTy) := by
  revert h_absorbs S h_resolved
  apply resolveAux_ind
    (P := fun e et _C Env Env' => TContext.AliasesResolved Env.context →
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst →
        HasTypeA [] (applySubstT et S).unresolved ((applySubstT et S).toLMonoTy))
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h h_envwf h_ne h_fwf h_resolved S h_absorbs
    simp only [resolveAux, inferConst, Bind.bind, Except.bind] at h
    elim_err h
    have heq := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨h_et, h_env⟩ := heq
    subst h_et h_env
    simp only [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    rename_i heq_inferConst
    split at heq_inferConst
    · simp only [Except.ok.injEq] at heq_inferConst ⊢
      rw [← heq_inferConst]
      simp only
      rw [LConst.ty_subst]
      exact HasTypeA.const
    · simp at heq_inferConst
  case h_op =>
    intro m o oty et C Env Env' h h_envwf h_ne h_fwf h_resolved S h_absorbs
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    split at h
    · cases h
      simp only [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
    · elim_errs h
      cases h
      simp only [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
  case h_fvar =>
    intro m x fty et C Env Env' h h_envwf h_ne h_fwf h_resolved S h_absorbs
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i ty_env h_infer
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, h_env⟩ := h
    subst h_et h_env
    simp only [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    exact HasTypeA.fvar
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      h_res h1 h2 h_gen h_unify h_et h_subeq h_abs_rem_e1 h_abs_rem_e2
      h_e1t_no_fresh h_e2t_no_fresh h_unify_eq
      h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_ih1 h_ih2 h_resolved S h_absorbs
    subst h_et
    rw [h_subeq] at h_absorbs
    have h_abs_S_rem := h_absorbs
    have h_abs_e2 : S.absorbs Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_rem_e2 h_abs_S_rem
    have h_abs_e1 : S.absorbs Env1.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_rem_e1 h_abs_S_rem
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_ctx1.2] at h_mem ⊢; exact h_resolved a h_mem
    have h_subst_e1t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e1t.toLMonoTy) =
        LMonoTy.subst S e1t.toLMonoTy := by
      rw [← LMonoTy.subst_remove_not_fv substInfo.subst fresh_name
            e1t.toLMonoTy h_e1t_no_fresh]
      exact LMonoTy.subst_absorbs S (HMaps.remove substInfo.subst fresh_name)
        e1t.toLMonoTy h_abs_S_rem
    have h_subst_e2t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e2t.toLMonoTy) =
        LMonoTy.subst S e2t.toLMonoTy := by
      rw [← LMonoTy.subst_remove_not_fv substInfo.subst fresh_name
            e2t.toLMonoTy h_e2t_no_fresh]
      exact LMonoTy.subst_absorbs S (HMaps.remove substInfo.subst fresh_name)
        e2t.toLMonoTy h_abs_S_rem
    have h_eq_S : LMonoTy.subst S e1t.toLMonoTy =
        LMonoTy.tcons "arrow"
          [LMonoTy.subst S e2t.toLMonoTy,
           LMonoTy.subst S (LMonoTy.subst substInfo.subst (.ftvar fresh_name))] := by
      have h_congr := congrArg (LMonoTy.subst S) h_unify_eq
      rw [h_subst_e1t] at h_congr
      rw [LMonoTy.subst_tcons_pair substInfo.subst "arrow"
            e2t.toLMonoTy (.ftvar fresh_name)] at h_congr
      rw [LMonoTy.subst_tcons_pair S "arrow"
            (LMonoTy.subst substInfo.subst e2t.toLMonoTy)
            (LMonoTy.subst substInfo.subst (.ftvar fresh_name))] at h_congr
      rw [h_subst_e2t] at h_congr
      exact h_congr
    have h_ih_e1 := h_ih1 h_resolved S h_abs_e1
    have h_ih_e2 := h_ih2 h_resolved1 S h_abs_e2
    simp only [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    rw [applySubstT_toLMonoTy] at h_ih_e1 h_ih_e2
    rw [h_eq_S] at h_ih_e1
    exact HasTypeA.app h_ih_e1 h_ih_e2
  case h_abs =>
    intro m name bty body et C Env Env' xv xty Env1 et_body Env2
      h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_ih h_resolved S h_absorbs
    subst h_et h_env'
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_aliases_eq] at h_mem ⊢; exact h_resolved a h_mem
    have h_abs_Env2 : S.absorbs Env2.stateSubstInfo.subst := by
      simp only [TEnv.eraseFromContext, TEnv.updateContext] at h_absorbs
      exact h_absorbs
    have h_ih_body := h_ih h_resolved1 S h_abs_Env2
    show HasTypeA []
      (applySubstT (.abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
        (LMonoTy.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])⟩
        name bty (LExpr.varCloseT 0 xv et_body)) S).unresolved
      ((applySubstT (.abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
        (LMonoTy.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])⟩
        name bty (LExpr.varCloseT 0 xv et_body)) S).toLMonoTy)
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
      typeBoundVar_adds_to_context C Env bty xv xty Env1 h_tbv
    have h_xty_af : LMonoTy.aliasFree Env1.context.aliases xty := by
      rw [h_aliases_eq]; exact typeBoundVar_xty_aliasFree C Env bty xv xty Env1 h_tbv h_resolved
    have h_annot_raw : LExprT.allFvarAnnot xv xty et_body :=
      resolveAux_allFvarAnnot C Env1 Env2
        (LExpr.varOpen 0 (xv, some xty) body) et_body xv xty h_res_body h_ctx_xv
        h_envwf1 h_ne1 h_fwf h_xty_af
    have h_annot : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_body S) :=
      applySubstT_allFvarAnnot xv xty et_body S h_annot_raw
    exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
      (applySubstT et_body S) h_ih_body h_annot
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3 substInfo
      h_res h_tbv h_res_body h_res_tr h_unify h_et h_env' h_abs32 h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr h_resolved S h_absorbs
    subst h_et h_env'
    have h_ne2 : Env2.context.types ≠ [] := h_ctx2.symm.types_ne_nil h_ne1
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_aliases_eq] at h_mem ⊢; exact h_resolved a h_mem
    have h_resolved2 : TContext.AliasesResolved Env2.context := by
      intro a h_mem; rw [h_ctx2.2] at h_mem ⊢; exact h_resolved1 a h_mem
    have h_abs_sub : S.absorbs substInfo.subst := by
      simp only [TEnv.eraseFromContext, TEnv.updateContext, TEnv.updateSubst] at h_absorbs
      exact h_absorbs
    have h_abs_Env3 : S.absorbs Env3.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ h_unify) h_abs_sub
    have h_abs_Env2 : S.absorbs Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs32 h_abs_Env3
    have h_ih_b := h_ih_body h_resolved1 S h_abs_Env2
    have h_ih_t := h_ih_tr h_resolved2 S h_abs_Env3
    show HasTypeA []
      (applySubstT (.quant ⟨m, LMonoTy.subst substInfo.subst xty⟩
        qk name (some (LMonoTy.subst substInfo.subst xty))
        (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body)) S).unresolved
      ((applySubstT (.quant ⟨m, LMonoTy.subst substInfo.subst xty⟩
        qk name (some (LMonoTy.subst substInfo.subst xty))
        (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body)) S).toLMonoTy)
    simp only [toLMonoTy]
    simp only [applySubstT, replaceMetadata, unresolved]
    change HasTypeA []
      (.quant m qk name (some (LMonoTy.subst S (LMonoTy.subst substInfo.subst xty)))
        (applySubstT (LExpr.varCloseT 0 xv et_tr) S).unresolved
        (applySubstT (LExpr.varCloseT 0 xv et_body) S).unresolved)
      LMonoTy.bool
    rw [applySubstT_varCloseT_comm (xv := xv) (et := et_tr),
        applySubstT_varCloseT_comm (xv := xv) (et := et_body)]
    rw [LMonoTy.subst_absorbs S substInfo.subst xty h_abs_sub]
    refine HasTypeA.quant (τ_tr := (LExpr.varCloseT 0 xv (applySubstT et_tr S)).toLMonoTy) ?_ ?_
    · have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
        typeBoundVar_adds_to_context C Env bty xv xty Env1 h_tbv
      have h_ctx_xv2 : Env2.context.types.find? xv = some (.forAll [] xty) :=
        (h_ctx2.find? xv).trans h_ctx_xv
      have h_xty_af2 : LMonoTy.aliasFree Env2.context.aliases xty := by
        rw [h_ctx2.2, h_aliases_eq]
        exact typeBoundVar_xty_aliasFree C Env bty xv xty Env1 h_tbv h_resolved
      have h_annot_tr_raw : LExprT.allFvarAnnot xv xty et_tr :=
        resolveAux_allFvarAnnot C Env2 Env3
          (LExpr.varOpen 0 (xv, some xty) triggers) et_tr xv xty h_res_tr h_ctx_xv2
          h_envwf2 h_ne2 h_fwf h_xty_af2
      have h_annot_tr : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_tr S) :=
        applySubstT_allFvarAnnot xv xty et_tr S h_annot_tr_raw
      exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
        (applySubstT et_tr S) h_ih_t h_annot_tr
    · have h_body_ty_bool : LMonoTy.subst S et_body.toLMonoTy = LMonoTy.bool := by
        have h_eq := unify_makes_equal et_body.toLMonoTy LMonoTy.bool
          Env3.stateSubstInfo substInfo h_unify
        have h := congrArg (LMonoTy.subst S) h_eq
        rw [LMonoTy.subst_absorbs S substInfo.subst _ h_abs_sub,
            LMonoTy.subst_absorbs S substInfo.subst _ h_abs_sub,
            LMonoTy.subst_bool] at h
        exact h
      have h_body_ty_eq : (LExpr.varCloseT 0 xv (applySubstT et_body S)).toLMonoTy = LMonoTy.bool := by
        rw [varCloseT_toLMonoTy, applySubstT_toLMonoTy, h_body_ty_bool]
      rw [← h_body_ty_eq]
      have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
        typeBoundVar_adds_to_context C Env bty xv xty Env1 h_tbv
      have h_xty_af1 : LMonoTy.aliasFree Env1.context.aliases xty := by
        rw [h_aliases_eq]
        exact typeBoundVar_xty_aliasFree C Env bty xv xty Env1 h_tbv h_resolved
      have h_annot_body_raw : LExprT.allFvarAnnot xv xty et_body :=
        resolveAux_allFvarAnnot C Env1 Env2
          (LExpr.varOpen 0 (xv, some xty) body) et_body xv xty h_res_body h_ctx_xv
          h_envwf1 h_ne1 h_fwf h_xty_af1
      have h_annot_body : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_body S) :=
        applySubstT_allFvarAnnot xv xty et_body S h_annot_body_raw
      exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
        (applySubstT et_body S) h_ih_b h_annot_body
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      h_res h1 h2 h_unify h_et h_subeq h_abs1 h_abs2 h_envwf h_ne h_fwf
      h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_ih1 h_ih2 h_resolved S h_absorbs
    subst h_et
    rw [h_subeq] at h_absorbs
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_ctx1.2] at h_mem ⊢; exact h_resolved a h_mem
    have h_abs_unify := Constraints.unify_absorbs _ _ _ h_unify
    have h_abs_e2 : S.absorbs Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_unify h_absorbs
    have h_abs_e1 : S.absorbs Env1.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs2 h_abs_e2
    have h_eq_types : toLMonoTy (applySubstT e1t S) = toLMonoTy (applySubstT e2t S) := by
      rw [applySubstT_toLMonoTy, applySubstT_toLMonoTy]
      have h_sound := Constraints.unify_sound _ _ _ h_unify
      have h_pair := h_sound _ (List.Mem.head _)
      simp only at h_pair
      exact LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_absorbs h_pair
    simp only [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    rw [LMonoTy.subst_bool]
    apply HasTypeA.eq (τ := toLMonoTy (applySubstT e1t S))
    · exact h_ih1 h_resolved S h_abs_e1
    · rw [h_eq_types]
      exact h_ih2 h_resolved1 S h_abs_e2
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      h_res hc ht he h_unify h_et h_subeq h_abs_th2 h_abs_el3 h_envwf h_ne h_fwf
      h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_envwf3 h_ctx3 h_ihc h_iht h_ihe h_resolved S h_absorbs
    subst h_et
    rw [h_subeq] at h_absorbs
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_ctx1.2] at h_mem ⊢; exact h_resolved a h_mem
    have h_resolved2 : TContext.AliasesResolved Env2.context := by
      intro a h_mem; rw [h_ctx2.2] at h_mem ⊢; exact h_resolved a h_mem
    have h_abs_unify := Constraints.unify_absorbs _ _ _ h_unify
    have h_abs_el : S.absorbs Env3.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_unify h_absorbs
    have h_abs_th : S.absorbs Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_el3 h_abs_el
    have h_abs_c : S.absorbs Env1.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_th2 h_abs_th
    have h_sound := Constraints.unify_sound _ _ _ h_unify
    have h_c_bool : LMonoTy.subst substInfo.subst ct.toLMonoTy = LMonoTy.bool := by
      have h_p := h_sound _ (List.Mem.head _)
      simp only [LMonoTy.subst_bool] at h_p; exact h_p
    have h_th_el : LMonoTy.subst substInfo.subst tht.toLMonoTy =
        LMonoTy.subst substInfo.subst elt.toLMonoTy := by
      have h_p := h_sound _ (List.Mem.tail _ (List.Mem.head _))
      simp only at h_p; exact h_p
    have h_c_type_bool : LMonoTy.subst S (toLMonoTy ct) = LMonoTy.bool := by
      have h_c_bool' : LMonoTy.subst substInfo.subst ct.toLMonoTy =
          LMonoTy.subst substInfo.subst LMonoTy.bool := by
        rw [h_c_bool, LMonoTy.subst_bool]
      have h_lifted := LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_absorbs h_c_bool'
      rw [LMonoTy.subst_bool] at h_lifted; exact h_lifted
    have h_th_el_eq : LMonoTy.subst S (toLMonoTy tht) = LMonoTy.subst S (toLMonoTy elt) :=
      LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_absorbs h_th_el
    change HasTypeA [] (LExpr.ite m (applySubstT ct S).unresolved
      (applySubstT tht S).unresolved (applySubstT elt S).unresolved)
      (LMonoTy.subst S (toLMonoTy tht))
    rw [← applySubstT_toLMonoTy tht S]
    apply HasTypeA.ite
    · have h_ih_c := h_ihc h_resolved S h_abs_c
      rw [applySubstT_toLMonoTy, h_c_type_bool] at h_ih_c
      exact h_ih_c
    · exact h_iht h_resolved1 S h_abs_th
    · have h_ih_el := h_ihe h_resolved2 S h_abs_el
      rw [applySubstT_toLMonoTy] at h_ih_el
      rw [applySubstT_toLMonoTy, h_th_el_eq]
      exact h_ih_el

/-- When `resolveAux` succeeds, applying the final substitution and erasing metadata
    produces a well-typed and well-annotated expression according to `HasTypeA`. -/
theorem resolveAux_HasTypeA [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono) (Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    HasTypeA [] (applySubstT et Env'.stateSubstInfo.subst).unresolved
               ((applySubstT et Env'.stateSubstInfo.subst).toLMonoTy) := by
  have h_absorbs := Subst.absorbs_refl Env'.stateSubstInfo.subst Env'.stateSubstInfo.isWF
  exact resolveAux_HasTypeA_aux e et C Env Env' h h_envwf h_ne h_fwf h_resolved
    Env'.stateSubstInfo.subst h_absorbs

/-- Applying any substitution that absorbs the resolver's final substitution to its output keeps
    that output annotated-typable at its substituted type. -/
theorem resolve_HasTypeA_subst [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env : TEnv T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = Except.ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (S : Subst) (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    HasTypeA [] (applySubstT e_typed S).unresolved ((applySubstT e_typed S).toLMonoTy) := by
  obtain ⟨Env0, etAux, h_res, h_et, h_wf_init, h_ne0, -, h_Env0⟩ :=
    resolve_resolveAux_init e e_typed C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  have h_resolved0 : Env0.context.AliasesResolved := by
    rw [h_Env0]
    split
    · intro a h_mem
      simp only [TEnv.updateContext, TEnv.context] at h_mem ⊢
      exact h_resolved a h_mem
    · exact h_resolved
  have hcore := resolveAux_HasTypeA_aux e etAux C Env0 Env' h_res h_envwf0 h_ne0 h_fwf
    h_resolved0 S h_absorbs
  rw [← h_et, applySubstT_absorbs S Env'.stateSubstInfo.subst h_absorbs]
  exact hcore

/-- Main soundness theorem: `LExpr.resolve` produces a well-typed and
    well-annotated `LExprT` according to `HasTypeA`. Unlike `resolve_HasType`,
    this does not require `WellScoped` or `checkContextTypesClosed`, only
    `AliasesResolved`. The trade-off is that it proves annotation-consistency
    (`HasTypeA`) rather than full polymorphic typing (`HasType`). -/
theorem resolve_HasTypeA [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env : TEnv T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = Except.ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] e_typed.unresolved (e_typed.toLMonoTy) := by
  obtain ⟨-, etAux, -, h_et, -⟩ :=
    resolve_resolveAux_init e e_typed C Env Env' h
  have h_absorbs := Subst.absorbs_refl Env'.stateSubstInfo.subst Env'.stateSubstInfo.isWF
  have h_idem : applySubstT e_typed Env'.stateSubstInfo.subst = e_typed := by
    rw [← h_et, applySubstT_absorbs _ _ h_absorbs]
  have h_sub := resolve_HasTypeA_subst e e_typed C Env Env' h h_envwf h_fwf h_resolved
    Env'.stateSubstInfo.subst h_absorbs
  rw [h_idem] at h_sub
  exact h_sub

/-! ### Stored binder annotations are registered types -/

/-- Every binder annotation `resolveAux` stores is registered after any substitution that absorbs
    the resolver's and has a registered range. -/
private theorem resolveAux_binderAnnotations_known
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactorySigWF C.functions) :
    ∀ S : Subst, Subst.absorbs S Env'.stateSubstInfo.subst → Subst.RangeKnown S C.knownTypes →
      ∀ t ∈ LExpr.binderAnnotations (LExpr.unresolved (LExpr.applySubstT et S)),
        t.knownInstance C.knownTypes = true := by
  apply resolveAux_ind
    (P := fun _ et (C : LContext T) _ Env' => ∀ S : Subst,
      Subst.absorbs S Env'.stateSubstInfo.subst → Subst.RangeKnown S C.knownTypes →
      ∀ t ∈ LExpr.binderAnnotations (LExpr.unresolved (LExpr.applySubstT et S)),
        t.knownInstance C.knownTypes = true)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res _ _ _ _ _ _
    obtain ⟨-, -, rfl, -⟩ := LExpr.resolveAux_const_shape C Env Env' m c et h_res
    simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.binderAnnotations]
  case h_op =>
    intro m o oty et C Env Env' h_res _ _ _ _ _ _
    obtain ⟨-, -, ty, -, -, -, -, rfl, -⟩ := LExpr.resolveAux_op_shape C Env Env' m o oty et h_res
    simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.binderAnnotations]
  case h_fvar =>
    intro m x fty et C Env Env' h_res _ _ _ _ _ _
    obtain ⟨ty, -, rfl⟩ := LExpr.resolveAux_fvar_shape C Env Env' m x fty et h_res
    simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.binderAnnotations]
  case h_app =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ hEt hSubst hAbs1 hAbs2 _ _ _
      _ _ _ _ _ _ _ ih1 ih2 S hAbs hRK
    subst hEt
    rw [hSubst] at hAbs
    have h1 := ih1 S (Subst.absorbs_trans _ _ _ hAbs1 hAbs) hRK
    have h2 := ih2 S (Subst.absorbs_trans _ _ _ hAbs2 hAbs) hRK
    simp only [LExpr.applySubstT, LExpr.replaceMetadata] at h1 h2 ⊢
    simp only [LExpr.unresolved, LExpr.binderAnnotations, List.mem_append]
    intro t ht
    rcases ht with ht | ht
    · exact h1 t ht
    · exact h2 t ht
  case h_abs =>
    intro m name annotation _ _ C Env _ xv xty Env1 bodyT Env2
      _ hBound _ hEt hEnv' _ _ _ _ _ _ ih S hAbs hRK
    subst hEt
    subst hEnv'
    have hAbs2 : Subst.absorbs S Env2.stateSubstInfo.subst := by
      simpa [TEnv.eraseFromContext, TEnv.updateContext] using hAbs
    have hArrowSubst :
        LMonoTy.subst S
            (LMonoTy.subst Env2.stateSubstInfo.subst
              (.arrow xty (LExpr.varCloseT 0 xv bodyT).toLMonoTy)) =
          .arrow (LMonoTy.subst S xty) (LMonoTy.subst S bodyT.toLMonoTy) := by
      rw [varCloseT_toLMonoTy, LMonoTy.subst_absorbs S Env2.stateSubstInfo.subst _ hAbs2,
        LMonoTy.arrow, LMonoTy.arrow, LMonoTy.subst_tcons_pair]
    have hStoredAbs :
        LExpr.unresolved (LExpr.applySubstT
          (.abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
            (.arrow xty (LExpr.varCloseT 0 xv bodyT).toLMonoTy)⟩
            name annotation (LExpr.varCloseT 0 xv bodyT)) S) =
          .abs m name (some (LMonoTy.subst S xty))
            (LExpr.unresolved (LExpr.applySubstT (LExpr.varCloseT 0 xv bodyT) S)) := by
      simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
      rw [hArrowSubst]
      simp only [LMonoTy.arrow, LMonoTy.isArrow]
    have hkn : LMonoTy.knownInstance (LMonoTy.subst S xty) C.knownTypes = true :=
      knownInstance_subst C.knownTypes S xty hRK
        (LExpr.typeBoundVar_subst_knownInstance C Env annotation xv xty Env1 hBound).2
    change ∀ t ∈ LExpr.binderAnnotations (LExpr.unresolved (LExpr.applySubstT
        (.abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
          (.arrow xty (LExpr.varCloseT 0 xv bodyT).toLMonoTy)⟩
          name annotation (LExpr.varCloseT 0 xv bodyT)) S)), _
    rw [hStoredAbs, applySubstT_varCloseT_comm]
    intro t ht
    simp only [LExpr.binderAnnotations, Option.toList, List.cons_append, List.nil_append,
      List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hkn
    · rw [LExpr.Proofs.binderAnnotations_unresolved_varCloseT] at ht
      exact ih S hAbs2 hRK t ht
  case h_quant =>
    intro m kind name annotation _ _ _ C Env _ xv xty Env1 bodyT Env2
      triggerT Env3 substInfo _ hBound _ _ hUnify hEt hEnv' hAbs32
      _ _ _ _ _ _ _ _ ihBody ihTrigger S hAbs hRK
    subst hEt
    subst hEnv'
    have hAbsSubst : Subst.absorbs S substInfo.subst := by
      simpa [TEnv.eraseFromContext, TEnv.updateContext, TEnv.updateSubst] using hAbs
    have hAbs3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hUnify) hAbsSubst
    have hAbs2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ hAbs32 hAbs3
    have hXty : LMonoTy.subst S (LMonoTy.subst substInfo.subst xty) = LMonoTy.subst S xty :=
      LMonoTy.subst_absorbs S substInfo.subst xty hAbsSubst
    have hkn : LMonoTy.knownInstance (LMonoTy.subst S xty) C.knownTypes = true :=
      knownInstance_subst C.knownTypes S xty hRK
        (LExpr.typeBoundVar_subst_knownInstance C Env annotation xv xty Env1 hBound).2
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
    rw [hXty]
    change ∀ t ∈ LExpr.binderAnnotations
      (.quant m kind name (some (LMonoTy.subst S xty))
        (LExpr.unresolved (LExpr.applySubstT (LExpr.varCloseT 0 xv triggerT) S))
        (LExpr.unresolved (LExpr.applySubstT (LExpr.varCloseT 0 xv bodyT) S))), _
    rw [applySubstT_varCloseT_comm, applySubstT_varCloseT_comm]
    intro t ht
    simp only [LExpr.binderAnnotations, Option.toList, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_append] at ht
    rw [LExpr.Proofs.binderAnnotations_unresolved_varCloseT,
      LExpr.Proofs.binderAnnotations_unresolved_varCloseT] at ht
    rcases ht with rfl | ht | ht
    · exact hkn
    · exact ihTrigger S hAbs3 hRK t ht
    · exact ihBody S hAbs2 hRK t ht
  case h_eq =>
    intro _ _ _ _ _ _ _ _ _ _ Env2 _
      _ _ _ hUnify hEt hSubst _ hAbs2 _ _ _
      _ _ _ _ ih1 ih2 S hAbs hRK
    subst hEt
    rw [hSubst] at hAbs
    have hAbs2S : Subst.absorbs S Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hUnify) hAbs
    have h1 := ih1 S (Subst.absorbs_trans _ _ _ hAbs2 hAbs2S) hRK
    have h2 := ih2 S hAbs2S hRK
    simp only [LExpr.applySubstT, LExpr.replaceMetadata] at h1 h2 ⊢
    simp only [LExpr.unresolved, LExpr.binderAnnotations, List.mem_append]
    intro t ht
    rcases ht with ht | ht
    · exact h1 t ht
    · exact h2 t ht
  case h_ite =>
    intro _ _ _ _ _ _ _ _ _ _ _ Env2 _ Env3
      _ _ _ _ _ hUnify hEt hSubst hAbs12 hAbs23
      _ _ _ _ _ _ _ _ _ ihCond ihThen ihElse S hAbs hRK
    subst hEt
    rw [hSubst] at hAbs
    have hAbs3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hUnify) hAbs
    have hAbs2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ hAbs23 hAbs3
    have hc := ihCond S (Subst.absorbs_trans _ _ _ hAbs12 hAbs2) hRK
    have ht := ihThen S hAbs2 hRK
    have he := ihElse S hAbs3 hRK
    simp only [LExpr.applySubstT, LExpr.replaceMetadata] at hc ht he ⊢
    simp only [LExpr.unresolved, LExpr.binderAnnotations, List.mem_append]
    intro t htm
    rcases htm with (htm | htm) | htm
    · exact hc t htm
    · exact ht t htm
    · exact he t htm

/-- Every binder annotation `LExpr.resolve` stores is registered after any substitution that
    absorbs the resolver's and has a registered range. -/
theorem resolve_binderAnnotations_known [ToString T.IDMeta]
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) :
    ∀ S : Subst, Subst.absorbs S Env'.stateSubstInfo.subst → Subst.RangeKnown S C.knownTypes →
      ∀ t ∈ LExpr.binderAnnotations (LExpr.unresolved (LExpr.applySubstT et S)),
        t.knownInstance C.knownTypes = true := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, -, -⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  intro S hAbs hRK
  rw [← h_et, applySubstT_absorbs S Env'.stateSubstInfo.subst hAbs et_aux]
  exact resolveAux_binderAnnotations_known C Env0 Env' e et_aux h_res h_envwf0 h_ne0
    h_fwf S hAbs hRK


/-! ### Free-variable and operator annotations of the resolver's output -/

omit [Std.ToFormat T.IDMeta] in
/-- If every free occurrence of `x` in `et` carries type `t`, every annotation of `x` in the erased
    expression is `t`. -/
private theorem fvarAnnot_eq_of_allFvarAnnot [DecidableEq T.IDMeta]
    (x : T.Identifier) (t : LMonoTy) :
    ∀ et : LExprT T.mono, LExprT.allFvarAnnot x t et →
      ∀ ann, (x, some ann) ∈ LExpr.freeVars (LExpr.unresolved et) → ann = t := by
  intro et
  induction et with
  | const m c => intro _ ann hmem; simp [LExpr.unresolved, LExpr.freeVars] at hmem
  | op m o ty => intro _ ann hmem; simp [LExpr.unresolved, LExpr.freeVars] at hmem
  | bvar m i => intro _ ann hmem; simp [LExpr.unresolved, LExpr.freeVars] at hmem
  | fvar m y yty =>
    intro h ann hmem
    simp only [LExpr.unresolved, LExpr.freeVars, List.mem_singleton, Prod.mk.injEq,
      Option.some.injEq] at hmem
    obtain ⟨hxy, hann⟩ := hmem
    rw [hann]
    exact h hxy.symm
  | abs m name ty body ih =>
    intro h ann hmem
    unfold LExpr.unresolved at hmem
    split at hmem <;> exact ih h ann hmem
  | quant m qk name ty tr body ihtr ih =>
    intro h ann hmem
    simp only [LExpr.unresolved, LExpr.freeVars, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ihtr h.1 ann hmem
    · exact ih h.2 ann hmem
  | app m fn arg ihfn iharg =>
    intro h ann hmem
    simp only [LExpr.unresolved, LExpr.freeVars, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ihfn h.1 ann hmem
    · exact iharg h.2 ann hmem
  | ite m c t f ihc iht ihf =>
    intro h ann hmem
    simp only [LExpr.unresolved, LExpr.freeVars, List.mem_append] at hmem
    rcases hmem with (hmem | hmem) | hmem
    · exact ihc h.1 ann hmem
    · exact iht h.2.1 ann hmem
    · exact ihf h.2.2 ann hmem
  | eq m e1 e2 ih1 ih2 =>
    intro h ann hmem
    simp only [LExpr.unresolved, LExpr.freeVars, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ih1 h.1 ann hmem
    · exact ih2 h.2 ann hmem

omit [Std.ToFormat T.IDMeta] in
/-- On a context with a binding, `resolve` starts `resolveAux` from that context unchanged. -/
private theorem resolve_init_eq_of_find [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Env : TEnv T.IDMeta) {x : T.Identifier} {sch : LTy}
    (h_ctx : Env.context.types.find? x = some sch) :
    (if Env.context.types.isEmpty = true then
      Env.updateContext { Env.context with types := [.empty] }
    else Env) = Env := by
  cases h_types : Env.context.types with
  | nil => rw [h_types] at h_ctx; simp [HMaps.find?] at h_ctx
  | cons _ _ => rfl

/-- In the output of `LExpr.resolve`, after any substitution `S` absorbing the resolver's, every
    annotation of a variable declared at `∀[]. ty0` in the input context is `S` applied to the alias
    resolution of `ty0`. -/
private theorem resolve_fvarAnnot_eq [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (S : Subst) (h_abs : Subst.absorbs S Env'.stateSubstInfo.subst)
    {x : T.Identifier} {ty0 r ann : LMonoTy}
    (h_ctx : Env.context.types.find? x = some (.forAll [] ty0))
    (h_rt : SourceTyResolves Env.context.aliases ty0 r)
    (h_mem : (x, some ann) ∈ LExpr.freeVars (LExpr.unresolved (LExpr.applySubstT et S))) :
    ann = LMonoTy.subst S r := by
  obtain ⟨Env0, et_aux, h_res, h_et, -, h_ne0, -, h_Env0⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  rw [resolve_init_eq_of_find Env h_ctx] at h_Env0
  subst h_Env0
  rw [← h_et, applySubstT_absorbs S Env'.stateSubstInfo.subst h_abs et_aux] at h_mem
  have h_ann := resolveAux_allFvarAnnot_resolves C Env0 Env' e et_aux x ty0 r h_res h_ctx h_envwf
    h_ne0 h_fwf h_rt
  exact fvarAnnot_eq_of_allFvarAnnot x _ _ (applySubstT_allFvarAnnot x r et_aux S h_ann) ann h_mem

/-- Under a substitution `S` absorbing the resolver's, every annotated free variable of
    `LExpr.resolve`'s output is declared in the alias-resolved monomorphic input context at a type
    `S` sends to its annotation. -/
theorem resolve_fvarAnnots_agree [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) (h_mono : MonoScope Env.context)
    (S : Subst) (h_abs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    ∀ x ann, (x, some ann) ∈ LExpr.freeVars (LExpr.unresolved (LExpr.applySubstT et S)) →
      ∃ ty, Env.context.resolveTypes.types.find? x = some (.forAll [] ty) ∧
        ann = LMonoTy.subst S ty := by
  intro x ann h_mem
  obtain ⟨sch, h_sch⟩ := resolve_fvar_declared C Env Env' e et h h_envwf h_fwf S h_mem
  obtain ⟨ty, rfl⟩ := MonoScope.find?_forAll h_mono h_sch
  exact ⟨Env.context.resolveTy ty, TContext.resolveTypes_find? h_sch,
    resolve_fvarAnnot_eq C Env Env' e et h h_envwf h_fwf S h_abs h_sch
      (TContext.resolveTy_sourceTyResolves Env.context ty) h_mem⟩

/-! ### Operator annotations instantiate factory signatures -/

/-- Every operator annotation in the output of `resolveAux` is an instance of the body of its
    function's type scheme, with the aliases of the input context resolved. -/
private theorem resolveAux_opAnnots [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactorySigWF C.functions) :
    ∀ o ty, (o, ty) ∈ LExpr.opAnnots (unresolved et) →
      ∃ f xs body, C.functions[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ (Env.context.resolveTy body) := by
  apply resolveAux_ind
    (P := fun _ et (C : LContext T) Env _ => ∀ o ty, (o, ty) ∈ LExpr.opAnnots (unresolved et) →
      ∃ f xs body, C.functions[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ (Env.context.resolveTy body))
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res _ _ _ o ty ho
    obtain ⟨-, -, rfl, -⟩ := LExpr.resolveAux_const_shape C Env Env' m c et h_res
    simp [unresolved, LExpr.opAnnots] at ho
  case h_op =>
    intro m o oty et C Env Env' h_res h_wf _ _ o' ty' ho
    obtain ⟨func, ⟨xs, body⟩, ty, Env_x, hfunc, htype, hiwc, rfl, -⟩ :=
      LExpr.resolveAux_op_shape C Env Env' m o oty et h_res
    simp only [unresolved, LExpr.opAnnots, Option.toList_some, List.map_cons, List.map_nil,
      List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    obtain ⟨τ, hτ⟩ := LTy.instantiateWithCheck_eq_subst_resolveTy C Env Env_x hiwc h_wf.aliasesWF
    exact ⟨func, xs, body, hfunc, htype, τ, hτ⟩
  case h_fvar =>
    intro m x fty et C Env Env' h_res _ _ _ o ty ho
    obtain ⟨ty, Env_x, rfl⟩ := LExpr.resolveAux_fvar_shape C Env Env' m x fty et h_res
    simp [unresolved, LExpr.opAnnots] at ho
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 freshName EnvGen substInfo
      hRes hRes1 hRes2 hGen hUnify hEt _ _ _ _ _ _ _ _ _ _ h_ctx1 _ _ ih1 ih2 o ty ho
    subst hEt
    rw [TContext.resolveTy_congr h_ctx1.2] at ih2
    simp only [unresolved, LExpr.opAnnots, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ih1 o ty ho
    · exact ih2 o ty ho
  case h_abs =>
    intro m name annotation body et C Env Env' xv xty Env1 bodyT Env2
      hRes hBound hBody hEt hEnv' _ _ _ _ _ h_aliases ih o ty ho
    subst hEt
    rw [TContext.resolveTy_congr h_aliases] at ih
    have hbody : LExpr.opAnnots (unresolved (.abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
        (.tcons "arrow" [xty, (LExpr.varCloseT 0 xv bodyT).toLMonoTy])⟩
        name annotation (LExpr.varCloseT 0 xv bodyT))) =
        LExpr.opAnnots (unresolved (LExpr.varCloseT 0 xv bodyT)) := by
      simp only [unresolved]
      split <;> rfl
    rw [hbody, Proofs.opAnnots_unresolved_varCloseT] at ho
    exact ih o ty ho
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xvb xtyb Env1 et_body Env2 et_tr Env3
      substInfo hRes hBound hBody hTr _ hEt _ _ _ _ _ _ _ h_aliases _ h_ctx2 ihBody ihTr o ty ho
    subst hEt
    rw [TContext.resolveTy_congr h_aliases] at ihBody
    rw [TContext.resolveTy_congr h_ctx2.2, TContext.resolveTy_congr h_aliases] at ihTr
    simp only [unresolved, LExpr.opAnnots, List.mem_append,
      Proofs.opAnnots_unresolved_varCloseT] at ho
    rcases ho with ho | ho
    · exact ihTr o ty ho
    · exact ihBody o ty ho
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      hRes hRes1 hRes2 hUnify hEt _ _ _ _ _ _ _ h_ctx1 _ _ ih1 ih2 o ty ho
    subst hEt
    rw [TContext.resolveTy_congr h_ctx1.2] at ih2
    simp only [unresolved, LExpr.opAnnots, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ih1 o ty ho
    · exact ih2 o ty ho
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      hRes hc ht he hUnify hEt _ _ _ _ _ _ _ h_ctx1 _ h_ctx2 _ _ ihc iht ihe o ty ho
    subst hEt
    rw [TContext.resolveTy_congr h_ctx1.2] at iht
    rw [TContext.resolveTy_congr h_ctx2.2] at ihe
    simp only [unresolved, LExpr.opAnnots, List.mem_append] at ho
    rcases ho with (ho | ho) | ho
    · exact ihc o ty ho
    · exact iht o ty ho
    · exact ihe o ty ho

/-- Under any type substitution, every operator annotation of `LExpr.resolve`'s output is an
    instance of the body of its function's type scheme, with the aliases of the input context
    resolved. -/
theorem resolve_opAnnots [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) (S : Subst) :
    ∀ o ty, (o, ty) ∈ LExpr.opAnnots (LExpr.unresolved (LExpr.applySubstT et S)) →
      ∃ f xs body, C.functions[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ (Env.context.resolveTy body) := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, -, h_Env0⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  have h_al : Env0.context.aliases = Env.context.aliases := by
    subst h_Env0
    split <;> rfl
  intro o ty ho
  rw [← h_et, Proofs.opAnnots_unresolved_applySubstT,
    Proofs.opAnnots_unresolved_applySubstT] at ho
  obtain ⟨⟨o1, ty1⟩, hmem1, heq1⟩ := List.mem_map.mp ho
  obtain ⟨⟨o2, ty2⟩, hmem2, heq2⟩ := List.mem_map.mp hmem1
  simp only [Prod.mk.injEq] at heq1 heq2
  obtain ⟨rfl, rfl⟩ := heq2
  obtain ⟨rfl, rfl⟩ := heq1
  obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ :=
    resolveAux_opAnnots C Env0 Env' e et_aux h_res h_envwf0 h_ne0 h_fwf o2 ty2 hmem2
  rw [TContext.resolveTy_congr h_al]
  obtain ⟨τ1, hτ1⟩ := LMonoTy.exists_subst_subst Env'.stateSubstInfo.subst τ
    (Env.context.resolveTy body)
  obtain ⟨τ2, hτ2⟩ := LMonoTy.exists_subst_subst S τ1 (Env.context.resolveTy body)
  refine ⟨f, xs, body, hf, hty, τ2, ?_⟩
  rw [hτ1, hτ2]

/-- Under any type substitution, every operator of `LExpr.resolve`'s output carries an instance
    of its factory signature, when `ks` has every signature type and binary `arrow` but no alias.
    The no-alias hypothesis `h_fresh` holds whenever no alias name has been registered as a
    type. -/
theorem resolve_opsConsistentR [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] {ks : KnownTypes}
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (h_sigs : FactorySigsKnown ks C.functions)
    (h_fresh : ∀ al ∈ Env.context.aliases, KnownTypes.containsName ks al.name = false)
    (S : Subst) :
    OpsConsistentR C.functions (LExpr.unresolved (LExpr.applySubstT et S)) :=
  OpsConsistentR.of_opAnnots_resolveTy h_sigs h_fresh (Proofs.fullyAnnotated_unresolved _)
    (resolve_opAnnots C Env Env' e et h h_envwf h_fwf S)

/-! ### Constants of the resolver's output -/

/-- Every constant of `resolveAux`'s output has its type name registered in the
    known types. -/
private theorem resolveAux_getConsts_known [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions) :
    ∀ c ∈ LExpr.getConsts et, C.knownTypes.containsName c.tyName = true := by
  apply resolveAux_ind
    (P := fun _ et (C : LContext T) _ _ =>
      ∀ c ∈ LExpr.getConsts et, C.knownTypes.containsName c.tyName = true)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res _ _ _ c' hc'
    obtain ⟨hk, -, rfl, -⟩ :=
      LExpr.resolveAux_const_shape C Env Env' m c et h_res
    simp only [LExpr.getConsts, List.mem_singleton] at hc'
    subst hc'
    exact hk
  case h_op =>
    intro m o oty et C Env Env' h_res _ _ _ c hc
    obtain ⟨_, _, _, _, _, _, _, h_et, _⟩ :=
      LExpr.resolveAux_op_shape C Env Env' m o oty et h_res
    subst h_et
    simp only [LExpr.getConsts, List.not_mem_nil] at hc
  case h_fvar =>
    intro m x fty et C Env Env' h_res _ _ _ c hc
    obtain ⟨_, _, h_et⟩ :=
      LExpr.resolveAux_fvar_shape C Env Env' m x fty et h_res
    subst h_et
    simp only [LExpr.getConsts, List.not_mem_nil] at hc
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 freshName EnvGen substInfo
      hRes hRes1 hRes2 hGen hUnify hEt _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 c hc
    subst hEt
    simp only [LExpr.getConsts, List.mem_append] at hc
    exact hc.elim (ih1 c) (ih2 c)
  case h_abs =>
    intro m name annotation body et C Env Env' xv xty Env1 bodyT Env2
      hRes hBound hBody hEt hEnv' _ _ _ _ _ _ ih c hc
    subst hEt
    simp only [LExpr.getConsts, Proofs.getConsts_varCloseT] at hc
    exact ih c hc
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xvb xtyb Env1 et_body Env2
      et_tr Env3 substInfo hRes hBound hBody hTr _ hEt _ _ _ _ _ _ _ _ _ _
      ihBody ihTr c hc
    subst hEt
    simp only [LExpr.getConsts, Proofs.getConsts_varCloseT, List.mem_append]
      at hc
    exact hc.elim (ihTr c) (ihBody c)
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      hRes hRes1 hRes2 hUnify hEt _ _ _ _ _ _ _ _ _ _ ih1 ih2 c hc
    subst hEt
    simp only [LExpr.getConsts, List.mem_append] at hc
    exact hc.elim (ih1 c) (ih2 c)
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      hRes hc ht he hUnify hEt _ _ _ _ _ _ _ _ _ _ _ _ ihc iht ihe c' hc'
    subst hEt
    simp only [LExpr.getConsts, List.mem_append] at hc'
    rcases hc' with (hc' | hc') | hc'
    · exact ihc c' hc'
    · exact iht c' hc'
    · exact ihe c' hc'

/-- Every constant of `LExpr.resolve`'s output, under any type substitution, has
    its type name registered in the known types. -/
private theorem resolve_getConsts_known [ToString T.IDMeta]
    [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) (S : Subst) :
    ∀ c ∈ LExpr.getConsts (LExpr.unresolved (LExpr.applySubstT et S)),
      C.knownTypes.containsName c.tyName = true := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, -, -⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  intro c hc
  rw [Proofs.getConsts_unresolved, ← h_et, Proofs.getConsts_applySubstT,
    Proofs.getConsts_applySubstT] at hc
  exact resolveAux_getConsts_known C Env0 Env' e et_aux h_res h_envwf0 h_ne0
    h_fwf c hc

/-! ### The free variables of the resolver's output in the typing context -/

/-- The alias-resolved input context, with the resolver's final substitution
    applied, holds every annotated free variable of `LExpr.resolve`'s output at
    its annotation as a monotype. -/
private theorem resolve_freeVars_ctx [ToString T.IDMeta] [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
    [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context) :
    ∀ y ann, (y, some ann) ∈ LExpr.freeVars (LExpr.unresolved et) →
      (TContext.subst Env.context.resolveTypes
        Env'.stateSubstInfo.subst).types.find? y = some (.forAll [] ann) := by
  have h_abs :=
    Subst.absorbs_refl Env'.stateSubstInfo.subst Env'.stateSubstInfo.isWF
  obtain ⟨-, etAux, -, h_et, -⟩ := resolve_resolveAux_init e et C Env Env' h
  have h_idem : applySubstT et Env'.stateSubstInfo.subst = et := by
    rw [← h_et, applySubstT_absorbs _ _ h_abs]
  have hagree :=
    resolve_fvarAnnots_agree C Env Env' e et h h_envwf h_fwf h_mono _ h_abs
  rw [h_idem] at hagree
  intro y ann hmem
  obtain ⟨ty, hfind, rfl⟩ := hagree y ann hmem
  exact TContext_types_subst_find Env.context.resolveTypes.types
    Env'.stateSubstInfo.subst y (.forAll [] ty) hfind

/-- Every free variable of `LExpr.resolve`'s output is annotated, and the
    annotations agree with any type map whose entries the alias-resolved input
    context, with the final substitution applied, holds as monotypes. -/
public theorem resolve_fvars_annotated_by [ToString T.IDMeta]
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (tyMap : Map T.Identifier LMonoTy)
    (hlink : ∀ y mty, Map.find? tyMap y = some mty →
      (TContext.subst Env.context.resolveTypes
        Env'.stateSubstInfo.subst).types.find? y = some (.forAll [] mty)) :
    fvars_annotated_by tyMap (LExpr.unresolved et) := by
  have hctx := resolve_freeVars_ctx C Env Env' e et h h_envwf h_fwf h_mono
  have hsome := freeVars_isSome_of_fullyAnnotated
    (Proofs.fullyAnnotated_unresolved et)
  refine fvars_annotated_by_of_agree tyMap _ hsome ?_
  intro y ann hmem ty hfind
  have hl := hlink y ty hfind
  rw [hctx y ann hmem] at hl
  exact (LTy.forAll.inj (Option.some.inj hl)).2

/-! ### Polymorphic typing of the resolver's output -/

/-- The output of a successful `LExpr.resolve` has polymorphic typing at its
    reported monotype, in the alias-resolved input context with the resolver's
    final substitution applied. The input context stores only monotypes, the
    factory's signatures are well formed and registered, `bool`, the literal
    types and the range of the initial substitution are registered, and no
    alias is named like a registered type. -/
public theorem resolve_output_HasType [ToString T.IDMeta] [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [HasGen T.IDMeta] [Inhabited T.IDMeta]
    [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : MonoScope Env.context)
    (h_sigs : FactorySigsKnown C.knownTypes C.functions)
    (h_fresh : ∀ al ∈ Env.context.aliases,
      KnownTypes.containsName C.knownTypes al.name = false)
    (h_bool : C.knownTypes["bool"]? = some 0) (h_lit : LiteralTysKnown C)
    (h_range : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    LExpr.HasType C
      (TContext.subst Env.context.resolveTypes Env'.stateSubstInfo.subst)
      (LExpr.unresolved et) (.forAll [] et.toLMonoTy) := by
  have h_abs :=
    Subst.absorbs_refl Env'.stateSubstInfo.subst Env'.stateSubstInfo.isWF
  obtain ⟨-, etAux, -, h_et, -⟩ := resolve_resolveAux_init e et C Env Env' h
  have h_idem : applySubstT et Env'.stateSubstInfo.subst = et := by
    rw [← h_et, applySubstT_absorbs _ _ h_abs]
  have hA := resolve_HasTypeA e et C Env Env' h h_envwf h_fwf h_resolved
  have hctx := resolve_freeVars_ctx C Env Env' e et h h_envwf h_fwf h_mono
  have hop :=
    resolve_opsConsistentR C Env Env' e et h h_envwf h_fwf h_sigs h_fresh
    Env'.stateSubstInfo.subst
  have hann :=
    resolve_opAnnots C Env Env' e et h h_envwf h_fwf Env'.stateSubstInfo.subst
  have hconst := resolve_getConsts_known C Env Env' e et h h_envwf h_fwf
    Env'.stateSubstInfo.subst
  have hrange :=
    (resolve_RangeKnown e et C Env Env' h h_envwf h_fwf h_sigs.1 h_bool h_lit
    h_range).1
  have hbind := resolve_binderAnnotations_known C Env Env' e et h h_envwf h_fwf
    Env'.stateSubstInfo.subst h_abs hrange
  rw [h_idem] at hop hann hconst hbind
  have hdecl : ∀ o ∈ LExpr.getOps (LExpr.unresolved et),
      ∃ f ty, C.functions[o.name]? = some f ∧ f.type = .ok ty := by
    intro o ho
    obtain ⟨ty, hty⟩ := exists_opAnnots_of_fullyAnnotated
      (Proofs.fullyAnnotated_unresolved et) o ho
    obtain ⟨f, xs, body, hf, hft, -⟩ := hann o ty hty
    exact ⟨f, .forAll xs body, hf, hft⟩
  have hfreshΓ : ∀ al ∈ (TContext.subst Env.context.resolveTypes
      Env'.stateSubstInfo.subst).aliases,
      KnownTypes.containsName C.knownTypes al.name = false := by
    rw [TContext.subst_aliases]
    exact h_fresh
  exact HasType_of_HasTypeA_of_annots hA hctx hop hdecl hconst h_fwf h_sigs
    hbind hfreshΓ

end

end Lambda

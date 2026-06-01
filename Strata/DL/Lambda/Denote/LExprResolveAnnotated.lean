/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprAliasFree
import all Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprAnnotated

/-! ## `resolve` produces well-annotated expressions (`HasTypeA`)

This module proves that when `LExpr.resolve` succeeds, the resulting expression
satisfies `HasTypeA` — i.e., the type annotations placed by resolution are
internally consistent.

### Comparison with `resolve_HasType`

`resolve_HasType` (in `LExprTypeSpec`) proves full polymorphic typing
(`HasType`) but requires `WellScoped`, `allKeysFresh`, and
`checkContextTypesClosed` assumptions .`resolve_HasTypeA` here proves
annotation-consistency (`HasTypeA`) under weaker assumptions: only `TEnvWF`,
`FactoryWF`, and `AliasesResolved`.

### Proof structure

The proof proceeds in layers:

1. **Alias-free infrastructure** (in `LExprAliasFree`):
`resolveAliases_aliasFree`,`resolveAliases_output_aliasFree`,
`instantiateWithCheck_aliasFree`,`typeBoundVar_xty_aliasFree`.
We need alias-freeness because `inferFVar` on a
monomorphic scheme `∀[]. xty` is only a no-op (returning exactly `xty`) when
`xty` is alias-free. Without this, the `fvar` case of the main induction cannot
conclude that the metadata annotation equals the context type.

2. **`allFvarAnnot` and `varCloseT`** (`resolveAux_allFvarAnnot`,
`varCloseT_unresolved_HasTypeA`).
The abs/quant cases of `resolveAux` open a bound variable as a fresh fvar,
recurse, then close it. To show the result is well-annotated, we need (a) that
`resolveAux` annotates every free occurrence of the fresh variable with its
type, and (b) that closing turns these into correctly-indexed bvars in the
`HasTypeA` sense.

3. **Main induction** (`resolveAux_HasTypeA_aux`). Our result is generalized
 over an arbitrary substitution `S` absorbing the output, rather than fixing
`S` to be the final substitution. This generalization is essential:
`resolveAux` recurses on sub-expressions whose output substitutions are smaller
than the final one, and the IH must apply to each sub-result under the caller's
(larger) substitution.
-/

namespace Lambda

open LExpr

section

variable {T : LExprParams} [Std.ToFormat T.IDMeta]

/-! ### Layer 2: `allFvarAnnot`, `varCloseT`, and structural helpers -/
omit [Std.ToFormat T.IDMeta] in
/-- Type substitution commutes with variable closing: substituting metadata types
    and then closing a free variable is the same as closing first then substituting. -/
theorem applySubstT_varCloseT_comm [DecidableEq T.IDMeta] (k : Nat) (xv : T.Identifier) (et : LExprT T.mono) (S : Subst) :
    applySubstT (LExpr.varCloseT k xv et) S = LExpr.varCloseT k xv (applySubstT et S) := by
  induction et generalizing k with
  | const m c => simp [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
  | op m o ty => simp [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
  | bvar m i => simp [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
  | fvar m y yty =>
    simp only [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
    split <;> simp_all [LExpr.replaceMetadata]
  | app m e1 e2 ih1 ih2 =>
    simp only [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
    congr 1; exact ih1 k; exact ih2 k
  | abs m name ty e_body ih =>
    simp only [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
    congr 1; exact ih (k + 1)
  | quant m qk name ty tr e_body ih_tr ih_e =>
    simp only [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
    congr 1; exact ih_tr (k + 1); exact ih_e (k + 1)
  | ite m c t f_expr ih_c ih_t ih_f =>
    simp only [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
    congr 1; exact ih_c k; congr 1; exact ih_t k; exact ih_f k
  | eq m e1 e2 ih1 ih2 =>
    simp only [applySubstT, LExpr.replaceMetadata, LExpr.varCloseT]
    congr 1; exact ih1 k; exact ih2 k


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


/-- When a variable has a monomorphic, alias-free scheme `∀[]. xty` in the context,
    `inferFVar` returns exactly `xty` (instantiation and alias resolution are no-ops). -/
private theorem inferFVar_mono_aliasFree [DecidableEq T.IDMeta] (C : LContext T) (Env : TEnv T.IDMeta)
    (x : T.Identifier) (fty : Option LMonoTy) (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env'))
    (h_ctx : Env.context.types.find? x = some (.forAll [] xty))
    (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    ty_res = xty := by
  simp only [inferFVar, Bind.bind, Except.bind, h_ctx] at h
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind,
             LTy.resolveAliases, LTy.instantiate] at h
  rw [resolveAliases_aliasFree xty Env h_af] at h
  elim_err h
  rename_i heq_iwc
  simp at heq_iwc
  elim_err heq_iwc
  split at heq_iwc
  · simp [Pure.pure, Except.pure] at heq_iwc
    subst heq_iwc
    simp at h
    split at h
    · cases h; rfl
    · elim_errs h
      cases h; rfl
  · simp at heq_iwc


/-- Bundled invariants that hold for the output environment of `resolveAux`:
    context is preserved, well-formedness holds, types are non-empty, and
    aliases remain resolved. -/
private structure ResolveAuxInvariants [DecidableEq T.IDMeta]
  (Env' : TEnv T.IDMeta) (Env : TEnv T.IDMeta) where
  context : Env'.context = Env.context
  envwf : TEnvWF Env'
  ne : Env'.context.types ≠ []
  resolved : TContext.AliasesResolved Env'.context

/-- Construct the invariants bundle from a successful `resolveAux` call. -/
private theorem ResolveAuxInvariants.mk_from_resolveAux
  [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ResolveAuxInvariants Env' Env :=
  let h_props := resolveAux_properties e et C Env Env' h_res h_ne
    h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.boundVarsFresh
  { context := h_props.context
    envwf := TEnvWF.of_resolveAux e et C Env Env' h_res h_envwf h_ne h_fwf h_props.context
    ne := h_props.context ▸ h_ne
    resolved := h_props.context ▸ h_resolved }

omit [Std.ToFormat T.IDMeta] in
/-- Transport an alias-free fact through a context-preserving step. -/
private theorem ResolveAuxInvariants.aliasFree_preserved
  [DecidableEq T.IDMeta]
    {Env' Env : TEnv T.IDMeta} (inv : ResolveAuxInvariants Env' Env)
    {xty : LMonoTy} (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LMonoTy.aliasFree Env'.context.aliases xty :=
  (congrArg TContext.aliases inv.context) ▸ h_af


/-- Core lemma: `resolveAux` annotates every free occurrence of a context variable
    `xv` with exactly its context type `xty`. Proved by well-founded induction on
    expression size, mirroring the structure of `resolveAux`. -/
private theorem resolveAux_allFvarAnnot_aux
  [DecidableEq T.IDMeta] [HasGen T.IDMeta] :
    ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
    ∀ (C : LContext T) (Env Env' : TEnv T.IDMeta)
      (et : LExprT T.mono) (xv : T.Identifier) (xty : LMonoTy),
    resolveAux C Env e = Except.ok (et, Env') →
    Env.context.types.find? xv = some (.forAll [] xty) →
    TEnvWF Env →
    Env.context.types ≠ [] →
    FactoryWF C.functions →
    TContext.AliasesResolved Env.context →
    LMonoTy.aliasFree Env.context.aliases xty →
    LExprT.allFvarAnnot xv xty et := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro e h_eq C Env Env' et xv xty h_res h_ctx h_envwf h_ne h_fwf h_resolved h_af
    match e with
    | .fvar m x fty =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_infer
      obtain ⟨ty_res, Env_res⟩ := v1
      simp at h_res h_infer
      obtain ⟨h_et, h_env'⟩ := h_res
      subst h_et h_env'
      simp only [LExprT.allFvarAnnot]
      intro h_xeq
      subst h_xeq
      exact inferFVar_mono_aliasFree C Env x fty ty_res Env_res h_infer h_ctx h_af
    | .const _ _ =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_ic; obtain ⟨ty, Env1⟩ := v1; simp at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      simp [LExprT.allFvarAnnot]
    | .op _ _ _ =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_errs h_res
      split at h_res
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
        obtain ⟨h_et, _⟩ := h_res; subst h_et; simp [LExprT.allFvarAnnot]
      · elim_errs h_res
        simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
        obtain ⟨h_et, _⟩ := h_res; subst h_et; simp [LExprT.allFvarAnnot]
    | .bvar _ _ =>
      simp only [resolveAux] at h_res
      simp at h_res
    | .app m e1 e2 =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; simp at h_res h_res1
      elim_err h_res
      rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; simp at h_res h_res2
      elim_errs h_res
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      simp only [LExprT.allFvarAnnot]
      have h_sz1 : e1.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_sz2 : e2.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_inv1 := ResolveAuxInvariants.mk_from_resolveAux (T := T) e1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf h_resolved
      have h_ctx1 : Env1.context.types.find? xv = some (.forAll [] xty) := h_inv1.context ▸ h_ctx
      exact ⟨ih e1.sizeOf h_sz1 e1 rfl C Env Env1 e1t xv xty h_res1 h_ctx h_envwf h_ne h_fwf h_resolved h_af,
             ih e2.sizeOf h_sz2 e2 rfl C Env1 Env2 e2t xv xty h_res2 h_ctx1 h_inv1.envwf h_inv1.ne h_fwf h_inv1.resolved (h_inv1.aliasFree_preserved h_af)⟩
    | .abs m name bty body =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_tbv; obtain ⟨xv', xty', Env1⟩ := v1; simp at h_res h_tbv
      elim_err h_res
      rename_i v2 h_res_body; obtain ⟨et_body, Env2⟩ := v2; simp at h_res h_res_body
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      simp only [LExprT.allFvarAnnot]
      have h_ne_xv : xv ≠ xv' := by
        intro heq; subst heq
        have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xty' Env1 h_tbv
        have h_none := Maps.find?_of_all_none Env.context.types xv h_fresh
        rw [h_ctx] at h_none; exact absurd h_none (by simp)
      have h_ctx1 := typeBoundVar_preserves_find C Env bty xv' xty' Env1 h_tbv xv (.forAll [] xty) h_ne_xv h_ctx
      have h_envwf1 := TEnvWF.of_typeBoundVar C Env bty xv' xty' Env1 h_tbv h_envwf
      have h_ne1 := typeBoundVar_context_types_ne_nil C Env bty xv' xty' Env1 h_tbv
      have h_aliases_eq := typeBoundVar_aliases_eq C Env bty xv' xty' Env1 h_tbv
      have h_resolved1 : TContext.AliasesResolved Env1.context := by
        intro a h_mem; rw [h_aliases_eq] at h_mem ⊢; exact h_resolved a h_mem
      have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := by
        rw [h_aliases_eq]; exact h_af
      have h_sz : (LExpr.varOpen 0 (xv', some xty') body).sizeOf < n := by
        subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]
      have h_ih_body := ih _ h_sz _ rfl C Env1 Env2 et_body xv xty h_res_body h_ctx1 h_envwf1 h_ne1 h_fwf h_resolved1 h_af1
      exact allFvarAnnot_varCloseT_ne xv xv' xty 0 et_body h_ih_body
    | .quant m qk name bty tr body =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_tbv; obtain ⟨xv', xty', Env1⟩ := v1; simp at h_res h_tbv
      elim_err h_res
      rename_i v2 h_res_body; obtain ⟨et_body, Env2⟩ := v2; simp at h_res h_res_body
      elim_err h_res
      rename_i v3 h_res_tr; obtain ⟨et_tr, Env3⟩ := v3; simp at h_res h_res_tr
      split at h_res <;> cases h_res
      simp only [LExprT.allFvarAnnot]
      have h_ne_xv : xv ≠ xv' := by
        intro heq; subst heq
        have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xty' Env1 h_tbv
        have h_none := Maps.find?_of_all_none Env.context.types xv h_fresh
        rw [h_ctx] at h_none; exact absurd h_none (by simp)
      have h_ctx1 := typeBoundVar_preserves_find C Env bty xv' xty' Env1 h_tbv xv (.forAll [] xty) h_ne_xv h_ctx
      have h_envwf1 := TEnvWF.of_typeBoundVar C Env bty xv' xty' Env1 h_tbv h_envwf
      have h_ne1 := typeBoundVar_context_types_ne_nil C Env bty xv' xty' Env1 h_tbv
      have h_aliases_eq := typeBoundVar_aliases_eq C Env bty xv' xty' Env1 h_tbv
      have h_resolved1 : TContext.AliasesResolved Env1.context := by
        intro a h_mem; rw [h_aliases_eq] at h_mem ⊢; exact h_resolved a h_mem
      have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := by
        rw [h_aliases_eq]; exact h_af
      have h_sz_body : (LExpr.varOpen 0 (xv', some xty') body).sizeOf < n := by
        subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
      have h_ih_body := ih _ h_sz_body _ rfl C Env1 Env2 et_body xv xty h_res_body h_ctx1 h_envwf1 h_ne1 h_fwf h_resolved1 h_af1
      have h_inv2 := ResolveAuxInvariants.mk_from_resolveAux (T := T)
        (LExpr.varOpen 0 (xv', some xty') body) et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf h_resolved1
      have h_ctx2 := h_inv2.context ▸ h_ctx1
      have h_sz_tr : (LExpr.varOpen 0 (xv', some xty') tr).sizeOf < n := by
        subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
      have h_ih_tr := ih _ h_sz_tr _ rfl C Env2 Env3 et_tr xv xty h_res_tr h_ctx2 h_inv2.envwf h_inv2.ne h_fwf h_inv2.resolved (h_inv2.aliasFree_preserved h_af1)
      exact ⟨allFvarAnnot_varCloseT_ne xv xv' xty 0 et_tr h_ih_tr,
             allFvarAnnot_varCloseT_ne xv xv' xty 0 et_body h_ih_body⟩
    | .ite m c th el =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_res_c; obtain ⟨ct, Env1⟩ := v1; simp at h_res h_res_c
      elim_err h_res
      rename_i v2 h_res_th; obtain ⟨tht, Env2⟩ := v2; simp at h_res h_res_th
      elim_err h_res
      rename_i v3 h_res_el; obtain ⟨elt, Env3⟩ := v3; simp at h_res h_res_el
      elim_err h_res
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      simp only [LExprT.allFvarAnnot]
      have h_sz_c : c.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_sz_th : th.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_sz_el : el.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_inv1 := ResolveAuxInvariants.mk_from_resolveAux (T := T) c ct C Env Env1 h_res_c h_envwf h_ne h_fwf h_resolved
      have h_ctx1 : Env1.context.types.find? xv = some (.forAll [] xty) := h_inv1.context ▸ h_ctx
      have h_inv2 := ResolveAuxInvariants.mk_from_resolveAux (T := T) th tht C Env1 Env2 h_res_th h_inv1.envwf h_inv1.ne h_fwf h_inv1.resolved
      have h_ctx2 : Env2.context.types.find? xv = some (.forAll [] xty) := h_inv2.context ▸ h_ctx1
      exact ⟨ih c.sizeOf h_sz_c c rfl C Env Env1 ct xv xty h_res_c h_ctx h_envwf h_ne h_fwf h_resolved h_af,
             ih th.sizeOf h_sz_th th rfl C Env1 Env2 tht xv xty h_res_th h_ctx1 h_inv1.envwf h_inv1.ne h_fwf h_inv1.resolved (h_inv1.aliasFree_preserved h_af),
             ih el.sizeOf h_sz_el el rfl C Env2 Env3 elt xv xty h_res_el h_ctx2 h_inv2.envwf h_inv2.ne h_fwf h_inv2.resolved (h_inv2.aliasFree_preserved (h_inv1.aliasFree_preserved h_af))⟩
    | .eq m e1 e2 =>
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; simp at h_res h_res1
      elim_err h_res
      rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; simp at h_res h_res2
      elim_err h_res
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      simp only [LExprT.allFvarAnnot]
      have h_sz1 : e1.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_sz2 : e2.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
      have h_inv1 := ResolveAuxInvariants.mk_from_resolveAux (T := T) e1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf h_resolved
      have h_ctx1 : Env1.context.types.find? xv = some (.forAll [] xty) := h_inv1.context ▸ h_ctx
      exact ⟨ih e1.sizeOf h_sz1 e1 rfl C Env Env1 e1t xv xty h_res1 h_ctx h_envwf h_ne h_fwf h_resolved h_af,
             ih e2.sizeOf h_sz2 e2 rfl C Env1 Env2 e2t xv xty h_res2 h_ctx1 h_inv1.envwf h_inv1.ne h_fwf h_inv1.resolved (h_inv1.aliasFree_preserved h_af)⟩

/-- `resolveAux` annotates every free occurrence of a context variable with its
    context type. Public interface to `resolveAux_allFvarAnnot_aux`. -/
theorem resolveAux_allFvarAnnot [DecidableEq T.IDMeta] [HasGen T.IDMeta]
  (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (e : LExpr T.mono) (et : LExprT T.mono)
    (xv : T.Identifier) (xty : LMonoTy)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_ctx : Env.context.types.find? xv = some (.forAll [] xty))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LExprT.allFvarAnnot xv xty et := by
  exact resolveAux_allFvarAnnot_aux e.sizeOf e rfl C Env Env' et xv xty
    h_res h_ctx h_envwf h_ne h_fwf h_resolved h_af

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
      simp at h_typed ⊢
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
theorem TEnvWF_resolve_init [DecidableEq T.IDMeta]
  (Env : TEnv T.IDMeta) (h_envwf : TEnvWF Env) :
    TEnvWF (if Env.context.types.isEmpty = true then
      Env.updateContext { types := [[]], aliases := Env.context.aliases }
    else Env) := by
  cases h_emp : Env.context.types.isEmpty with
  | false => simp; exact h_envwf
  | true =>
    simp [TEnv.updateContext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact h_envwf.aliasesWF
    · exact h_envwf.substFreshForGen
    · intro v hv n hn
      change v ∈ TContext.types.knownTypeVars [[]] at hv
      simp [TContext.types.knownTypeVars, TContext.types.knownTypeVars.go] at hv
    · intro y ty hf
      change Maps.find? [[]] y = some ty at hf
      simp [Maps.find?, Map.find?] at hf
    · intro y ty hf
      change Maps.find? [[]] y = some ty at hf
      simp [Maps.find?, Map.find?] at hf

/-- `TEnvWF` is preserved through `resolveAux`: the output environment is
    well-formed whenever the input is. -/
theorem resolveAux_TEnvWF [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    TEnvWF Env' :=
  let props := resolveAux_properties e et C Env Env' h_res h_ne
    h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.boundVarsFresh
  TEnvWF.of_resolveAux e et C Env Env' h_res h_envwf h_ne h_fwf props.context

/-- `TEnvWF` is preserved through `resolve`: the output environment is
    well-formed whenever the input is. -/
theorem resolve_TEnvWF [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactoryWF C.functions) :
    TEnvWF Env' := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  generalize h_init : (if Env.context.types.isEmpty = true then
      Env.updateContext { types := [[]], aliases := Env.context.aliases }
    else Env) = Env0 at h
  match h_res : resolveAux C Env0 e with
  | .error _ => simp [h_res] at h
  | .ok (et, Env_out) =>
    simp [h_res] at h
    obtain ⟨_, h_env'⟩ := h
    subst h_env'
    have h_envwf0 : TEnvWF Env0 := h_init ▸ TEnvWF_resolve_init Env h_envwf
    have h_ne0 : Env0.context.types ≠ [] := by
      subst h_init
      split
      · exact List.cons_ne_nil _ _
      · rename_i h_not_empty; intro h_abs; simp_all; contradiction
    exact resolveAux_TEnvWF e et C Env0 Env_out h_res h_envwf0 h_ne0 h_fwf

/-! ### Layer 3: Main induction -/

/-- Core soundness lemma: for any substitution `S` absorbing the output substitution,
    the resolved and substituted expression satisfies `HasTypeA`. Proved by
    well-founded induction on expression size. -/
private theorem resolveAux_HasTypeA_aux [DecidableEq T.IDMeta] [HasGen T.IDMeta] :
    ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = Except.ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      FactoryWF C.functions →
      TContext.AliasesResolved Env.context →
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst →
      HasTypeA [] (applySubstT et S).unresolved
                 ((applySubstT et S).toLMonoTy) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h h_envwf h_ne h_fwf h_resolved S h_absorbs
  match e with
  | .const _ _ =>
    simp only [resolveAux, inferConst, Bind.bind, Except.bind] at h
    elim_err h
    have heq := h
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
    elim_errs h
    split at h
    . cases h
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
    . elim_errs h
      cases h
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
  | .bvar _ _ => simp [resolveAux] at h
  | .fvar _ _ _ =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i ty_env h_infer
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, h_env⟩ := h
    subst h_et h_env
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    exact HasTypeA.fvar
  | .app m_app e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i e1t_env heq_e1
    elim_err h
    rename_i e2t_env heq_e2
    elim_err h
    rename_i genEnv heq_gen
    elim_err h
    rename_i substInfo heq_unify
    cases h
    have h_unify : Constraints.unify
        [(toLMonoTy e1t_env.fst, LMonoTy.tcons "arrow" [toLMonoTy e2t_env.fst, LMonoTy.ftvar genEnv.fst])]
        genEnv.snd.stateSubstInfo = .ok substInfo :=
      unify_of_mapError heq_unify
    have h_gen_subst := TEnv.genTyVar_subst e2t_env.snd genEnv.fst genEnv.snd heq_gen
    have h_gen_ctx := TEnv.genTyVar_context e2t_env.snd genEnv.fst genEnv.snd heq_gen
    have h_gen_tyGen := genTyVar_tyGen e2t_env.snd genEnv.fst genEnv.snd heq_gen
    have h_gen_name := genTyVar_name_eq e2t_env.snd genEnv.fst genEnv.snd heq_gen
    have h_inv1 := ResolveAuxInvariants.mk_from_resolveAux (T := T) e1 e1t_env.fst C Env e1t_env.snd heq_e1 h_envwf h_ne h_fwf h_resolved
    have h_props1 := resolveAux_properties e1 e1t_env.fst C Env e1t_env.snd heq_e1
      h_ne h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen
      h_envwf.boundVarsFresh
    have h_props2 := resolveAux_properties e2 e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2
      h_inv1.ne h_inv1.envwf.aliasesWF h_fwf h_inv1.envwf.substFreshForGen h_inv1.envwf.ctxFreshForGen
      h_inv1.envwf.boundVarsFresh
    -- Absorption: h_absorbs : S.absorbs (Maps.remove substInfo.subst genEnv.fst)
    have h_abs_S_rem : S.absorbs (Maps.remove substInfo.subst genEnv.fst) := by
      simp [TEnv.updateSubst] at h_absorbs; exact h_absorbs
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
        h_inv1.envwf.substFreshForGen h_props2.genState_mono
    have h_fresh_e2 : Maps.find? e2t_env.snd.stateSubstInfo.subst genEnv.fst = none ∧
        (∀ a t, Maps.find? e2t_env.snd.stateSubstInfo.subst a = some t →
          genEnv.fst ∉ LMonoTy.freeVars t) :=
      genTyVar_fresh_wrt_input_subst e2t_env.snd e2t_env.snd genEnv.snd genEnv.fst heq_gen
        h_props2.preserves.1 (Nat.le_refl _)
    have h_abs_rem_e2 := Subst.absorbs_of_remove
      substInfo.subst e2t_env.snd.stateSubstInfo.subst genEnv.fst
      h_abs_unify h_fresh_e2.1 h_fresh_e2.2
    have h_abs_rem_e1 := Subst.absorbs_of_remove
      substInfo.subst e1t_env.snd.stateSubstInfo.subst genEnv.fst
      (Subst.absorbs_trans _ _ _ h_props2.absorbs h_abs_unify)
      h_fresh_e1.1 h_fresh_e1.2
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
    have h_sz1 : e1.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz2 : e2.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_ih_e1 := ih e1.sizeOf h_sz1 e1 rfl e1t_env.fst C Env e1t_env.snd heq_e1
      h_envwf h_ne h_fwf h_resolved S h_abs_e1
    have h_ih_e2 := ih e2.sizeOf h_sz2 e2 rfl e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2
      h_inv1.envwf h_inv1.ne h_fwf h_inv1.resolved S h_abs_e2
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    rw [applySubstT_toLMonoTy] at h_ih_e1 h_ih_e2
    rw [h_eq_S] at h_ih_e1
    exact HasTypeA.app h_ih_e1 h_ih_e2
  | .abs m_abs name_abs bty_abs e_body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_tbv
    obtain ⟨xv, xty, Env1⟩ := v1
    dsimp at h h_tbv
    elim_err h
    rename_i v2 h_res_body
    obtain ⟨et_body, Env2⟩ := v2
    dsimp at h h_res_body
    simp at h
    obtain ⟨h_et, h_env'⟩ := h
    subst h_et h_env'
    have h_envwf1 : TEnvWF Env1 :=
      TEnvWF.of_typeBoundVar C Env bty_abs xv xty Env1 h_tbv h_envwf
    have h_ne1 : Env1.context.types ≠ [] :=
      typeBoundVar_context_types_ne_nil C Env bty_abs xv xty Env1 h_tbv
    have h_sz_body : (LExpr.varOpen 0 (xv, some xty) e_body).sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]
    have h_abs_Env2 : S.absorbs Env2.stateSubstInfo.subst := by
      simp [TEnv.eraseFromContext, TEnv.updateContext] at h_absorbs
      exact h_absorbs
    have h_aliases_eq1 := typeBoundVar_aliases_eq C Env bty_abs xv xty Env1 h_tbv
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_aliases_eq1] at h_mem ⊢; exact h_resolved a h_mem
    have h_ih_body := ih (LExpr.varOpen 0 (xv, some xty) e_body).sizeOf h_sz_body
      (LExpr.varOpen 0 (xv, some xty) e_body) rfl et_body C Env1 Env2 h_res_body
      h_envwf1 h_ne1 h_fwf h_resolved1 S h_abs_Env2
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
    have h_xty_af : LMonoTy.aliasFree Env1.context.aliases xty := by
      rw [h_aliases_eq1]; exact typeBoundVar_xty_aliasFree C Env bty_abs xv xty Env1 h_tbv h_resolved
    have h_annot_raw : LExprT.allFvarAnnot xv xty et_body :=
      resolveAux_allFvarAnnot C Env1 Env2
        (LExpr.varOpen 0 (xv, some xty) e_body) et_body xv xty h_res_body h_ctx_xv
        h_envwf1 h_ne1 h_fwf h_resolved1 h_xty_af
    have h_annot : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_body S) :=
      applySubstT_allFvarAnnot xv xty et_body S h_annot_raw
    exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
      (applySubstT et_body S) h_ih_body h_annot
  | .quant m_q qk_q name_q bty_q trigger_q e_q =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_tbv
    obtain ⟨xv, xty, Env1⟩ := v1
    dsimp at h h_tbv
    elim_err h
    rename_i v2 h_res_body
    obtain ⟨et_body, Env2⟩ := v2
    dsimp at h h_res_body
    elim_err h
    rename_i v3 h_res_tr
    obtain ⟨et_tr, Env3⟩ := v3
    dsimp at h h_res_tr
    elim_err h
    simp at h
    obtain ⟨h_et, h_env'⟩ := h
    subst h_et h_env'
    rename_i h_body_bool
    have h_body_ty_bool : toLMonoTy et_body = LMonoTy.bool := by
      simp [bne] at h_body_bool; exact h_body_bool
    have h_envwf1 : TEnvWF Env1 :=
      TEnvWF.of_typeBoundVar C Env bty_q xv xty Env1 h_tbv h_envwf
    have h_ne1 : Env1.context.types ≠ [] :=
      typeBoundVar_context_types_ne_nil C Env bty_q xv xty Env1 h_tbv
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
    -- AliasesResolved for Env1 and Env2
    have h_aliases_eq1 := typeBoundVar_aliases_eq C Env bty_q xv xty Env1 h_tbv
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_aliases_eq1] at h_mem ⊢; exact h_resolved a h_mem
    have h_resolved2 : TContext.AliasesResolved Env2.context :=
      h_ctx_body ▸ h_resolved1
    have h_sz_body : (LExpr.varOpen 0 (xv, some xty) e_q).sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
    have h_ih_body := ih (LExpr.varOpen 0 (xv, some xty) e_q).sizeOf h_sz_body
      (LExpr.varOpen 0 (xv, some xty) e_q) rfl et_body C Env1 Env2 h_res_body
      h_envwf1 h_ne1 h_fwf h_resolved1 S h_abs_Env2
    have h_sz_tr : (LExpr.varOpen 0 (xv, some xty) trigger_q).sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
    have h_ih_tr := ih (LExpr.varOpen 0 (xv, some xty) trigger_q).sizeOf h_sz_tr
      (LExpr.varOpen 0 (xv, some xty) trigger_q) rfl et_tr C Env2 Env3 h_res_tr
      h_envwf2 h_ne2 h_fwf h_resolved2 S h_abs_Env3
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
    change HasTypeA []
      (.quant m_q qk_q name_q (some (LMonoTy.subst S (LMonoTy.subst Env3.stateSubstInfo.subst xty)))
        (applySubstT (LExpr.varCloseT 0 xv et_tr) S).unresolved
        (applySubstT (LExpr.varCloseT 0 xv et_body) S).unresolved)
      LMonoTy.bool
    rw [applySubstT_varCloseT_comm (xv := xv) (et := et_tr),
        applySubstT_varCloseT_comm (xv := xv) (et := et_body)]
    rw [LMonoTy.subst_absorbs S Env3.stateSubstInfo.subst xty h_abs_Env3]
    refine HasTypeA.quant (τ_tr := (LExpr.varCloseT 0 xv (applySubstT et_tr S)).toLMonoTy) ?_ ?_
    · have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
        typeBoundVar_adds_to_context C Env bty_q xv xty Env1 h_tbv
      have h_ctx_xv2 : Env2.context.types.find? xv = some (.forAll [] xty) :=
        h_ctx_body ▸ h_ctx_xv
      have h_xty_af2 : LMonoTy.aliasFree Env2.context.aliases xty := by
        rw [show Env2.context.aliases = Env1.context.aliases from by
          rw [show Env2.context = Env1.context from h_ctx_body]]
        rw [h_aliases_eq1]
        exact typeBoundVar_xty_aliasFree C Env bty_q xv xty Env1 h_tbv h_resolved
      have h_annot_tr_raw : LExprT.allFvarAnnot xv xty et_tr :=
        resolveAux_allFvarAnnot C Env2 Env3
          (LExpr.varOpen 0 (xv, some xty) trigger_q) et_tr xv xty h_res_tr h_ctx_xv2
          h_envwf2 h_ne2 h_fwf h_resolved2 h_xty_af2
      have h_annot_tr : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_tr S) :=
        applySubstT_allFvarAnnot xv xty et_tr S h_annot_tr_raw
      exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
        (applySubstT et_tr S) h_ih_tr h_annot_tr
    · have h_body_ty_eq : (LExpr.varCloseT 0 xv (applySubstT et_body S)).toLMonoTy = LMonoTy.bool := by
        rw [varCloseT_toLMonoTy, applySubstT_toLMonoTy, h_body_ty_bool, LMonoTy.subst_bool]
      rw [← h_body_ty_eq]
      have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
        typeBoundVar_adds_to_context C Env bty_q xv xty Env1 h_tbv
      have h_xty_af1 : LMonoTy.aliasFree Env1.context.aliases xty := by
        rw [h_aliases_eq1]
        exact typeBoundVar_xty_aliasFree C Env bty_q xv xty Env1 h_tbv h_resolved
      have h_annot_body_raw : LExprT.allFvarAnnot xv xty et_body :=
        resolveAux_allFvarAnnot C Env1 Env2
          (LExpr.varOpen 0 (xv, some xty) e_q) et_body xv xty h_res_body h_ctx_xv
          h_envwf1 h_ne1 h_fwf h_resolved1 h_xty_af1
      have h_annot_body : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_body S) :=
        applySubstT_allFvarAnnot xv xty et_body S h_annot_body_raw
      exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
        (applySubstT et_body S) h_ih_body h_annot_body
  | .eq m_eq e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i e1t_env heq_e1
    elim_err h
    rename_i e2t_env heq_e2
    elim_err h
    rename_i substInfo heq_unify
    cases h
    have h_unify : Constraints.unify [(e1t_env.fst.toLMonoTy, e2t_env.fst.toLMonoTy)]
        e2t_env.snd.stateSubstInfo = .ok substInfo := by
      revert heq_unify
      generalize Constraints.unify [(e1t_env.fst.toLMonoTy, e2t_env.fst.toLMonoTy)]
        e2t_env.snd.stateSubstInfo = res
      intro h_me; match res, h_me with
      | .ok _, h_me => simp [Except.mapError] at h_me; rw [h_me]
      | .error _, h_me => simp [Except.mapError] at h_me
    have h_inv1 := ResolveAuxInvariants.mk_from_resolveAux (T := T) e1 e1t_env.fst C Env e1t_env.snd heq_e1 h_envwf h_ne h_fwf h_resolved
    have h_props2 := resolveAux_properties e2 e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2
      h_inv1.ne h_inv1.envwf.aliasesWF h_fwf h_inv1.envwf.substFreshForGen h_inv1.envwf.ctxFreshForGen
      h_inv1.envwf.boundVarsFresh
    -- Absorption chain
    have h_abs_unify := unify_absorbs _ _ _ h_unify
    have h_abs_e2 : S.absorbs e2t_env.snd.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _
        h_abs_unify h_absorbs
    have h_abs_e1 : S.absorbs e1t_env.snd.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _
        h_props2.absorbs h_abs_e2
    have h_S_abs_substInfo : S.absorbs substInfo.subst := by
      simp [TEnv.updateSubst] at h_absorbs; exact h_absorbs
    -- Unification soundness: both types become equal under S
    have h_eq_types : toLMonoTy (applySubstT e1t_env.fst S) = toLMonoTy (applySubstT e2t_env.fst S) := by
      rw [applySubstT_toLMonoTy, applySubstT_toLMonoTy]
      have h_sound := unify_sound _ _ _ h_unify
      have h_pair := h_sound _ (List.Mem.head _)
      simp at h_pair
      exact LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_S_abs_substInfo h_pair
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    rw [LMonoTy.subst_bool]
    apply HasTypeA.eq (τ := toLMonoTy (applySubstT e1t_env.fst S))
    · have h_sz : e1.sizeOf < n := by subst h_eq; simp_all [LExpr.sizeOf]; omega
      exact ih e1.sizeOf h_sz e1 rfl e1t_env.fst C Env e1t_env.snd heq_e1 h_envwf h_ne h_fwf h_resolved S h_abs_e1
    · rw [h_eq_types]
      have h_sz2 : e2.sizeOf < n := by subst h_eq; simp_all [LExpr.sizeOf]; omega
      exact ih e2.sizeOf h_sz2 e2 rfl e2t_env.fst C e1t_env.snd e2t_env.snd heq_e2 h_inv1.envwf h_inv1.ne h_fwf h_inv1.resolved S h_abs_e2
  | .ite m_ite c_expr th_expr el_expr =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i ct_env heq_c
    elim_err h
    rename_i tht_env heq_th
    elim_err h
    rename_i elt_env heq_el
    elim_err h
    rename_i substInfo heq_unify
    cases h
    have h_unify : Constraints.unify
        [(ct_env.fst.toLMonoTy, LMonoTy.bool),
         (tht_env.fst.toLMonoTy, elt_env.fst.toLMonoTy)]
        elt_env.snd.stateSubstInfo = .ok substInfo := by
      revert heq_unify
      generalize Constraints.unify _ elt_env.snd.stateSubstInfo = res
      intro h_me; match res, h_me with
      | .ok _, h_me => simp [Except.mapError] at h_me; rw [h_me]
      | .error _, h_me => simp [Except.mapError] at h_me
    have h_inv_c := ResolveAuxInvariants.mk_from_resolveAux (T := T) c_expr ct_env.fst C Env ct_env.snd heq_c h_envwf h_ne h_fwf h_resolved
    have h_inv_th := ResolveAuxInvariants.mk_from_resolveAux (T := T) th_expr tht_env.fst C ct_env.snd tht_env.snd heq_th h_inv_c.envwf h_inv_c.ne h_fwf h_inv_c.resolved
    have h_props_el := resolveAux_properties el_expr elt_env.fst C tht_env.snd elt_env.snd heq_el
      h_inv_th.ne h_inv_th.envwf.aliasesWF h_fwf h_inv_th.envwf.substFreshForGen h_inv_th.envwf.ctxFreshForGen
      h_inv_th.envwf.boundVarsFresh
    have h_props_th := resolveAux_properties th_expr tht_env.fst C ct_env.snd tht_env.snd heq_th
      h_inv_c.ne h_inv_c.envwf.aliasesWF h_fwf h_inv_c.envwf.substFreshForGen h_inv_c.envwf.ctxFreshForGen
      h_inv_c.envwf.boundVarsFresh
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
      have h_c_bool' : LMonoTy.subst substInfo.subst ct_env.fst.toLMonoTy =
          LMonoTy.subst substInfo.subst LMonoTy.bool := by
        rw [h_c_bool, LMonoTy.subst_bool]
      have h_lifted := LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_S_abs_substInfo h_c_bool'
      rw [LMonoTy.subst_bool] at h_lifted; exact h_lifted
    -- th and el have equal types under S
    have h_th_el_eq : LMonoTy.subst S (toLMonoTy tht_env.fst) = LMonoTy.subst S (toLMonoTy elt_env.fst) :=
      LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_S_abs_substInfo h_th_el
    have h_sz_c : c_expr.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz_th : th_expr.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz_el : el_expr.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    change HasTypeA [] (LExpr.ite m_ite (applySubstT ct_env.fst S).unresolved
      (applySubstT tht_env.fst S).unresolved (applySubstT elt_env.fst S).unresolved)
      (LMonoTy.subst S (toLMonoTy tht_env.fst))
    rw [← applySubstT_toLMonoTy tht_env.fst S]
    apply HasTypeA.ite
    · have h_ih_c := ih c_expr.sizeOf h_sz_c c_expr rfl ct_env.fst C Env ct_env.snd heq_c h_envwf h_ne h_fwf h_resolved S h_abs_c
      rw [applySubstT_toLMonoTy, h_c_type_bool] at h_ih_c
      exact h_ih_c
    · exact ih th_expr.sizeOf h_sz_th th_expr rfl tht_env.fst C ct_env.snd tht_env.snd heq_th h_inv_c.envwf h_inv_c.ne h_fwf h_inv_c.resolved S h_abs_th
    · have h_ih_el := ih el_expr.sizeOf h_sz_el el_expr rfl elt_env.fst C tht_env.snd elt_env.snd heq_el h_inv_th.envwf h_inv_th.ne h_fwf h_inv_th.resolved S h_abs_el
      rw [applySubstT_toLMonoTy] at h_ih_el
      rw [applySubstT_toLMonoTy, h_th_el_eq]
      exact h_ih_el

/-- When `resolveAux` succeeds, applying the final substitution and erasing metadata
    produces a well-typed and well-annotated expression according to `HasTypeA`. -/
theorem resolveAux_HasTypeA [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono) (Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    HasTypeA [] (applySubstT et Env'.stateSubstInfo.subst).unresolved
               ((applySubstT et Env'.stateSubstInfo.subst).toLMonoTy) := by
  have h_absorbs := Subst.absorbs_refl Env'.stateSubstInfo.subst Env'.stateSubstInfo.isWF
  exact resolveAux_HasTypeA_aux e.sizeOf e rfl et C Env Env' h h_envwf h_ne h_fwf h_resolved
    Env'.stateSubstInfo.subst h_absorbs

/-- Main soundness theorem: `LExpr.resolve` produces a well-typed and
    well-annotated `LExprT` according to `HasTypeA`. Unlike `resolve_HasType`,
    this does not require `WellScoped`, `allKeysFresh`, or `checkContextTypesClosed`
    — only `AliasesResolved`. The trade-off is that it proves annotation-consistency
    (`HasTypeA`) rather than full polymorphic typing (`HasType`). -/
theorem resolve_HasTypeA [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env : TEnv T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = Except.ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] e_typed.unresolved (e_typed.toLMonoTy) := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
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
    have h_resolved0 : (if Env.context.types.isEmpty = true then
        Env.updateContext { types := [[]], aliases := Env.context.aliases }
      else Env).context.AliasesResolved := by
      split
      · simp [TEnv.updateContext, TEnv.context, TContext.AliasesResolved] at h_resolved ⊢
        exact h_resolved
      · exact h_resolved
    exact resolveAux_HasTypeA C _ e val.fst val.snd h_res h_envwf0 h_ne0 h_fwf h_resolved0

end

end Lambda

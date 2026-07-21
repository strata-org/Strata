/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprAliasFree
import all Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprAnnotated

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Properties of `LExpr.resolve`

This module proves two major results about `LExpr.resolve`, both for the case
where resolution succeeds:

1. **`resolve_HasTypeA`** — the resulting expression satisfies `HasTypeA`, i.e.
   the type annotations placed by resolution are internally consistent.

2. **`resolve_eqModuloAnnotations`** — the resulting expression is equal to the
   input *modulo annotations* (`EqModuloAnnotations`): resolution preserves the
   structure (constructors, identifiers, constants), changing only metadata and
   type annotations. In particular it leaves the free variables unchanged.

Together these characterize resolution: it produces a well-typed annotation of
the *same* underlying expression.

### Comparison with `resolve_HasType`

`resolve_HasType` (in `LExprTypeSpec`) proves full polymorphic typing
(`HasType`) for the input but requires `WellScoped`, `allKeysFresh`, and
`checkContextTypesClosed` assumptions. `resolve_HasTypeA` here proves
annotation-consistency (`HasTypeA`) for the output under different assumptions:
`TEnvWF`, `FactoryWF`, and `AliasesResolved`. It drops the scoping/freshness/
closure conditions but adds `AliasesResolved`, which `resolve_HasType` does not
need.

### Proof structure of `resolve_HasTypeA`

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


/-- Bundled well-formedness invariants for the output environment of
    `resolveAux`: well-formedness holds, types are non-empty, and aliases
    remain resolved. Context preservation is stated separately at each use
    site. -/
private structure ResolveAuxWF [DecidableEq T.IDMeta]
  (Env' : TEnv T.IDMeta) where
  envwf : TEnvWF Env'
  ne : Env'.context.types ≠ []
  resolved : TContext.AliasesResolved Env'.context

/-- If `ResolveAuxWF Env` holds and `resolveAux` succeeds, then
    `ResolveAuxWF Env'` holds for the output environment. -/
private theorem ResolveAuxWF.mk_from_resolveAux
  [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_wf : ResolveAuxWF Env)
    (h_fwf : FactoryWF C.functions) :
    ResolveAuxWF Env' ∧ Env'.context = Env.context :=
  let h_props := resolveAux_properties e et C Env Env' h_res h_wf.ne
    h_wf.envwf.aliasesWF h_fwf h_wf.envwf.substFreshForGen h_wf.envwf.ctxFreshForGen h_wf.envwf.boundVarsFresh
  ⟨⟨TEnvWF.of_resolveAux e et C Env Env' h_res h_wf.envwf h_wf.ne h_fwf h_props.context,
    h_props.context ▸ h_wf.ne,
    h_props.context ▸ h_wf.resolved⟩, h_props.context⟩

omit [Std.ToFormat T.IDMeta] in
/-- Transport an alias-free fact through a context-preserving step. -/
private theorem ResolveAuxWF.aliasFree_preserved
  [DecidableEq T.IDMeta]
    {Env' Env : TEnv T.IDMeta} (h_ctx : Env'.context = Env.context)
    {xty : LMonoTy} (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LMonoTy.aliasFree Env'.context.aliases xty :=
  (congrArg TContext.aliases h_ctx) ▸ h_af


/-- Core lemma: `resolveAux` annotates every free occurrence of a context variable
    `xv` with exactly its context type `xty`. Proved by well-founded induction on
    expression size, mirroring the structure of `resolveAux`. -/
private theorem resolveAux_allFvarAnnot_aux
  [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (e : LExpr T.mono) (et : LExprT T.mono)
    (xv : T.Identifier) (xty : LMonoTy)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_ctx : Env.context.types.find? xv = some (.forAll [] xty))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
    (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LExprT.allFvarAnnot xv xty et := by
  revert h_af h_ctx xty xv
  apply resolveAux_ind
    (P := fun e et _C Env _Env' => ∀ (xv : T.Identifier) (xty : LMonoTy),
      Env.context.types.find? xv = some (.forAll [] xty) →
      LMonoTy.aliasFree Env.context.aliases xty →
      LExprT.allFvarAnnot xv xty et)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res h_envwf h_ne h_fwf xv xty h_ctx h_af
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    rename_i v1 h_ic; obtain ⟨ty, Env1⟩ := v1; simp at h_res
    obtain ⟨h_et, _⟩ := h_res; subst h_et
    simp [LExprT.allFvarAnnot]
  case h_op =>
    intro m o oty et C Env Env' h_res h_envwf h_ne h_fwf xv xty h_ctx h_af
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_errs h_res
    split at h_res
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et; simp [LExprT.allFvarAnnot]
    · elim_errs h_res
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et; simp [LExprT.allFvarAnnot]
  case h_fvar =>
    intro m x fty et C Env Env' h_res h_envwf h_ne h_fwf xv xty h_ctx h_af
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
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      h_res h1 h2 h_gen h_unify h_et _ _ _ _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2 xv xty h_ctx h_af
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ctx1' : Env1.context.types.find? xv = some (.forAll [] xty) := h_ctx1 ▸ h_ctx
    have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := h_ctx1 ▸ h_af
    exact ⟨h_ih1 xv xty h_ctx h_af, h_ih2 xv xty h_ctx1' h_af1⟩
  case h_abs =>
    intro m name bty body et C Env Env' xvb xtyb Env1 et_body Env2
      h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_ih xv xty h_ctx h_af
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ne_xv : xv ≠ xvb := by
      intro heq; subst heq
      have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xtyb Env1 h_tbv
      have h_none := Maps.find?_of_all_none Env.context.types xv h_fresh
      rw [h_ctx] at h_none; exact absurd h_none (by simp)
    have h_ctx1 := typeBoundVar_preserves_find C Env bty xvb xtyb Env1 h_tbv xv (.forAll [] xty) h_ne_xv h_ctx
    have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := h_aliases_eq ▸ h_af
    have h_ih_body := h_ih xv xty h_ctx1 h_af1
    exact allFvarAnnot_varCloseT_ne xv xvb xty 0 et_body h_ih_body
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xvb xtyb Env1 et_body Env2 et_tr Env3
      h_res h_tbv h_res_body h_res_tr h_et h_env' _ h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr xv xty h_ctx h_af
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ne_xv : xv ≠ xvb := by
      intro heq; subst heq
      have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xtyb Env1 h_tbv
      have h_none := Maps.find?_of_all_none Env.context.types xv h_fresh
      rw [h_ctx] at h_none; exact absurd h_none (by simp)
    have h_ctx1 := typeBoundVar_preserves_find C Env bty xvb xtyb Env1 h_tbv xv (.forAll [] xty) h_ne_xv h_ctx
    have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := h_aliases_eq ▸ h_af
    have h_ctx2' : Env2.context.types.find? xv = some (.forAll [] xty) := h_ctx2 ▸ h_ctx1
    have h_af2 : LMonoTy.aliasFree Env2.context.aliases xty :=
      (congrArg TContext.aliases h_ctx2) ▸ h_af1
    have h_ih_b := h_ih_body xv xty h_ctx1 h_af1
    have h_ih_t := h_ih_tr xv xty h_ctx2' h_af2
    exact ⟨allFvarAnnot_varCloseT_ne xv xvb xty 0 et_tr h_ih_t,
           allFvarAnnot_varCloseT_ne xv xvb xty 0 et_body h_ih_b⟩
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      h_res h1 h2 h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2 xv xty h_ctx h_af
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ctx1' : Env1.context.types.find? xv = some (.forAll [] xty) := h_ctx1 ▸ h_ctx
    have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := h_ctx1 ▸ h_af
    exact ⟨h_ih1 xv xty h_ctx h_af, h_ih2 xv xty h_ctx1' h_af1⟩
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      h_res hc ht he h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_envwf3 h_ctx3 h_ihc h_iht h_ihe xv xty h_ctx h_af
    subst h_et
    simp only [LExprT.allFvarAnnot]
    have h_ctx1' : Env1.context.types.find? xv = some (.forAll [] xty) := h_ctx1 ▸ h_ctx
    have h_af1 : LMonoTy.aliasFree Env1.context.aliases xty := h_ctx1 ▸ h_af
    have h_ctx2' : Env2.context.types.find? xv = some (.forAll [] xty) := h_ctx2 ▸ h_ctx
    have h_af2 : LMonoTy.aliasFree Env2.context.aliases xty := h_ctx2 ▸ h_af
    exact ⟨h_ihc xv xty h_ctx h_af, h_iht xv xty h_ctx1' h_af1, h_ihe xv xty h_ctx2' h_af2⟩

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
    (h_af : LMonoTy.aliasFree Env.context.aliases xty) :
    LExprT.allFvarAnnot xv xty et :=
  resolveAux_allFvarAnnot_aux C Env Env' e et xv xty
    h_res h_ctx h_envwf h_ne h_fwf h_af

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


/-- Well-formedness of `abs` metadata: every `abs` subnode carries arrow-typed
    metadata. `resolve` establishes this invariant. It is needed because
    `unresolved` reads the bound-variable annotation from the metadata arrow's
    domain when `m.type.isArrow = some _`, and from the user-annotation field
    otherwise; only under `AbsWF` does `applySubstT` (which rewrites metadata)
    commute with `applySubst` (which rewrites annotation fields). -/
def LExprT.AbsWF {T : LExprParamsT} : LExprT T → Prop
  | .abs m _ _ e => m.type.isArrow.isSome = true ∧ LExprT.AbsWF e
  | .app _ f a => LExprT.AbsWF f ∧ LExprT.AbsWF a
  | .quant _ _ _ _ tr e => LExprT.AbsWF tr ∧ LExprT.AbsWF e
  | .ite _ c t e => LExprT.AbsWF c ∧ LExprT.AbsWF t ∧ LExprT.AbsWF e
  | .eq _ a b => LExprT.AbsWF a ∧ LExprT.AbsWF b
  | _ => True

omit [Std.ToFormat T.IDMeta] in
/-- Under `AbsWF`, applying a metadata substitution and unresolving equals
    unresolving and applying the substitution to user-annotation fields. -/
theorem applySubstT_unresolved_eq_applySubst [DecidableEq T.IDMeta]
    (et : LExprT T.mono) (S : Subst) (h : LExprT.AbsWF et) :
    (applySubstT et S).unresolved = (et.unresolved).applySubst S := by
  rw [LExpr.applySubst_eq_replaceUserProvidedType]
  induction et with
  | const m c =>
    simp [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType]
  | op m o ty =>
    simp [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType,
      Option.map]
  | bvar m i =>
    simp [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType]
  | fvar m x fty =>
    simp [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType,
      Option.map]
  | app m e1 e2 ih1 ih2 =>
    simp only [LExprT.AbsWF] at h
    simp only [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType]
    exact congr (congrArg (LExpr.app m.underlying) (ih1 h.1)) (ih2 h.2)
  | abs m name bty body ih =>
    simp only [LExprT.AbsWF] at h
    obtain ⟨h_arrow, h_body⟩ := h
    simp only [applySubstT, LExpr.replaceMetadata, unresolved]
    -- m.type is an arrow; both sides read its (substituted) domain
    obtain ⟨⟨dom, cod⟩, h_eq⟩ := Option.isSome_iff_exists.mp h_arrow
    have h_mtype : m.type = LMonoTy.arrow dom cod := LMonoTy.isArrow_some h_eq
    have h_subst_arrow : LMonoTy.subst S m.type = LMonoTy.arrow (LMonoTy.subst S dom) (LMonoTy.subst S cod) := by
      rw [h_mtype]; simp only [LMonoTy.arrow]; exact LMonoTy.subst_tcons_pair S "arrow" dom cod
    have h_lhs : (LMonoTy.subst S m.type).isArrow = some (LMonoTy.subst S dom, LMonoTy.subst S cod) := by
      rw [h_subst_arrow]; exact LMonoTy.isArrow_arrow _ _
    rw [h_lhs, h_eq]
    exact congrArg (LExpr.abs m.underlying name (some (LMonoTy.subst S dom))) (ih h_body)
  | quant m qk name bty tr body ih_tr ih_body =>
    simp only [LExprT.AbsWF] at h
    simp only [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType,
      Option.map]
    exact congr (congrArg (LExpr.quant m.underlying qk name (some (LMonoTy.subst S m.type)))
      (ih_tr h.1)) (ih_body h.2)
  | ite m c t f ih_c ih_t ih_f =>
    simp only [LExprT.AbsWF] at h
    simp only [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType]
    exact congr (congr (congrArg (LExpr.ite m.underlying) (ih_c h.1)) (ih_t h.2.1)) (ih_f h.2.2)
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExprT.AbsWF] at h
    simp only [applySubstT, LExpr.replaceMetadata, unresolved, LExpr.replaceUserProvidedType]
    exact congr (congrArg (LExpr.eq m.underlying) (ih1 h.1)) (ih2 h.2)

omit [Std.ToFormat T.IDMeta] in
/-- `AbsWF` is preserved by metadata substitution: substituting an arrow type
    keeps it an arrow, so every abs subnode's metadata remains arrow-typed. -/
theorem applySubstT_AbsWF [DecidableEq T.IDMeta]
    (et : LExprT T.mono) (S : Subst) (h : LExprT.AbsWF et) :
    LExprT.AbsWF (applySubstT et S) := by
  induction et with
  | const m c => trivial
  | op m o ty => trivial
  | bvar m i => trivial
  | fvar m x fty => trivial
  | app m e1 e2 ih1 ih2 =>
    simp only [LExprT.AbsWF] at h ⊢
    simp only [applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih1 h.1, ih2 h.2⟩
  | abs m name bty body ih =>
    simp only [LExprT.AbsWF] at h ⊢
    obtain ⟨h_arrow, h_body⟩ := h
    simp only [applySubstT, LExpr.replaceMetadata] at *
    refine ⟨?_, ih h_body⟩
    obtain ⟨⟨dom, cod⟩, h_eq⟩ := Option.isSome_iff_exists.mp h_arrow
    have h_mtype : m.type = LMonoTy.arrow dom cod := LMonoTy.isArrow_some h_eq
    have h_subst_arrow : LMonoTy.subst S m.type = LMonoTy.arrow (LMonoTy.subst S dom) (LMonoTy.subst S cod) := by
      rw [h_mtype]; simp only [LMonoTy.arrow]; exact LMonoTy.subst_tcons_pair S "arrow" dom cod
    rw [h_subst_arrow, LMonoTy.isArrow_arrow]; rfl
  | quant m qk name bty tr body ih_tr ih_body =>
    simp only [LExprT.AbsWF] at h ⊢
    simp only [applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih_tr h.1, ih_body h.2⟩
  | ite m c t f ih_c ih_t ih_f =>
    simp only [LExprT.AbsWF] at h ⊢
    simp only [applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih_c h.1, ih_t h.2.1, ih_f h.2.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExprT.AbsWF] at h ⊢
    simp only [applySubstT, LExpr.replaceMetadata] at *
    exact ⟨ih1 h.1, ih2 h.2⟩

omit [Std.ToFormat T.IDMeta] in
/-- `AbsWF` is preserved by `varCloseT`: closing a free variable only rewrites
    `fvar`/`bvar` nodes, leaving every abs node's metadata unchanged. -/
theorem varCloseT_AbsWF [DecidableEq T.IDMeta]
    (k : Nat) (xv : T.Identifier) (et : LExprT T.mono) (h : LExprT.AbsWF et) :
    LExprT.AbsWF (LExpr.varCloseT k xv et) := by
  induction et generalizing k with
  | const m c => trivial
  | op m o ty => trivial
  | bvar m i => trivial
  | fvar m y yty =>
    simp only [LExpr.varCloseT]
    split <;> trivial
  | app m e1 e2 ih1 ih2 =>
    simp only [LExprT.AbsWF, LExpr.varCloseT] at h ⊢
    exact ⟨ih1 k h.1, ih2 k h.2⟩
  | abs m name bty body ih =>
    simp only [LExprT.AbsWF, LExpr.varCloseT] at h ⊢
    exact ⟨h.1, ih (k + 1) h.2⟩
  | quant m qk name bty tr body ih_tr ih_body =>
    simp only [LExprT.AbsWF, LExpr.varCloseT] at h ⊢
    exact ⟨ih_tr (k + 1) h.1, ih_body (k + 1) h.2⟩
  | ite m c t f ih_c ih_t ih_f =>
    simp only [LExprT.AbsWF, LExpr.varCloseT] at h ⊢
    exact ⟨ih_c k h.1, ih_t k h.2.1, ih_f k h.2.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExprT.AbsWF, LExpr.varCloseT] at h ⊢
    exact ⟨ih1 k h.1, ih2 k h.2⟩

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

/-- Bundle of `resolve`-level preservation facts (companion to `resolve_TEnvWF`),
    lifted from `resolveAux_properties` through the initial-context guard:
    the generator counter is monotone, the context's aliases stay resolved, and
    every free variable of the resolved output type is gen-fresh for the output
    state. The last fact is needed to discharge the constraint-freshness
    precondition of `unify_preserves_SubstFreshForGen` for the body's inferred
    type. -/
theorem resolve_properties [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen ∧
    TContext.AliasesResolved Env'.context ∧
    (∀ v, v ∈ LMonoTy.freeVars e_typed.toLMonoTy →
      ∀ k, k ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k) := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  generalize h_init : (if Env.context.types.isEmpty = true then
      Env.updateContext { types := [[]], aliases := Env.context.aliases }
    else Env) = Env0 at h
  -- `Env0` keeps `Env`'s generator state and (after init) keeps aliases resolved.
  have h_gen0 : Env0.genEnv.genState = Env.genEnv.genState := by
    subst h_init; split <;> rfl
  have h_envwf0 : TEnvWF Env0 := h_init ▸ TEnvWF_resolve_init Env h_envwf
  have h_ne0 : Env0.context.types ≠ [] := by
    subst h_init
    split
    · exact List.cons_ne_nil _ _
    · rename_i h_not_empty; intro h_abs; simp_all; contradiction
  have h_resolved0 : TContext.AliasesResolved Env0.context := by
    subst h_init
    split
    · simp [TEnv.updateContext, TEnv.context, TContext.AliasesResolved] at h_resolved ⊢
      exact h_resolved
    · exact h_resolved
  match h_res : resolveAux C Env0 e with
  | .error _ => simp [h_res] at h
  | .ok (et, Env_out) =>
    simp [h_res] at h
    obtain ⟨h_et, h_env'⟩ := h
    subst h_et h_env'
    have h_props := resolveAux_properties e et C Env0 Env_out h_res h_ne0
      h_envwf0.aliasesWF h_fwf h_envwf0.substFreshForGen h_envwf0.ctxFreshForGen
      h_envwf0.boundVarsFresh
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_gen0]; exact h_props.genState_mono
    · rw [h_props.context]; exact h_resolved0
    · -- The output type is `subst Env_out.subst et.toLMonoTy`; its free vars come
      -- from `et.toLMonoTy` (fresh by `preserves.2`) or from the output
      -- substitution's values (fresh by `preserves.1`).
      intro v hv k hk
      rw [applySubstT_toLMonoTy] at hv
      have h_sub := LMonoTy.freeVars_of_subst_subset Env_out.stateSubstInfo.subst
        et.toLMonoTy hv
      rw [List.mem_append] at h_sub
      cases h_sub with
      | inl h_orig => exact h_props.preserves.2 v h_orig k hk
      | inr h_val => exact h_props.preserves.1 v (Or.inr h_val) k hk

/-- Free vars of `LMonoTys.instantiateEnv ids mtys` output are all gen-prefixed
    (`tyPrefix ++ toString k`), assuming the input freeVars are all in `ids`. -/
theorem instantiateEnv_freeVars_gen [DecidableEq T.IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env'))
    (h_closed : ∀ tv, tv ∈ LMonoTys.freeVars mtys → tv ∈ ids) :
    ∀ tv, tv ∈ LMonoTys.freeVars mtys' → ∃ (k : Nat), tv = TState.tyPrefix ++ toString k := by
  intro tv h_tv
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨h1, _⟩ := h; rw [← h1] at h_tv
    simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h_inst
    elim_err h_inst
    rename_i v1 h_gen
    obtain ⟨freshtvs, genEnv1⟩ := v1; simp at h_inst h_gen
    obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq] at h_tv
    have h_len : freshtvs.length = ids.length :=
      TGenEnv.genTyVars_length _ _ _ _ h_gen
    have h_in_fresh := LMonoTys.freeVars_subst_closed ids freshtvs h_len mtys h_closed tv h_tv
    exact TGenEnv.genTyVars_prefixed ids.length _ freshtvs genEnv1 h_gen tv h_in_fresh

/-- Precise characterization: free vars of `LMonoTy.subst [zip ids (map ftvar freshtvs)] mty`
    are either in `freshtvs` (a renamed bound var) or a free var of `mty` not in `ids`. -/
theorem freeVars_zip_subst_cases
    (ids freshtvs : List TyIdentifier) (h_len : freshtvs.length = ids.length)
    (mty : LMonoTy) (tv : TyIdentifier)
    (h_tv : tv ∈ LMonoTy.freeVars
        (LMonoTy.subst [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mty)) :
    tv ∈ freshtvs ∨ (tv ∈ LMonoTy.freeVars mty ∧ tv ∉ ids) := by
  induction mty with
  | ftvar x =>
    rw [LMonoTy.subst_unfold] at h_tv
    simp only [LMonoTy.substReduce] at h_tv
    generalize h_find : Maps.find? [List.zip ids (List.map LMonoTy.ftvar freshtvs)] x = fo at h_tv
    cases fo with
    | none =>
      simp only [LMonoTy.freeVars, List.mem_singleton] at h_tv
      subst h_tv
      refine Or.inr ⟨by simp [LMonoTy.freeVars], ?_⟩
      intro h_mem
      obtain ⟨ftv, _, h_find_some⟩ := Maps.find?_zip_ftvar_mem ids freshtvs h_len tv h_mem
      rw [h_find_some] at h_find; exact absurd h_find (by simp)
    | some t =>
      have h_t_val : t ∈ Maps.values [List.zip ids (List.map LMonoTy.ftvar freshtvs)] :=
        Maps.find?_mem_values _ h_find
      simp only [Maps.values, List.append_nil, List.zip] at h_t_val
      rw [Map.values_zipWith_eq_take] at h_t_val
      have h_take : (List.map LMonoTy.ftvar freshtvs).take ids.length =
          List.map LMonoTy.ftvar freshtvs := by
        rw [List.take_of_length_le]; simp [h_len]
      rw [h_take] at h_t_val
      obtain ⟨ftv, h_ftv_mem, h_teq⟩ := List.mem_map.mp h_t_val
      subst h_teq
      simp only [LMonoTy.freeVars, List.mem_singleton] at h_tv
      subst h_tv
      exact Or.inl h_ftv_mem
  | bitvec n =>
    rw [LMonoTy.subst_unfold] at h_tv
    simp only [LMonoTy.substReduce, LMonoTy.freeVars] at h_tv
    exact absurd h_tv (by simp)
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold] at h_tv
    simp only [LMonoTy.substReduce, LMonoTy.substReduceList_eq_map, LMonoTy.freeVars] at h_tv
    have h_exists : ∃ a ∈ args, tv ∈ LMonoTy.freeVars (LMonoTy.subst
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)] a) := by
      clear ih
      induction args with
      | nil => simp [LMonoTys.freeVars] at h_tv
      | cons a arest iha =>
        simp only [List.map_cons, LMonoTys.freeVars_of_cons, List.mem_append] at h_tv
        rcases h_tv with h_a | h_rest
        · exact ⟨a, List.mem_cons_self, h_a⟩
        · obtain ⟨a', h_mem', h_fv'⟩ := iha h_rest
          exact ⟨a', List.mem_cons_of_mem _ h_mem', h_fv'⟩
    obtain ⟨a, h_a_mem, h_a_fv⟩ := h_exists
    rcases ih a h_a_mem h_a_fv with h_fresh | ⟨h_body, h_notin⟩
    · exact Or.inl h_fresh
    · refine Or.inr ⟨?_, h_notin⟩
      simp only [LMonoTy.freeVars]
      exact LMonoTys.freeVars_mem_subset h_a_mem h_body

/-- Free vars of `LTy.instantiate ty` output are either free vars of the scheme
    `ty` (`LTy.freeVars ty`) or gen-prefixed (from the fresh bound-var substitution). -/
theorem LTy_instantiate_freeVars_cases [DecidableEq T.IDMeta]
    (ty : LTy) (genEnv : TGenEnv T.IDMeta) (mty : LMonoTy) (genEnv' : TGenEnv T.IDMeta)
    (h : LTy.instantiate ty genEnv = .ok (mty, genEnv')) :
    ∀ tv, tv ∈ LMonoTy.freeVars mty →
      tv ∈ LTy.freeVars ty ∨ ∃ (k : Nat), tv = TState.tyPrefix ++ toString k := by
  intro tv h_tv
  cases ty with
  | forAll xs body =>
    cases xs with
    | nil =>
      simp only [LTy.instantiate, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_eq, _⟩ := h; subst h_eq
      left; simp only [LTy.freeVars, List.removeAll_nil]; exact h_tv
    | cons x rest =>
      simp only [LTy.instantiate, Bind.bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i v1 h_gen; obtain ⟨freshtvs, genEnv1⟩ := v1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_mty, _⟩ := h; subst h_mty
        have h_len : freshtvs.length = (x :: rest).length :=
          TGenEnv.genTyVars_length _ _ _ _ h_gen
        rcases freeVars_zip_subst_cases (x :: rest) freshtvs h_len body tv h_tv with
          h_fresh | ⟨h_body, h_notin⟩
        · right
          exact TGenEnv.genTyVars_prefixed (x :: rest).length _ freshtvs genEnv1 h_gen tv h_fresh
        · left
          simp only [LTy.freeVars, List.removeAll, List.mem_filter,
            Bool.not_eq_eq_eq_not, Bool.not_true, List.elem_eq_mem, decide_eq_false_iff_not]
          exact ⟨h_body, h_notin⟩

/-- Free vars of `LMonoTy.instantiateWithCheck mty` output are all gen-prefixed. -/
theorem LMonoTy_instantiateWithCheck_freeVars_gen [DecidableEq T.IDMeta]
    (mty : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty C Env = .ok (mty', Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ tv, tv ∈ LMonoTy.freeVars mty' → ∃ (k : Nat), tv = TState.tyPrefix ++ toString k := by
  intro tv h_tv
  obtain ⟨mty_ie, Env_ie, Env_ra, h_ie, h_ra⟩ :=
    LMonoTy.instantiateWithCheck_decompose mty C Env mty' Env' h
  have h_aw_ie : TContext.AliasesWF Env_ie.context := by
    have h_ctx_ie : Env_ie.context = Env.context :=
      LMonoTys.instantiateEnv_context _ _ Env _ _ h_ie
    rw [h_ctx_ie]; exact h_aw
  have h_tv_ie : tv ∈ LMonoTy.freeVars mty_ie :=
    LMonoTy_resolveAliases_freeVars_subset mty_ie Env_ie mty' Env_ra h_ra h_aw_ie tv h_tv
  have h_closed : ∀ w, w ∈ LMonoTys.freeVars [mty] → w ∈ mty.freeVars := by
    intro w hw; simp only [LMonoTys.freeVars, List.append_nil] at hw; exact hw
  exact instantiateEnv_freeVars_gen mty.freeVars [mty] Env [mty_ie] Env_ie h_ie h_closed tv
    (by simp only [LMonoTys.freeVars, List.append_nil]; exact h_tv_ie)

/-- Free vars of `LTy.instantiateWithCheck ty` output are all gen-prefixed, for a
    closed scheme (`LTy.freeVars ty = []`). -/
theorem LTy_instantiateWithCheck_freeVars_gen [DecidableEq T.IDMeta]
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty', Env'))
    (h_closed : LTy.freeVars ty = [])
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ tv, tv ∈ LMonoTy.freeVars mty' → ∃ (k : Nat), tv = TState.tyPrefix ++ toString k := by
  intro tv h_tv
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h h_ra
  elim_err h
  rename_i h_check
  elim_err h
  obtain ⟨h_mty, _⟩ := Prod.mk.injEq .. ▸ (Except.ok.inj h); subst h_mty
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
  elim_err h_ra
  rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
  simp only at h_ra h_lty_inst
  have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_lty_inst
  have h_aw_mid : TContext.AliasesWF ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context := by
    show TContext.AliasesWF genEnv'.context; rw [h_ctx_inst]; exact h_aw
  have h_tv_inst : tv ∈ LMonoTy.freeVars mty_inst :=
    LMonoTy_resolveAliases_freeVars_subset mty_inst {Env with genEnv := genEnv'} mty_ra Env_ra
      h_ra h_aw_mid tv h_tv
  rcases LTy_instantiate_freeVars_cases ty Env.genEnv mty_inst genEnv' h_lty_inst tv h_tv_inst with
    h_fv | h_gen
  · rw [h_closed] at h_fv; exact absurd h_fv (by simp)
  · exact h_gen

/-- Free vars of `LTy.instantiateWithCheck ty` output are either free vars of the
    scheme `ty` or gen-prefixed. -/
theorem LTy_instantiateWithCheck_freeVars_cases [DecidableEq T.IDMeta]
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty', Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ tv, tv ∈ LMonoTy.freeVars mty' →
      tv ∈ LTy.freeVars ty ∨ ∃ (k : Nat), tv = TState.tyPrefix ++ toString k := by
  intro tv h_tv
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h h_ra
  elim_err h
  rename_i h_check
  elim_err h
  obtain ⟨h_mty, _⟩ := Prod.mk.injEq .. ▸ (Except.ok.inj h); subst h_mty
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
  elim_err h_ra
  rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
  simp only at h_ra h_lty_inst
  have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_lty_inst
  have h_aw_mid : TContext.AliasesWF ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context := by
    show TContext.AliasesWF genEnv'.context; rw [h_ctx_inst]; exact h_aw
  have h_tv_inst : tv ∈ LMonoTy.freeVars mty_inst :=
    LMonoTy_resolveAliases_freeVars_subset mty_inst {Env with genEnv := genEnv'} mty_ra Env_ra
      h_ra h_aw_mid tv h_tv
  exact LTy_instantiate_freeVars_cases ty Env.genEnv mty_inst genEnv' h_lty_inst tv h_tv_inst

/-- `LMonoTy.instantiateWithCheck` preserves `stateSubstInfo`. -/
theorem LMonoTy_instantiateWithCheck_preserves_stateSubstInfo [DecidableEq T.IDMeta]
    (mty : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty C Env = .ok (mty', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  dsimp only [LMonoTy.instantiateWithCheck, bind, Except.instMonad, Except.bind] at h
  split at h
  · simp at h
  · rename_i instTypes Env_ie h_ie
    have h_ie_subst : Env_ie.stateSubstInfo = Env.stateSubstInfo := by
      simp only [LMonoTys.instantiateEnv] at h_ie
      split at h_ie
      · simp at h_ie
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h_ie
        obtain ⟨_, h_env⟩ := h_ie; rw [← h_env]
    split at h
    · simp at h
    · rename_i vra h_ra; obtain ⟨mty_ra, Env_ra⟩ := vra
      split at h
      · simp at h
      · split at h
        · simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, h_env'⟩ := h; rw [← h_env']
          exact (LMonoTy_resolveAliases_subst_eq _ Env_ie mty_ra Env_ra h_ra).trans h_ie_subst
        · simp at h

/-- `typeBoundVar` preserves `stateSubstInfo`. -/
theorem typeBoundVar_stateSubstInfo [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  elim_err h
  rename_i genResult h_gen
  have h_gen_subst : genResult.snd.stateSubstInfo = Env.stateSubstInfo := by
    elim_err h_gen
    have h_gen_eq := Except.ok.inj h_gen; rw [← h_gen_eq]
  split at h
  · elim_err h
    rename_i _ bty_mty _ _ Env_inst h_inst
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    rw [TEnv.addInNewestContext_stateSubstInfo]
    exact (LMonoTy_instantiateWithCheck_preserves_stateSubstInfo bty_mty C genResult.snd
      _ Env_inst h_inst).trans h_gen_subst
  · elim_err h
    rename_i v1 h_genTy
    obtain ⟨xtyid, Env1⟩ := v1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    rw [TEnv.addInNewestContext_stateSubstInfo]
    exact (TEnv.genTyVar_subst genResult.snd xtyid Env1 h_genTy).trans h_gen_subst

/-- `typeBoundVar` output type `xty` has free vars that are either in the input
    context's `knownTypeVars` or gen-prefixed. -/
theorem typeBoundVar_xty_freeVars [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTy.freeVars xty →
      v ∈ TContext.knownTypeVars Env.context ∨ ∃ (k : Nat), v = TState.tyPrefix ++ toString k := by
  intro v hv
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  elim_err h
  rename_i genResult h_gen
  have h_gen_ctx : genResult.snd.context = Env.context := by
    elim_err h_gen
    rename_i a_id T'_env h_genVar
    have h_eq := Except.ok.inj h_gen; rw [← h_eq]
    simp only [TEnv.context]
    exact HasGen.genVar_context Env.genEnv a_id T'_env h_genVar
  split at h
  · elim_err h
    rename_i _ bty_mty _ _ Env_inst h_inst
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h_xty, _⟩ := h; subst h_xty
    have h_aw_gen : TContext.AliasesWF genResult.snd.context := h_gen_ctx ▸ h_aw
    obtain ⟨k, hk⟩ := LMonoTy_instantiateWithCheck_freeVars_gen bty_mty C genResult.snd
      _ Env_inst h_inst h_aw_gen v hv
    exact Or.inr ⟨k, hk⟩
  · rename_i h_none
    elim_err h
    rename_i v1 h_genTyVar
    obtain ⟨xtyid, Env_tg⟩ := v1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h_xty, _⟩ := h; subst h_xty
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv; subst hv
    have h_name := genTyVar_name_eq genResult.snd v Env_tg h_genTyVar
    exact Or.inr ⟨genResult.snd.genEnv.genState.tyGen, h_name⟩

/-- `typeBoundVar` grows `knownTypeVars` only by the free vars of `xty`. -/
theorem typeBoundVar_knownTypeVars_cases [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    ∀ v, v ∈ TContext.knownTypeVars Env'.context →
      v ∈ TContext.knownTypeVars Env.context ∨ v ∈ LMonoTy.freeVars xty := by
  intro v hv
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  elim_err h
  rename_i genResult h_gen
  have h_gen_ctx : genResult.snd.context = Env.context := by
    elim_err h_gen
    rename_i a_id T'_env h_genVar
    have h_eq := Except.ok.inj h_gen; rw [← h_eq]
    simp only [TEnv.context]
    exact HasGen.genVar_context Env.genEnv a_id T'_env h_genVar
  split at h
  · elim_err h
    rename_i _ bty_mty _ _ Env_inst h_inst
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_xv, h_xty, h_env⟩ := h; subst h_env h_xty h_xv
    have h_ctx_inst : Env_inst.context = Env.context := by
      rw [LMonoTy_instantiateWithCheck_context' bty_mty C genResult.snd _ Env_inst h_inst,
        h_gen_ctx]
    rcases knownTypeVars_addInNewestContext_cases Env_inst _ (.forAll [] _) v hv with
      h_old | h_new
    · left; rw [← h_ctx_inst]; exact h_old
    · right; simpa only [LTy.freeVars, List.removeAll_nil] using h_new
  · elim_err h
    rename_i v1 h_genTy
    obtain ⟨xtyid, Env_tg⟩ := v1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_xv, h_xty, h_env⟩ := h; subst h_env h_xty h_xv
    have h_ctx_tg : Env_tg.context = Env.context := by
      rw [TEnv.genTyVar_context genResult.snd xtyid Env_tg h_genTy, h_gen_ctx]
    rcases knownTypeVars_addInNewestContext_cases Env_tg _ (.forAll [] _) v hv with
      h_old | h_new
    · left; rw [← h_ctx_tg]; exact h_old
    · right; simpa only [LTy.freeVars, List.removeAll_nil] using h_new

/-- **Predicate-closure of `resolve`.** For any predicate `P` on type variables that
    is closed over the input context's known type variables and the input
    substitution's range, `resolve` keeps `P` holding on (i) every free variable of
    the resolved output type and (ii) every range variable of the output
    substitution. This is the *positive* companion to `resolve_properties`'s
    gen-freshness conjunct: where that says "output vars are not future gen-names",
    this propagates an *arbitrary* invariant `P`. Instantiated with
    `P v := v ∉ func.typeArgs`, it shows the body's resolved type never mentions a
    user type argument (the formals were monomorphized to fresh `$__ty` vars before
    resolution), which is what makes `v_unify`'s range disjoint from `func.typeArgs`.

    PROOF PLAN (deferred — `sorry` with concrete plan, see ALPHAEQUIV_RENAMESUBST_PLAN.md
    §10m): lift the existing `resolveAux_properties` size-induction skeleton
    (LExprTypeSpec:3606) with `P` as an extra threaded invariant. The three and only
    type-variable entry points each preserve `P`:
    (i) the context — preserved because `resolveAux` does not change the context
        (`ResolveAuxProperties.context`) and new bound-var bindings come from
        `typeBoundVar`/`genTyVar`/`instantiateWithCheck`;
    (ii) `genTyVar` — fresh `$__ty` vars; for `P = (· ∉ typeArgs)` these satisfy `P`
        by `genTyVars_prefixed` + `LFuncWF.typeArgs_no_gen_prefix`;
    (iii) annotations via `LMonoTy.instantiateWithCheck` — its output freeVars ⊆
        `freshtvs` by `LMonoTy.freeVars_subst_closed`, hence `$__ty`, hence `P`;
        `resolveAliases` introduces no new var (`TypeAlias.WF.fvs_closed` +
        `TypeAlias.expand` ⟹ `freeVars(expand) ⊆ freeVars(args)`).
    The `app`/`eq`/`ite` cases compose recursion with `Constraints.unify_pred`
    (the unify step preserves `P` from constraint+input-subst to result-subst). -/
theorem resolve_freeVars_pred [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : LExpr.resolve C Env e = .ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (P : TyIdentifier → Prop)
    (h_ctx : ∀ v, v ∈ TContext.knownTypeVars Env.context → P v)
    (h_sub : ∀ v, (v ∈ Maps.keys Env.stateSubstInfo.subst ∨
                    v ∈ Subst.freeVars Env.stateSubstInfo.subst) → P v)
    -- `P` holds on every generated type variable. FALSE without this (an unannotated binder's
    -- `genTyVar` injects a fresh `$__ty<k>` into the output type, unconstrained by `h_ctx`/`h_sub`;
    -- for `P := fun _ => False` the conclusion is refuted). At the sole call site
    -- (`vunify_avoids_typeArgs`, `P := (·∉typeArgs)`) discharged by `genTyVars_prefixed` +
    -- `LFuncWF.typeArgs_no_gen_prefix` (the gen-prefix guard, extracted from `h`).
    (h_gen : ∀ v (k : Nat), v = TState.tyPrefix ++ toString k → P v) :
    (∀ v, v ∈ LMonoTy.freeVars e_typed.toLMonoTy → P v) ∧
    (∀ v, (v ∈ Maps.keys Env'.stateSubstInfo.subst ∨
            v ∈ Subst.freeVars Env'.stateSubstInfo.subst) → P v) := by
  have h_aux : ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      (∀ v, v ∈ TContext.knownTypeVars Env.context → P v) →
      (∀ v, (v ∈ Maps.keys Env.stateSubstInfo.subst ∨
              v ∈ Subst.freeVars Env.stateSubstInfo.subst) → P v) →
      (∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy → P v) ∧
      (∀ v, (v ∈ Maps.keys Env'.stateSubstInfo.subst ∨
              v ∈ Subst.freeVars Env'.stateSubstInfo.subst) → P v) := by
    intro e et C Env Env' h_res h_envwf h_ne h_fwf
    apply resolveAux_ind
      (P := fun e et _C Env Env' =>
        (∀ v, v ∈ TContext.knownTypeVars Env.context → P v) →
        (∀ v, (v ∈ Maps.keys Env.stateSubstInfo.subst ∨
                v ∈ Subst.freeVars Env.stateSubstInfo.subst) → P v) →
        (∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy → P v) ∧
        (∀ v, (v ∈ Maps.keys Env'.stateSubstInfo.subst ∨
                v ∈ Subst.freeVars Env'.stateSubstInfo.subst) → P v))
      (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
      (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
    case h_const =>
      intro m c et C Env Env' h h_envwf h_ne h_fwf h_ctx h_sub
      simp only [resolveAux, inferConst, Bind.bind, Except.bind] at h
      elim_err h
      rename_i v1 heq_inferConst
      split at heq_inferConst
      · simp only [Except.ok.injEq] at heq_inferConst
        subst heq_inferConst
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_et, h_env⟩ := h
        subst h_et h_env
        refine ⟨fun v hv => ?_, h_sub⟩
        simp only [toLMonoTy, LConst.ty_freeVars] at hv
        exact absurd hv (by simp)
      · simp at heq_inferConst
    case h_op =>
      intro m o oty et C Env Env' h h_envwf h_ne h_fwf h_ctx h_sub
      have h_aw := h_envwf.aliasesWF
      simp only [resolveAux, Bind.bind, Except.bind] at h
      elim_err h
      rename_i func h_find
      elim_err h
      rename_i type_val h_type
      elim_err h
      rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
      have h_func_mem : func ∈ C.functions.toArray := Factory.getElem?_is_some_implies_mem h_find
      have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
      have h_ty_closed : LTy.freeVars type_val = [] :=
        LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
      have h_ty_inst_gen : ∀ tv, tv ∈ LMonoTy.freeVars ty_inst →
          ∃ (k : Nat), tv = TState.tyPrefix ++ toString k :=
        LTy_instantiateWithCheck_freeVars_gen type_val C Env ty_inst Env1 h_inst h_ty_closed h_aw
      have h_ty_inst_P : ∀ v, v ∈ LMonoTy.freeVars ty_inst → P v := by
        intro v hv; obtain ⟨k, hk⟩ := h_ty_inst_gen v hv; exact h_gen v k hk
      have h_sub_stateEq : Env1.stateSubstInfo = Env.stateSubstInfo :=
        LTy_instantiateWithCheck_preserves_stateSubstInfo type_val C Env ty_inst Env1 h_inst
      cases oty with
      | none =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_et, h_env⟩ := h; subst h_et h_env
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · simp only [toLMonoTy] at hv; exact h_ty_inst_P v hv
        · rw [h_sub_stateEq] at hv; exact h_sub v hv
      | some oty_val =>
        simp only [Except.mapError] at h
        elim_err h
        rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
        elim_err h
        rename_i v3 h_mapError
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_et, h_env⟩ := h; subst h_et h_env
        have h_unify := unify_of_mapError h_mapError
        have h_aw1 : TContext.AliasesWF Env1.context := by
          rw [LTy_instantiateWithCheck_context' type_val C Env ty_inst Env1 h_inst]; exact h_aw
        have h_oty_inst_gen : ∀ tv, tv ∈ LMonoTy.freeVars oty_inst →
            ∃ (k : Nat), tv = TState.tyPrefix ++ toString k :=
          LMonoTy_instantiateWithCheck_freeVars_gen oty_val C Env1 oty_inst Env2 h_inst2 h_aw1
        have h_oty_inst_P : ∀ v, v ∈ LMonoTy.freeVars oty_inst → P v := by
          intro v hv; obtain ⟨k, hk⟩ := h_oty_inst_gen v hv; exact h_gen v k hk
        have h_sub2_stateEq : Env2.stateSubstInfo = Env1.stateSubstInfo :=
          LMonoTy_instantiateWithCheck_preserves_stateSubstInfo oty_val C Env1 oty_inst Env2 h_inst2
        have h_sub2_P : ∀ v, v ∈ Maps.keys Env2.stateSubstInfo.subst → P v := by
          intro v hv; rw [h_sub2_stateEq, h_sub_stateEq] at hv; exact h_sub v (Or.inl hv)
        have h_sub2_Pv : ∀ v, v ∈ Subst.freeVars Env2.stateSubstInfo.subst → P v := by
          intro v hv; rw [h_sub2_stateEq, h_sub_stateEq] at hv; exact h_sub v (Or.inr hv)
        have h_cs_P : ∀ v, v ∈ Constraints.freeVars [(ty_inst, oty_inst)] → P v := by
          intro v hv
          simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
            List.mem_append] at hv
          rcases hv with hv | hv
          · exact h_ty_inst_P v hv
          · exact h_oty_inst_P v hv
        have h_unify_pred := Constraints.unify_pred h_unify P h_cs_P h_sub2_P h_sub2_Pv
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · simp only [toLMonoTy] at hv; exact h_ty_inst_P v hv
        · simp only [TEnv.updateSubst] at hv
          rcases hv with hv | hv
          · exact h_unify_pred.1 v hv
          · exact h_unify_pred.2 v hv
    case h_fvar =>
      intro m x fty et C Env Env' h h_envwf h_ne h_fwf h_ctx h_sub
      have h_aw := h_envwf.aliasesWF
      simp only [resolveAux, Bind.bind, Except.bind] at h
      elim_err h
      rename_i v1 h_infer; obtain ⟨ty_res, Env_res⟩ := v1; dsimp at h h_infer
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_et, h_env⟩ := h; subst h_et h_env
      simp only [inferFVar] at h_infer
      split at h_infer
      · simp at h_infer
      · rename_i ty_found h_find_ctx
        simp only [Bind.bind, Except.bind] at h_infer
        elim_err h_infer
        rename_i v2 h_inst; obtain ⟨ty_inst, Env1⟩ := v2; dsimp at h_infer h_inst
        have h_ty_inst_P : ∀ v, v ∈ LMonoTy.freeVars ty_inst → P v := by
          intro v hv
          rcases LTy_instantiateWithCheck_freeVars_cases ty_found C Env ty_inst Env1
            h_inst h_aw v hv with h_fv | ⟨k, hk⟩
          · exact h_ctx v (TContext.mem_knownTypeVars_of_find h_find_ctx h_fv)
          · exact h_gen v k hk
        have h_sub1_stateEq : Env1.stateSubstInfo = Env.stateSubstInfo :=
          LTy_instantiateWithCheck_preserves_stateSubstInfo ty_found C Env ty_inst Env1 h_inst
        cases fty with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_infer
          obtain ⟨h_ty, h_env1⟩ := h_infer; subst h_ty h_env1
          refine ⟨fun v hv => ?_, fun v hv => ?_⟩
          · simp only [toLMonoTy] at hv; exact h_ty_inst_P v hv
          · rw [h_sub1_stateEq] at hv; exact h_sub v hv
        | some fty_val =>
          simp only [Except.mapError] at h_infer
          elim_err h_infer
          rename_i v3 h_inst2; obtain ⟨fty_inst, Env2⟩ := v3; dsimp at h_infer h_inst2
          elim_err h_infer
          rename_i v4 h_mapError
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_infer
          obtain ⟨h_ty, h_env2⟩ := h_infer; subst h_ty h_env2
          have h_unify := unify_of_mapError h_mapError
          have h_aw1 : TContext.AliasesWF Env1.context := by
            rw [LTy_instantiateWithCheck_context' ty_found C Env ty_inst Env1 h_inst]; exact h_aw
          have h_fty_inst_P : ∀ v, v ∈ LMonoTy.freeVars fty_inst → P v := by
            intro v hv
            obtain ⟨k, hk⟩ := LMonoTy_instantiateWithCheck_freeVars_gen fty_val C Env1
              fty_inst Env2 h_inst2 h_aw1 v hv
            exact h_gen v k hk
          have h_sub2_stateEq : Env2.stateSubstInfo = Env1.stateSubstInfo :=
            LMonoTy_instantiateWithCheck_preserves_stateSubstInfo fty_val C Env1 fty_inst Env2 h_inst2
          have h_sub2_P : ∀ v, v ∈ Maps.keys Env2.stateSubstInfo.subst → P v := by
            intro v hv; rw [h_sub2_stateEq, h_sub1_stateEq] at hv; exact h_sub v (Or.inl hv)
          have h_sub2_Pv : ∀ v, v ∈ Subst.freeVars Env2.stateSubstInfo.subst → P v := by
            intro v hv; rw [h_sub2_stateEq, h_sub1_stateEq] at hv; exact h_sub v (Or.inr hv)
          have h_cs_P : ∀ v, v ∈ Constraints.freeVars [(fty_inst, ty_inst)] → P v := by
            intro v hv
            simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
              List.mem_append] at hv
            rcases hv with hv | hv
            · exact h_fty_inst_P v hv
            · exact h_ty_inst_P v hv
          have h_unify_pred := Constraints.unify_pred h_unify P h_cs_P h_sub2_P h_sub2_Pv
          refine ⟨fun v hv => ?_, fun v hv => ?_⟩
          · simp only [toLMonoTy] at hv; exact h_ty_inst_P v hv
          · simp only [TEnv.updateSubst] at hv
            rcases hv with hv | hv
            · exact h_unify_pred.1 v hv
            · exact h_unify_pred.2 v hv
    case h_app =>
      intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
        h_res h1 h2 h_genv h_unify h_et h_subeq h_abs_rem1 h_abs_rem2
        h_e1t_no_fresh h_e2t_no_fresh h_unify_eq
        h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_ih1 h_ih2 h_ctx h_sub
      subst h_et
      have h_ih1' := h_ih1 h_ctx h_sub
      have h_ctx1' : ∀ v, v ∈ TContext.knownTypeVars Env1.context → P v := by
        rw [h_ctx1]; exact h_ctx
      have h_ih2' := h_ih2 h_ctx1' h_ih1'.2
      have h_fresh_P : P fresh_name := by
        have h_name := genTyVar_name_eq Env2 fresh_name Env_gen h_genv
        exact h_gen fresh_name Env2.genEnv.genState.tyGen h_name
      have h_gen_subst : Env_gen.stateSubstInfo = Env2.stateSubstInfo :=
        TEnv.genTyVar_subst Env2 fresh_name Env_gen h_genv
      have h_cs_P : ∀ w, w ∈ Constraints.freeVars
          [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])] → P w := by
        intro w hw
        simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
          LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw | hw | hw
        · exact h_ih1'.1 w hw
        · exact h_ih2'.1 w hw
        · subst hw; exact h_fresh_P
      have h_gensub_k : ∀ w, w ∈ Maps.keys Env_gen.stateSubstInfo.subst → P w := by
        intro w hw; rw [h_gen_subst] at hw; exact h_ih2'.2 w (Or.inl hw)
      have h_gensub_v : ∀ w, w ∈ Subst.freeVars Env_gen.stateSubstInfo.subst → P w := by
        intro w hw; rw [h_gen_subst] at hw; exact h_ih2'.2 w (Or.inr hw)
      have h_unify_pred := Constraints.unify_pred h_unify P h_cs_P h_gensub_k h_gensub_v
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [toLMonoTy] at hv
        rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset substInfo.subst
          (.ftvar fresh_name) hv) with h | h
        · simp only [LMonoTy.freeVars, List.mem_singleton] at h; subst h; exact h_fresh_P
        · exact h_unify_pred.2 v h
      · rw [h_subeq] at hv
        rcases hv with hv | hv
        · exact h_unify_pred.1 v (Maps.keys_remove_subset substInfo.subst fresh_name v hv)
        · exact h_unify_pred.2 v (Subst.freeVars_remove_subset substInfo.subst fresh_name v hv)
    case h_abs =>
      intro m name bty body et C Env Env' xv xty Env1 et_body Env2
        h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
        h_ih h_ctx h_sub
      subst h_et h_env'
      have h_aw := h_envwf.aliasesWF
      have h_xty_P : ∀ v, v ∈ LMonoTy.freeVars xty → P v := by
        intro v hv
        rcases typeBoundVar_xty_freeVars C Env bty xv xty Env1 h_tbv h_aw v hv with
          h_kv | ⟨k, hk⟩
        · exact h_ctx v h_kv
        · exact h_gen v k hk
      have h_sub1_stateEq : Env1.stateSubstInfo = Env.stateSubstInfo :=
        typeBoundVar_stateSubstInfo C Env bty xv xty Env1 h_tbv
      have h_sub1 : ∀ v, (v ∈ Maps.keys Env1.stateSubstInfo.subst ∨
          v ∈ Subst.freeVars Env1.stateSubstInfo.subst) → P v := by
        intro v hv; rw [h_sub1_stateEq] at hv; exact h_sub v hv
      have h_ctx1 : ∀ v, v ∈ TContext.knownTypeVars Env1.context → P v := by
        intro v hv
        rcases typeBoundVar_knownTypeVars_cases C Env bty xv xty Env1 h_tbv v hv with
          h_old | h_new
        · exact h_ctx v h_old
        · exact h_xty_P v h_new
      have h_ih' := h_ih h_ctx1 h_sub1
      have h_erase_subst : (Env2.eraseFromContext xv).stateSubstInfo = Env2.stateSubstInfo := by
        simp only [TEnv.eraseFromContext, TEnv.updateContext]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h_eq : (LExpr.varCloseT 0 xv et_body).toLMonoTy = et_body.toLMonoTy :=
          varCloseT_toLMonoTy 0 xv et_body
        have hv' : v ∈ LMonoTy.freeVars (LMonoTy.subst Env2.stateSubstInfo.subst
            (LMonoTy.tcons "arrow" [xty, et_body.toLMonoTy])) := by
          rw [← h_eq]; exact hv
        rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset Env2.stateSubstInfo.subst
          _ hv') with h_arrow | h_sub2
        · simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil, List.mem_append] at h_arrow
          rcases h_arrow with h_x | h_b
          · exact h_xty_P v h_x
          · exact h_ih'.1 v h_b
        · exact h_ih'.2 v (Or.inr h_sub2)
      · rw [h_erase_subst] at hv; exact h_ih'.2 v hv
    case h_quant =>
      intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3
        h_res h_tbv h_res_body h_res_tr h_et h_env' h_body_ty_bool h_envwf h_ne h_fwf
        h_envwf1 h_ne1 h_aliases_eq h_envwf2 h_ctx2 h_ih_body h_ih_tr h_ctx h_sub
      subst h_et h_env'
      have h_aw := h_envwf.aliasesWF
      have h_xty_P : ∀ v, v ∈ LMonoTy.freeVars xty → P v := by
        intro v hv
        rcases typeBoundVar_xty_freeVars C Env bty xv xty Env1 h_tbv h_aw v hv with
          h_kv | ⟨k, hk⟩
        · exact h_ctx v h_kv
        · exact h_gen v k hk
      have h_sub1_stateEq : Env1.stateSubstInfo = Env.stateSubstInfo :=
        typeBoundVar_stateSubstInfo C Env bty xv xty Env1 h_tbv
      have h_sub1 : ∀ v, (v ∈ Maps.keys Env1.stateSubstInfo.subst ∨
          v ∈ Subst.freeVars Env1.stateSubstInfo.subst) → P v := by
        intro v hv; rw [h_sub1_stateEq] at hv; exact h_sub v hv
      have h_ctx1 : ∀ v, v ∈ TContext.knownTypeVars Env1.context → P v := by
        intro v hv
        rcases typeBoundVar_knownTypeVars_cases C Env bty xv xty Env1 h_tbv v hv with
          h_old | h_new
        · exact h_ctx v h_old
        · exact h_xty_P v h_new
      have h_ih_body' := h_ih_body h_ctx1 h_sub1
      have h_ctx2' : ∀ v, v ∈ TContext.knownTypeVars Env2.context → P v := by
        rw [h_ctx2]; exact h_ctx1
      have h_ih_tr' := h_ih_tr h_ctx2' h_ih_body'.2
      have h_erase_subst : (Env3.eraseFromContext xv).stateSubstInfo = Env3.stateSubstInfo := by
        simp only [TEnv.eraseFromContext, TEnv.updateContext]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [toLMonoTy, LMonoTy.freeVars, LMonoTys.freeVars] at hv
        exact absurd hv (by simp)
      · rw [h_erase_subst] at hv; exact h_ih_tr'.2 v hv
    case h_eq =>
      intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
        h_res h1 h2 h_unify h_et h_subeq h_abs1 h_abs2
        h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_ih1 h_ih2 h_ctx h_sub
      subst h_et
      have h_ih1' := h_ih1 h_ctx h_sub
      have h_ctx1' : ∀ v, v ∈ TContext.knownTypeVars Env1.context → P v := by
        rw [h_ctx1]; exact h_ctx
      have h_ih2' := h_ih2 h_ctx1' h_ih1'.2
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [toLMonoTy, LMonoTy.freeVars, LMonoTys.freeVars] at hv
        exact absurd hv (by simp)
      · rw [h_subeq] at hv
        have h_cs_P : ∀ w, w ∈ Constraints.freeVars [(e1t.toLMonoTy, e2t.toLMonoTy)] → P w := by
          intro w hw
          simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
            List.mem_append] at hw
          rcases hw with hw | hw
          · exact h_ih1'.1 w hw
          · exact h_ih2'.1 w hw
        have h_unify_pred := Constraints.unify_pred h_unify P h_cs_P
          (fun w hw => h_ih2'.2 w (Or.inl hw)) (fun w hw => h_ih2'.2 w (Or.inr hw))
        rcases hv with hv | hv
        · exact h_unify_pred.1 v hv
        · exact h_unify_pred.2 v hv
    case h_ite =>
      intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
        h_res hc ht he h_unify h_et h_subeq h_abs2 h_abs3
        h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_envwf3 h_ctx3
        h_ihc h_iht h_ihe h_ctx h_sub
      subst h_et
      have h_ihc' := h_ihc h_ctx h_sub
      have h_ctx1' : ∀ v, v ∈ TContext.knownTypeVars Env1.context → P v := by
        rw [h_ctx1]; exact h_ctx
      have h_iht' := h_iht h_ctx1' h_ihc'.2
      have h_ctx2' : ∀ v, v ∈ TContext.knownTypeVars Env2.context → P v := by
        rw [h_ctx2]; exact h_ctx
      have h_ihe' := h_ihe h_ctx2' h_iht'.2
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [toLMonoTy] at hv; exact h_iht'.1 v hv
      · rw [h_subeq] at hv
        have h_cs_P : ∀ w, w ∈ Constraints.freeVars
            [(ct.toLMonoTy, LMonoTy.bool), (tht.toLMonoTy, elt.toLMonoTy)] → P w := by
          intro w hw
          simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
            LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append] at hw
          rcases hw with hw | hw | hw
          · exact h_ihc'.1 w hw
          · exact h_iht'.1 w hw
          · exact h_ihe'.1 w hw
        have h_unify_pred := Constraints.unify_pred h_unify P h_cs_P
          (fun w hw => h_ihe'.2 w (Or.inl hw)) (fun w hw => h_ihe'.2 w (Or.inr hw))
        rcases hv with hv | hv
        · exact h_unify_pred.1 v hv
        · exact h_unify_pred.2 v hv
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨Env0, h_env0⟩ : ∃ Env0, Env0 = (if Env.context.types.isEmpty then
      Env.updateContext { Env.context with types := [[]] } else Env) := ⟨_, rfl⟩
  rw [← h_env0] at h
  generalize h_ra : resolveAux C Env0 e = res at h
  cases res with
  | error => simp at h
  | ok val =>
    obtain ⟨et0, EnvR⟩ := val
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, h_env⟩ := h
    have h_ne0 : Env0.context.types ≠ [] := by
      rw [h_env0]; split
      · simp only [TEnv.updateContext, TEnv.context]; exact List.cons_ne_nil _ _
      · rename_i h_not; intro h_abs; rw [h_abs] at h_not
        exact h_not rfl
    have h_ctx0 : ∀ v, v ∈ TContext.knownTypeVars Env0.context → P v := by
      intro v hv; rw [h_env0] at hv; revert hv; split
      · intro hv
        change v ∈ TContext.types.knownTypeVars [[]] at hv
        simp [TContext.types.knownTypeVars, TContext.types.knownTypeVars.go] at hv
      · intro hv; exact h_ctx v hv
    have h_sub0 : ∀ v, (v ∈ Maps.keys Env0.stateSubstInfo.subst ∨
        v ∈ Subst.freeVars Env0.stateSubstInfo.subst) → P v := by
      intro v hv
      have h_s0 : Env0.stateSubstInfo = Env.stateSubstInfo := by
        rw [h_env0]; split
        · simp only [TEnv.updateContext]
        · rfl
      rw [h_s0] at hv; exact h_sub v hv
    have h_envwf0 : TEnvWF Env0 := by
      rw [h_env0]; split
      · rename_i h_emp
        simp only [TEnv.updateContext]
        refine ⟨h_envwf.aliasesWF, h_envwf.substFreshForGen, ?_, ?_, ?_⟩
        · intro v hv n hn
          change v ∈ TContext.types.knownTypeVars [[]] at hv
          simp [TContext.types.knownTypeVars, TContext.types.knownTypeVars.go] at hv
        · intro y ty hf
          change Maps.find? [[]] y = some ty at hf
          simp [Maps.find?, Map.find?] at hf
        · intro y ty hf
          change Maps.find? [[]] y = some ty at hf
          simp [Maps.find?, Map.find?] at hf
      · exact h_envwf
    have h_aux_res := h_aux e et0 C Env0 EnvR h_ra h_envwf0 h_ne0 h_fwf h_ctx0 h_sub0
    subst h_et h_env
    refine ⟨fun v hv => ?_, h_aux_res.2⟩
    rw [applySubstT_toLMonoTy] at hv
    rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset EnvR.stateSubstInfo.subst
      et0.toLMonoTy hv) with h_t | h_s
    · exact h_aux_res.1 v h_t
    · exact h_aux_res.2 v (Or.inr h_s)

/-! ### Layer 3: Main induction -/

/-- Core soundness lemma: for any substitution `S` absorbing the output substitution,
    the resolved and substituted expression satisfies `HasTypeA`. Proved by
    well-founded induction on expression size. -/
private theorem resolveAux_HasTypeA_aux [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
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
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
    rename_i heq_inferConst
    split at heq_inferConst
    · simp at heq_inferConst ⊢
      rw [← heq_inferConst]
      simp only []
      rw [LConst.ty_subst]
      exact HasTypeA.const
    · simp at heq_inferConst
  case h_op =>
    intro m o oty et C Env Env' h h_envwf h_ne h_fwf h_resolved S h_absorbs
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_errs h
    split at h
    · cases h
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
    · elim_errs h
      cases h
      simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
      exact HasTypeA.op
  case h_fvar =>
    intro m x fty et C Env Env' h h_envwf h_ne h_fwf h_resolved S h_absorbs
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i ty_env h_infer
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, h_env⟩ := h
    subst h_et h_env
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
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
    have h_resolved1 : TContext.AliasesResolved Env1.context := h_ctx1 ▸ h_resolved
    have h_subst_e1t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e1t.toLMonoTy) =
        LMonoTy.subst S e1t.toLMonoTy := by
      rw [← LMonoTy.subst_remove_not_fv substInfo.subst fresh_name
            e1t.toLMonoTy h_e1t_no_fresh]
      exact LMonoTy.subst_absorbs S (Maps.remove substInfo.subst fresh_name)
        e1t.toLMonoTy h_abs_S_rem
    have h_subst_e2t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e2t.toLMonoTy) =
        LMonoTy.subst S e2t.toLMonoTy := by
      rw [← LMonoTy.subst_remove_not_fv substInfo.subst fresh_name
            e2t.toLMonoTy h_e2t_no_fresh]
      exact LMonoTy.subst_absorbs S (Maps.remove substInfo.subst fresh_name)
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
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
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
      simp [TEnv.eraseFromContext, TEnv.updateContext] at h_absorbs
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
    intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3
      h_res h_tbv h_res_body h_res_tr h_et h_env' h_body_ty_bool h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr h_resolved S h_absorbs
    subst h_et h_env'
    have h_ne2 : Env2.context.types ≠ [] := h_ctx2 ▸ h_ne1
    have h_resolved1 : TContext.AliasesResolved Env1.context := by
      intro a h_mem; rw [h_aliases_eq] at h_mem ⊢; exact h_resolved a h_mem
    have h_resolved2 : TContext.AliasesResolved Env2.context := h_ctx2 ▸ h_resolved1
    have h_abs_Env3 : S.absorbs Env3.stateSubstInfo.subst := by
      simp [TEnv.eraseFromContext, TEnv.updateContext] at h_absorbs
      exact h_absorbs
    have h_abs_Env2 : S.absorbs Env2.stateSubstInfo.subst := by
      have h_props_tr := resolveAux_properties
        (LExpr.varOpen 0 (xv, some xty) triggers) et_tr C Env2 Env3 h_res_tr
        h_ne2 h_envwf2.aliasesWF h_fwf h_envwf2.substFreshForGen
        h_envwf2.ctxFreshForGen h_envwf2.boundVarsFresh
      exact Subst.absorbs_trans _ _ _ h_props_tr.absorbs h_abs_Env3
    have h_ih_b := h_ih_body h_resolved1 S h_abs_Env2
    have h_ih_t := h_ih_tr h_resolved2 S h_abs_Env3
    show HasTypeA []
      (applySubstT (.quant ⟨m, LMonoTy.subst Env3.stateSubstInfo.subst xty⟩
        qk name (some (LMonoTy.subst Env3.stateSubstInfo.subst xty))
        (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body)) S).unresolved
      ((applySubstT (.quant ⟨m, LMonoTy.subst Env3.stateSubstInfo.subst xty⟩
        qk name (some (LMonoTy.subst Env3.stateSubstInfo.subst xty))
        (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body)) S).toLMonoTy)
    simp only [toLMonoTy]
    simp only [applySubstT, replaceMetadata, unresolved]
    change HasTypeA []
      (.quant m qk name (some (LMonoTy.subst S (LMonoTy.subst Env3.stateSubstInfo.subst xty)))
        (applySubstT (LExpr.varCloseT 0 xv et_tr) S).unresolved
        (applySubstT (LExpr.varCloseT 0 xv et_body) S).unresolved)
      LMonoTy.bool
    rw [applySubstT_varCloseT_comm (xv := xv) (et := et_tr),
        applySubstT_varCloseT_comm (xv := xv) (et := et_body)]
    rw [LMonoTy.subst_absorbs S Env3.stateSubstInfo.subst xty h_abs_Env3]
    refine HasTypeA.quant (τ_tr := (LExpr.varCloseT 0 xv (applySubstT et_tr S)).toLMonoTy) ?_ ?_
    · have h_ctx_xv : Env1.context.types.find? xv = some (.forAll [] xty) :=
        typeBoundVar_adds_to_context C Env bty xv xty Env1 h_tbv
      have h_ctx_xv2 : Env2.context.types.find? xv = some (.forAll [] xty) :=
        h_ctx2 ▸ h_ctx_xv
      have h_xty_af2 : LMonoTy.aliasFree Env2.context.aliases xty := by
        rw [show Env2.context.aliases = Env1.context.aliases from by rw [h_ctx2]]
        rw [h_aliases_eq]
        exact typeBoundVar_xty_aliasFree C Env bty xv xty Env1 h_tbv h_resolved
      have h_annot_tr_raw : LExprT.allFvarAnnot xv xty et_tr :=
        resolveAux_allFvarAnnot C Env2 Env3
          (LExpr.varOpen 0 (xv, some xty) triggers) et_tr xv xty h_res_tr h_ctx_xv2
          h_envwf2 h_ne2 h_fwf h_xty_af2
      have h_annot_tr : LExprT.allFvarAnnot xv (LMonoTy.subst S xty) (applySubstT et_tr S) :=
        applySubstT_allFvarAnnot xv xty et_tr S h_annot_tr_raw
      exact varCloseT_unresolved_HasTypeA_nil xv (LMonoTy.subst S xty)
        (applySubstT et_tr S) h_ih_t h_annot_tr
    · have h_body_ty_eq : (LExpr.varCloseT 0 xv (applySubstT et_body S)).toLMonoTy = LMonoTy.bool := by
        rw [varCloseT_toLMonoTy, applySubstT_toLMonoTy, h_body_ty_bool, LMonoTy.subst_bool]
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
    have h_resolved1 : TContext.AliasesResolved Env1.context := h_ctx1 ▸ h_resolved
    have h_abs_unify := Constraints.unify_absorbs _ _ _ h_unify
    have h_abs_e2 : S.absorbs Env2.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs_unify h_absorbs
    have h_abs_e1 : S.absorbs Env1.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ h_abs2 h_abs_e2
    have h_eq_types : toLMonoTy (applySubstT e1t S) = toLMonoTy (applySubstT e2t S) := by
      rw [applySubstT_toLMonoTy, applySubstT_toLMonoTy]
      have h_sound := Constraints.unify_sound _ _ _ h_unify
      have h_pair := h_sound _ (List.Mem.head _)
      simp at h_pair
      exact LMonoTy.subst_eq_of_absorbs S substInfo.subst _ _ h_absorbs h_pair
    simp [applySubstT, replaceMetadata, unresolved, toLMonoTy]
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
    have h_resolved1 : TContext.AliasesResolved Env1.context := h_ctx1 ▸ h_resolved
    have h_resolved2 : TContext.AliasesResolved Env2.context := h_ctx2 ▸ h_resolved
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
      simp [LMonoTy.subst_bool] at h_p; exact h_p
    have h_th_el : LMonoTy.subst substInfo.subst tht.toLMonoTy =
        LMonoTy.subst substInfo.subst elt.toLMonoTy := by
      have h_p := h_sound _ (List.Mem.tail _ (List.Mem.head _))
      simp at h_p; exact h_p
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
  exact resolveAux_HasTypeA_aux e et C Env Env' h h_envwf h_ne h_fwf h_resolved
    Env'.stateSubstInfo.subst h_absorbs

/-- `resolveAux` produces an `AbsWF` expression: every abs subnode in the result
    carries arrow-typed metadata. Proved by `resolveAux_ind`; the abs case fixes
    the metadata to `subst _ (.tcons "arrow" [xty, _])`, which is an arrow. -/
theorem resolveAux_AbsWF [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (e : LExpr T.mono) (et : LExprT T.mono)
    (h_res : resolveAux C Env e = Except.ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    LExprT.AbsWF et := by
  apply resolveAux_ind
    (P := fun _e et _C _Env _Env' => LExprT.AbsWF et)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res h_envwf h_ne h_fwf
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    rename_i v1 h_ic; obtain ⟨ty, Env1⟩ := v1; simp at h_res
    obtain ⟨h_et, _⟩ := h_res; subst h_et; trivial
  case h_op =>
    intro m o oty et C Env Env' h_res h_envwf h_ne h_fwf
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_errs h_res
    split at h_res
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et; trivial
    · elim_errs h_res
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et; trivial
  case h_fvar =>
    intro m x fty et C Env Env' h_res h_envwf h_ne h_fwf
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    rename_i v1 h_infer
    obtain ⟨ty_res, Env_res⟩ := v1
    simp at h_res
    obtain ⟨h_et, _⟩ := h_res; subst h_et; trivial
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      h_res h1 h2 h_gen h_unify h_et _ _ _ _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2
    subst h_et
    exact ⟨h_ih1, h_ih2⟩
  case h_abs =>
    intro m name bty body et C Env Env' xv xty Env1 et_body Env2
      h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq h_ih
    subst h_et
    simp only [LExprT.AbsWF]
    refine ⟨?_, varCloseT_AbsWF 0 xv et_body h_ih⟩
    rw [LMonoTy.subst_tcons_pair]
    simp only [LMonoTy.isArrow, Option.isSome_some]
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3
      h_res h_tbv h_res_body h_res_tr h_et h_env' _ h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr
    subst h_et
    exact ⟨varCloseT_AbsWF 0 xv et_tr h_ih_tr, varCloseT_AbsWF 0 xv et_body h_ih_body⟩
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      h_res h1 h2 h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2
    subst h_et
    exact ⟨h_ih1, h_ih2⟩
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      h_res hc ht he h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_envwf3 h_ctx3 h_ihc h_iht h_ihe
    subst h_et
    exact ⟨h_ihc, h_iht, h_ihe⟩

/-- `resolve` produces an `AbsWF` expression. Public interface, peeling the
    context-initialization wrapper before delegating to `resolveAux_AbsWF`. -/
theorem resolve_AbsWF [DecidableEq T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env : TEnv T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = Except.ok (e_typed, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactoryWF C.functions) :
    LExprT.AbsWF e_typed := by
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
    have h_ne0 : (if Env.context.types.isEmpty then
        Env.updateContext { types := [[]], aliases := Env.context.aliases }
      else Env).context.types ≠ [] := by
      split
      · exact List.cons_ne_nil _ _
      · rename_i h_not_empty
        intro h_abs
        simp_all
        contradiction
    exact applySubstT_AbsWF val.fst val.snd.stateSubstInfo.subst
      (resolveAux_AbsWF C _ val.snd e val.fst h_res h_envwf0 h_ne0 h_fwf)

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

/-! ## `EqModuloAnnotations` and `resolve_eqModuloAnnotations`

Two expressions are equal modulo annotations if they have the same structure
(constructors, identifiers, constants) but may differ in metadata and type
annotations. We prove that `resolve` preserves this structure.
-/

namespace Lambda
open LExpr

section EqModuloAnnotations

/-- Two expressions over param types sharing the same `IDMeta` are equal modulo
    annotations: same constructors, same identifiers, same constants, but
    potentially different metadata and type annotations. -/
def EqModuloAnnotations (e₁ : LExpr ⟨⟨M₁, IDMeta⟩, Ty₁⟩) (e₂ : LExpr ⟨⟨M₂, IDMeta⟩, Ty₂⟩) : Prop :=
  match e₁, e₂ with
  | .const _ c₁, .const _ c₂ => c₁ = c₂
  | .op _ o₁ _, .op _ o₂ _ => o₁ = o₂
  | .bvar _ i₁, .bvar _ i₂ => i₁ = i₂
  | .fvar _ x₁ _, .fvar _ x₂ _ => x₁ = x₂
  | .app _ fn₁ arg₁, .app _ fn₂ arg₂ =>
      EqModuloAnnotations fn₁ fn₂ ∧ EqModuloAnnotations arg₁ arg₂
  | .abs _ n₁ _ body₁, .abs _ n₂ _ body₂ =>
      n₁ = n₂ ∧ EqModuloAnnotations body₁ body₂
  | .quant _ qk₁ n₁ _ tr₁ body₁, .quant _ qk₂ n₂ _ tr₂ body₂ =>
      qk₁ = qk₂ ∧ n₁ = n₂ ∧ EqModuloAnnotations tr₁ tr₂ ∧ EqModuloAnnotations body₁ body₂
  | .ite _ c₁ t₁ f₁, .ite _ c₂ t₂ f₂ =>
      EqModuloAnnotations c₁ c₂ ∧ EqModuloAnnotations t₁ t₂ ∧ EqModuloAnnotations f₁ f₂
  | .eq _ l₁ r₁, .eq _ l₂ r₂ =>
      EqModuloAnnotations l₁ l₂ ∧ EqModuloAnnotations r₁ r₂
  | _, _ => False

private theorem eqModuloAnnotations_trans
    {e₁ : LExpr ⟨⟨M₁, IDMeta⟩, Ty₁⟩} {e₂ : LExpr ⟨⟨M₂, IDMeta⟩, Ty₂⟩} {e₃ : LExpr ⟨⟨M₃, IDMeta⟩, Ty₃⟩}
    (h₁₂ : EqModuloAnnotations e₁ e₂) (h₂₃ : EqModuloAnnotations e₂ e₃) :
    EqModuloAnnotations e₁ e₃ := by
  induction e₁ generalizing e₂ e₃ <;>
  cases e₂ <;> simp [EqModuloAnnotations] at h₁₂ <;>
  cases e₃ <;> simp [EqModuloAnnotations] at h₂₃ ⊢ <;>
  grind

private theorem applySubstT_unresolved_eqMod {T : LExprParams} (et : LExprT T.mono) (S : Subst) :
    EqModuloAnnotations (applySubstT et S).unresolved et.unresolved := by
  induction et with
  | const => simp [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
  | op => simp [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
  | bvar => simp [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
  | fvar => simp [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
  | app _ e1 e2 ih1 ih2 =>
    simp only [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
    exact ⟨ih1, ih2⟩
  | abs m name ty e ih =>
    simp only [applySubstT, replaceMetadata, unresolved]
    split <;> split <;> (simp only [EqModuloAnnotations]; exact ⟨trivial, ih⟩)
  | quant m qk name ty tr e ih_tr ih_e =>
    simp only [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
    exact ⟨trivial, trivial, ih_tr, ih_e⟩
  | ite _ c t f ih_c ih_t ih_f =>
    simp only [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
    exact ⟨ih_c, ih_t, ih_f⟩
  | eq _ e1 e2 ih1 ih2 =>
    simp only [applySubstT, replaceMetadata, unresolved, EqModuloAnnotations]
    exact ⟨ih1, ih2⟩

private theorem varCloseT_varOpen_eqModuloAnnotations {T : LExprParams} [DecidableEq T.IDMeta]
    (k : Nat) (xv : T.Identifier) (xty : LMonoTy)
    (et : LExprT T.mono) (body : LExpr T.mono)
    (h : EqModuloAnnotations et.unresolved (LExpr.varOpen k (xv, some xty) body))
    (h_fresh : xv ∉ LExpr.getVars body) :
    EqModuloAnnotations (LExpr.varCloseT k xv et).unresolved body := by
  induction et generalizing k body with
  | const m c =>
    cases body <;> simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢
    · exact h
    · split at h <;> simp [EqModuloAnnotations] at h
  | op m o ty =>
    cases body <;> simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢
    · exact h
    · split at h <;> simp [EqModuloAnnotations] at h
  | bvar m i =>
    cases body <;> simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢
    split at h
    · simp [EqModuloAnnotations] at h
    · exact h
  | fvar m x fty =>
    cases body with
    | bvar m' i' =>
      simp only [varOpen, substK, unresolved] at h ⊢
      split at h
      · simp only [EqModuloAnnotations] at h
        subst h
        simp only [LExpr.varCloseT, beq_self_eq_true, ite_true, unresolved, EqModuloAnnotations]
        rename_i h_eq; exact (beq_iff_eq.mp h_eq).symm
      · simp [EqModuloAnnotations] at h
    | fvar m' y fty' =>
      simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h
      subst h
      simp only [LExpr.getVars, List.mem_singleton] at h_fresh
      simp only [LExpr.varCloseT]
      split
      · rename_i h_eq
        exact absurd (beq_iff_eq.mp h_eq) h_fresh
      · simp [unresolved, EqModuloAnnotations]
    | _ => simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h
  | app m e1 e2 ih1 ih2 =>
    cases body with
    | app m' e1' e2' =>
      simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢
      simp only [LExpr.getVars, List.mem_append] at h_fresh
      exact ⟨ih1 k _ h.1 (fun hm => h_fresh (Or.inl hm)),
             ih2 k _ h.2 (fun hm => h_fresh (Or.inr hm))⟩
    | bvar _ _ => simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢; split at h <;> simp [EqModuloAnnotations] at h
    | _ => simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h
  | abs m name ty e ih =>
    cases body with
    | abs m' name' ty' body' =>
      simp only [varOpen, substK] at h
      simp only [LExpr.getVars] at h_fresh
      simp only [unresolved] at h
      split at h
      · simp only [EqModuloAnnotations] at h
        obtain ⟨h_n, h_body⟩ := h
        simp only [LExpr.varCloseT, unresolved]
        split <;> (simp only [EqModuloAnnotations]; exact ⟨h_n, ih (k + 1) _ h_body h_fresh⟩)
      · simp only [EqModuloAnnotations] at h
        obtain ⟨h_n, h_body⟩ := h
        simp only [LExpr.varCloseT, unresolved]
        split <;> (simp only [EqModuloAnnotations]; exact ⟨h_n, ih (k + 1) _ h_body h_fresh⟩)
    | bvar _ _ =>
      simp only [varOpen, substK, unresolved] at h
      split at h <;> (split at h <;> simp_all [EqModuloAnnotations])
    | _ =>
      simp only [varOpen, substK, unresolved] at h
      split at h <;> simp [EqModuloAnnotations] at h
  | quant m qk name ty tr e ih_tr ih_e =>
    cases body with
    | quant m' qk' name' ty' tr' body' =>
      simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h ⊢
      simp only [LExpr.getVars, List.mem_append] at h_fresh
      obtain ⟨h_qk, h_n, h_tr, h_body⟩ := h
      simp only [LExpr.varCloseT, unresolved, EqModuloAnnotations]
      exact ⟨h_qk, h_n,
             ih_tr (k + 1) _ h_tr (fun hm => h_fresh (Or.inl hm)),
             ih_e (k + 1) _ h_body (fun hm => h_fresh (Or.inr hm))⟩
    | bvar _ _ => simp only [varOpen, substK, unresolved] at h ⊢; split at h <;> simp [EqModuloAnnotations] at h
    | _ => simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h
  | ite m c t f ih_c ih_t ih_f =>
    cases body with
    | ite m' c' t' f' =>
      simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢
      simp only [LExpr.getVars, List.mem_append] at h_fresh
      exact ⟨ih_c k _ h.1 (fun hm => h_fresh (Or.inl (Or.inl hm))),
             ih_t k _ h.2.1 (fun hm => h_fresh (Or.inl (Or.inr hm))),
             ih_f k _ h.2.2 (fun hm => h_fresh (Or.inr hm))⟩
    | bvar _ _ => simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢; split at h <;> simp [EqModuloAnnotations] at h
    | _ => simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h
  | eq m e1 e2 ih1 ih2 =>
    cases body with
    | eq m' e1' e2' =>
      simp only [varOpen, substK, unresolved, LExpr.varCloseT, EqModuloAnnotations] at h ⊢
      simp only [LExpr.getVars, List.mem_append] at h_fresh
      exact ⟨ih1 k _ h.1 (fun hm => h_fresh (Or.inl hm)),
             ih2 k _ h.2 (fun hm => h_fresh (Or.inr hm))⟩
    | bvar _ _ => simp only [varOpen, substK, unresolved] at h ⊢; split at h <;> simp [EqModuloAnnotations] at h
    | _ => simp only [varOpen, substK, unresolved, EqModuloAnnotations] at h

private theorem resolveAux_eqModuloAnnotations {T : LExprParams}
    [DecidableEq T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_wf : ResolveAuxWF Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : WellScoped e Env.context) :
    EqModuloAnnotations et.unresolved e := by
  apply resolveAux_ind
    (P := fun e et C Env Env' => WellScoped e Env.context → EqModuloAnnotations et.unresolved e)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_wf.envwf) (h_ne := h_wf.ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res h_envwf h_ne h_fwf h_ws
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_et, _⟩ := h_res; subst h_et
    simp [unresolved, EqModuloAnnotations]
  case h_op =>
    intro m o oty et C Env Env' h_res h_envwf h_ne h_fwf h_ws
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_errs h_res
    split at h_res
    · cases h_res; simp [unresolved, EqModuloAnnotations]
    · elim_errs h_res; cases h_res; simp [unresolved, EqModuloAnnotations]
  case h_fvar =>
    intro m x fty et C Env Env' h_res h_envwf h_ne h_fwf h_ws
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    elim_err h_res
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_et, _⟩ := h_res; subst h_et
    simp [unresolved, EqModuloAnnotations]
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      h_res h1 h2 h3 h_unify h_et _ _ _ _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2 h_ws
    subst h_et
    have h_ws1 : WellScoped e1 Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars]; exact Or.inl hx)
    have h_ws2 : WellScoped e2 Env1.context :=
      h_ctx1 ▸ (fun x hx => h_ws x (by simp [LExpr.freeVars]; exact Or.inr hx))
    simp only [unresolved, EqModuloAnnotations]
    exact ⟨h_ih1 h_ws1, h_ih2 h_ws2⟩
  case h_abs =>
    intro m name bty body et C Env Env' xv xty Env1 et_body Env2
      h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq h_ih h_ws
    subst h_et
    have h_ws_body : WellScoped body Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars]; exact hx)
    have h_xv_fresh := typeBoundVar_xv_not_in_knownVars C Env bty xv xty Env1 h_tbv
    have h_fresh := WellScoped_fresh_not_in_getVars body Env.context xv h_ws_body h_xv_fresh
    have h_ws_open := WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 body h_tbv h_ws_body
    have h_ih_body := h_ih h_ws_open
    simp only [unresolved]
    split <;> (simp only [EqModuloAnnotations];
               exact ⟨trivial, varCloseT_varOpen_eqModuloAnnotations 0 xv xty et_body body h_ih_body h_fresh⟩)
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3
      h_res h_tbv h_res_body h_res_tr h_et h_env' _ h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr h_ws
    subst h_et
    have h_ws_body : WellScoped body Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars]; exact Or.inr hx)
    have h_ws_tr : WellScoped triggers Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars]; exact Or.inl hx)
    have h_xv_fresh := typeBoundVar_xv_not_in_knownVars C Env bty xv xty Env1 h_tbv
    have h_fresh_body := WellScoped_fresh_not_in_getVars body Env.context xv h_ws_body h_xv_fresh
    have h_fresh_tr := WellScoped_fresh_not_in_getVars triggers Env.context xv h_ws_tr h_xv_fresh
    have h_ws_open_body := WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 body h_tbv h_ws_body
    have h_ws_open_tr := WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 triggers h_tbv h_ws_tr
    have h_ws_open_tr' : WellScoped (LExpr.varOpen 0 (xv, some xty) triggers) Env2.context :=
      h_ctx2 ▸ h_ws_open_tr
    have h_ih_b := h_ih_body h_ws_open_body
    have h_ih_t := h_ih_tr h_ws_open_tr'
    simp only [unresolved, EqModuloAnnotations]
    exact ⟨trivial, trivial,
           varCloseT_varOpen_eqModuloAnnotations 0 xv xty et_tr triggers h_ih_t h_fresh_tr,
           varCloseT_varOpen_eqModuloAnnotations 0 xv xty et_body body h_ih_b h_fresh_body⟩
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      h_res h1 h2 h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_ih1 h_ih2 h_ws
    subst h_et
    have h_ws1 : WellScoped e1 Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars]; exact Or.inl hx)
    have h_ws2 : WellScoped e2 Env1.context :=
      h_ctx1 ▸ (fun x hx => h_ws x (by simp [LExpr.freeVars]; exact Or.inr hx))
    simp only [unresolved, EqModuloAnnotations]
    exact ⟨h_ih1 h_ws1, h_ih2 h_ws2⟩
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      h_res hc ht he h_unify h_et _ _ _ h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2
      h_envwf3 h_ctx3 h_ihc h_iht h_ihe h_ws
    subst h_et
    have h_wsc : WellScoped c Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; exact Or.inl hx)
    have h_wsth : WellScoped th Env1.context :=
      h_ctx1 ▸ (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; exact Or.inr (Or.inl hx)))
    have h_wsel : WellScoped el Env2.context :=
      h_ctx2 ▸ (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; exact Or.inr (Or.inr hx)))
    simp only [unresolved, EqModuloAnnotations]
    exact ⟨h_ihc h_wsc, h_iht h_wsth, h_ihe h_wsel⟩
  exact h_ws

/-- `resolve` only changes annotations: the unresolved output is structurally
    identical to the input. -/
theorem resolve_eqModuloAnnotations {T : LExprParams}
    [DecidableEq T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env : TEnv T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = Except.ok (e_typed, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_fwf : FactoryWF C.functions)
    (h_ws : WellScoped e Env.context) :
    EqModuloAnnotations e_typed.unresolved e := by
  have h_not_empty : Env.context.types.isEmpty = false := by
    cases h_types : Env.context.types <;> simp_all [Maps.isEmpty]
  simp only [LExpr.resolve, h_not_empty, Bind.bind, Except.bind] at h
  match h_res : resolveAux C Env e with
  | .error _ => simp [h_res] at h
  | .ok (et, Env'') =>
    simp [h_res] at h
    obtain ⟨h_et, h_env⟩ := h
    subst h_et h_env
    exact eqModuloAnnotations_trans
      (applySubstT_unresolved_eqMod et Env''.stateSubstInfo.subst)
      (resolveAux_eqModuloAnnotations e et C Env Env'' h_res
        ⟨h_envwf, h_ne, h_resolved⟩ h_fwf h_ws)

end EqModuloAnnotations

end Lambda

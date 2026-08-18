/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LTyUnifyProps
import all Strata.Util.HMap
import all Strata.Util.HMaps
import all Strata.DL.Lambda.Identifiers
import all Strata.DL.Util.Func
import all Strata.Util.ListMap
import all Strata.Util.ListMapProps
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.FactoryProps
public import Strata.DL.Lambda.LExprTypeSpec
public meta import Init.Grind.Cases

/-! ## Free-variable properties of `LExprT` operators

Properties of the `LExprT` operators defined in `Strata.DL.Lambda.LExprT`
concerning the free variables (`LExpr.getVars`) of their output.

Two families live here:

* the reshaping operators (`unresolved`, `varCloseT`) — `getVars` is invariant
  under `unresolved` and `varCloseT k xv` drops `xv` and adds nothing new; and
* the type-inference operators (`resolve`, `resolveAux`, `typeBoundVar`,
  `inferFVar`) — which free-variable names can survive resolution, stated in
  terms of the input context's known variables.

### Key results
* `getVars_unresolved` — `getVars` is invariant under `unresolved` (it only
  strips type annotations).
* `getVars_varCloseT_subset` — closing binder `xv` drops `xv` from the free vars
  and adds nothing new.
* `resolve_getVars_mem_knownVars` — every output free var of `resolve` is a
  known var of the input context (freshness-free, routed through the output side).
* `resolve_knownVars_subset` — every known var of `resolve`'s output context was
  already a known var of the input context, so any "every known var satisfies
  `P`" invariant transports across successive `resolve` calls.  (`resolve` also
  preserves `TEnvWF`, needed to chain such calls, via the existing
  `resolve_TEnvWF`.)
* `typeBoundVar_knownVars_reverse` — a var known after `typeBoundVar` is either
  the generated binder or was already known.
* `inferFVar_mem_knownVars` — `inferFVar` succeeds only for known vars.

The scoping results are consumed externally — e.g. to prove that no
`old`-prefixed free variable can appear in a resolved precondition (see
`Strata.Languages.Core.WFProps`).
-/

namespace Lambda

open Std (ToFormat Format format)
open Strata.Util (HMap HMaps)
open LTy

public section

namespace LExpr

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata]

attribute [local simp] Pure.pure Except.pure

namespace Proofs

omit [ToString T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Closing the binder `xv` in `et` removes `xv` from the free variables and
    introduces no new ones: every free variable of `varCloseT k xv et` is a free
    variable of `et` distinct from `xv`. -/
theorem getVars_varCloseT_subset (k : Nat) (xv : T.Identifier) (et : LExprT T.mono)
    (id : Identifier T.IDMeta)
    (h : id ∈ LExpr.getVars (LExpr.varCloseT k xv et)) :
    id ∈ LExpr.getVars et ∧ id ≠ xv := by
  induction et generalizing k with
  | const | op | bvar => simp [LExpr.varCloseT, LExpr.getVars] at h
  | fvar m y yty =>
    simp only [LExpr.varCloseT] at h
    split at h
    · rename_i heq; simp [LExpr.getVars] at h
    · rename_i hne; simp only [LExpr.getVars, List.mem_singleton] at h ⊢
      subst h
      refine ⟨rfl, fun hc => hne ?_⟩
      subst hc; exact beq_self_eq_true _
  | abs m name ty e ih =>
    simp only [LExpr.varCloseT, LExpr.getVars] at h ⊢; exact ih (k+1) h
  | quant m qk name ty tr e ih_tr ih_e =>
    simp only [LExpr.varCloseT, LExpr.getVars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact ⟨Or.inl (ih_tr (k+1) h).1, (ih_tr (k+1) h).2⟩
    · exact ⟨Or.inr (ih_e (k+1) h).1, (ih_e (k+1) h).2⟩
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.varCloseT, LExpr.getVars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact ⟨Or.inl (ih1 k h).1, (ih1 k h).2⟩
    · exact ⟨Or.inr (ih2 k h).1, (ih2 k h).2⟩
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.varCloseT, LExpr.getVars, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact ⟨Or.inl (Or.inl (ihc k h).1), (ihc k h).2⟩
    · exact ⟨Or.inl (Or.inr (iht k h).1), (iht k h).2⟩
    · exact ⟨Or.inr (ihf k h).1, (ihf k h).2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.varCloseT, LExpr.getVars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact ⟨Or.inl (ih1 k h).1, (ih1 k h).2⟩
    · exact ⟨Or.inr (ih2 k h).1, (ih2 k h).2⟩

/-- `getVars` is invariant under `unresolved`: dropping the resolved type
    annotations does not change which free variables occur. -/
theorem getVars_unresolved {Tt : LExprParamsT} (et : LExprT Tt) :
    LExpr.getVars (LExpr.unresolved et) = LExpr.getVars et := by
  induction et with
  | const | op | bvar | fvar => rfl
  | abs m name ty e ih =>
    simp only [LExpr.unresolved]
    split <;> simp [LExpr.getVars, ih]
  | quant m qk name ty tr e ih_tr ih_e =>
    simp only [LExpr.unresolved, LExpr.getVars, ih_tr, ih_e]
  | app m e1 e2 ih1 ih2 => simp only [LExpr.unresolved, LExpr.getVars, ih1, ih2]
  | ite m c t f ihc iht ihf => simp only [LExpr.unresolved, LExpr.getVars, ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 => simp only [LExpr.unresolved, LExpr.getVars, ih1, ih2]

/-!
### Output-side scoping for `resolve`

The goal is: every free variable name of a resolved expression is a known
variable of the input context.  This is the freshness-free counterpart of a
`WellScoped`-from-`resolve` result: an `input`-side statement ("all input free
vars are known") would require the generated binder `xv` to be fresh in the
body, which does NOT follow from `typeBoundVar`'s specification (`genExprVar`
checks `xv` only against `knownVars`, never the expression).  Routing through
the OUTPUT side avoids the gap: in the abs/quant cases the output body is
`varCloseT 0 xv et_body`, and `getVars_varCloseT_subset` supplies `id ≠ xv` for
free, so the reverse-monotonicity disjunction collapses to the "already known"
branch with no freshness hypothesis.
-/
/-- Every free variable found in the type stack is among the known variables. -/
private theorem find?_some_mem_knownVars {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    (ctx : TContext IDMeta) (x : Identifier IDMeta)
    (ty : LTy) (h : ctx.types.find? x = some ty) :
    x ∈ TContext.knownVars ctx :=
  HMaps.find?_mem_keys ctx.types h

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `knownVars` membership transports across context equivalence (it reads the
    context only through `knownVars = types.keys`, which `Equiv` preserves). -/
private theorem mem_knownVars_of_Equiv {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    {id : T.Identifier} (hid : id ∈ TContext.knownVars Γ) :
    id ∈ TContext.knownVars Γ' := by
  simp only [TContext.knownVars] at hid ⊢
  obtain ⟨v, hv⟩ := (HMaps.mem_keys_iff_find? Γ.types id).mp hid
  exact HMaps.find?_mem_keys Γ'.types (by rw [← h.find? id]; exact hv)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `inferFVar` succeeds only when `x` is in the context, hence in `knownVars`. -/
theorem inferFVar_mem_knownVars
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty, Env')) :
    x ∈ TContext.knownVars Env.context := by
  unfold inferFVar at h
  cases h_find : Env.context.types.find? x with
  | none => rw [h_find] at h; simp at h
  | some tsch => exact find?_some_mem_knownVars Env.context x tsch h_find

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Reverse of adding a single fresh binding to the newest scope: every var whose
    key survives in `types.addInNewest (single xv ty)` is either `xv` itself or was
    already a key of `types`. -/
private theorem mem_keys_addInNewest_single_reverse
    (types : HMaps T.Identifier LTy) (xv : T.Identifier) (ty : LTy)
    (v : T.Identifier)
    (hv : v ∈ (types.addInNewest (HMap.single xv ty)).keys) :
    v = xv ∨ v ∈ types.keys := by
  obtain ⟨vty, h_find⟩ := (HMaps.mem_keys_iff_find? _ v).mp hv
  rcases HMaps.find?_addInNewest_single types xv ty v with ⟨_, h_eq⟩ | h
  · exact Or.inl h_eq
  · exact Or.inr (HMaps.find?_mem_keys types (h ▸ h_find))

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Reverse of `typeBoundVar_knownVars_mono`: any var known in the context
    produced by `typeBoundVar` is either the freshly-bound `xv` or was already
    known in the input context. -/
theorem typeBoundVar_knownVars_reverse
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (v : T.Identifier) (hv : v ∈ TContext.knownVars Env1.context) :
    v = xv ∨ v ∈ TContext.knownVars Env.context := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_gen h_gen; obtain ⟨_, Env_g⟩ := v_gen
  have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_gen
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h
    generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
    match res_ic with
    | .error _ => simp at h
    | .ok (_, Env_mid) =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_xv, _, h_env'⟩ := h; subst h_xv; subst h_env'
    have h_mid_ctx := (LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_mid h_ic).trans h_g_ctx
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownVars] at hv ⊢
    rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from congrArg TContext.types h_mid_ctx] at hv
    exact mem_keys_addInNewest_single_reverse _ _ _ v hv
  | none =>
    simp; intro h; elim_err h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_mid⟩ := v_tg
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_xv, _, h_env'⟩ := h; subst h_xv; subst h_env'
    have h_mid_ctx := (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownVars] at hv ⊢
    rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from congrArg TContext.types h_mid_ctx] at hv
    exact mem_keys_addInNewest_single_reverse _ _ _ v hv

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Every output free variable of `resolveAux` is a known variable of the input
    context.  Freshness-free (see the section note). -/
private theorem resolveAux_getVars_mem_knownVars (e) (et) (C) (Env Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactoryWF C.functions) :
    ∀ id ∈ LExpr.getVars et, id ∈ TContext.knownVars Env.context := by
  apply resolveAux_ind
    (P := fun _e et _C Env _Env' => ∀ id ∈ LExpr.getVars et, id ∈ TContext.knownVars Env.context)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res _ _ _ id hid
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    split at h_res
    · simp at h_res
    · rename_i r _; obtain ⟨ty, Env_r⟩ := r
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      exact absurd hid (by simp [LExpr.getVars])
  case h_op =>
    intro m o oty et C Env Env' h_res _ _ _ id
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    revert h_res; repeat' split
    all_goals (
      intro h_res
      simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h_res
      try (obtain ⟨h_et, _⟩ := h_res; subst h_et; intro hid;
           simp only [LExpr.getVars, List.not_mem_nil] at hid))
  case h_fvar =>
    intro m x fty et C Env Env' h_res _ _ _ id hid
    simp only [resolveAux, Bind.bind, Except.bind] at h_res
    split at h_res
    · simp at h_res
    · rename_i r _; obtain ⟨ty, Env_r⟩ := r
      rename_i h_infer
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, _⟩ := h_res; subst h_et
      simp only [LExpr.getVars, List.mem_singleton] at hid
      rw [hid]
      exact inferFVar_mem_knownVars C Env x fty ty Env_r h_infer
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      _ _ _ _ _ h_et _ _ _ _ _ _ _ _ _ _ h_ctx1 _ _ h_ih1 h_ih2
    subst h_et
    intro id hid
    simp only [LExpr.getVars, List.mem_append] at hid
    rcases hid with h1 | h2
    · exact h_ih1 id h1
    · exact mem_knownVars_of_Equiv h_ctx1 (h_ih2 id h2)
  case h_abs =>
    intro m name bty body et C Env Env' xv xty Env1 et_body Env2
      _ h_tbv _ h_et _ _ _ _ _ _ _ h_ih
    subst h_et
    intro id hid
    simp only [LExpr.getVars] at hid
    obtain ⟨hid_body, hid_ne⟩ := getVars_varCloseT_subset 0 xv et_body id hid
    have hid_known := h_ih id hid_body
    rcases typeBoundVar_knownVars_reverse C Env bty xv xty Env1 h_tbv id hid_known with h_eq | h_ok
    · exact absurd h_eq hid_ne
    · exact h_ok
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3 substInfo
      _ h_tbv _ _ _ h_et _ _ _ _ _ _ _ _ _ h_ctx2 h_ih_body h_ih_tr
    subst h_et
    intro id hid
    simp only [LExpr.getVars, List.mem_append] at hid
    rcases hid with h_tr | h_body
    · obtain ⟨hid_tr, hid_ne⟩ := getVars_varCloseT_subset 0 xv et_tr id h_tr
      have hid_known := mem_knownVars_of_Equiv h_ctx2 (h_ih_tr id hid_tr)
      rcases typeBoundVar_knownVars_reverse C Env bty xv xty Env1 h_tbv id hid_known with h_eq | h_ok
      · exact absurd h_eq hid_ne
      · exact h_ok
    · obtain ⟨hid_body, hid_ne⟩ := getVars_varCloseT_subset 0 xv et_body id h_body
      have hid_known := h_ih_body id hid_body
      rcases typeBoundVar_knownVars_reverse C Env bty xv xty Env1 h_tbv id hid_known with h_eq | h_ok
      · exact absurd h_eq hid_ne
      · exact h_ok
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      _ _ _ _ h_et _ _ _ _ _ _ _ h_ctx1 _ _ h_ih1 h_ih2
    subst h_et
    intro id hid
    simp only [LExpr.getVars, List.mem_append] at hid
    rcases hid with h1 | h2
    · exact h_ih1 id h1
    · exact mem_knownVars_of_Equiv h_ctx1 (h_ih2 id h2)
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      _ _ _ _ _ h_et _ _ _ _ _ _ _ h_ctx1 _ h_ctx2 _ _ h_ihc h_iht h_ihe
    subst h_et
    intro id hid
    simp only [LExpr.getVars, List.mem_append] at hid
    rcases hid with (hc | ht) | he
    · exact h_ihc id hc
    · exact mem_knownVars_of_Equiv h_ctx1 (h_iht id ht)
    · exact mem_knownVars_of_Equiv h_ctx2 (h_ihe id he)

/-- `getVars` is invariant under `replaceMetadata` (only metadata changes). -/
private theorem getVars_replaceMetadata {Tt : LExprParamsT} {NewMeta : Type} (e : LExpr Tt)
    (f : Tt.base.Metadata → NewMeta) :
    LExpr.getVars (LExpr.replaceMetadata e f) = LExpr.getVars e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs m name ty e ih => simp only [LExpr.replaceMetadata, LExpr.getVars, ih]
  | quant m qk name ty tr e ih_tr ih_e => simp only [LExpr.replaceMetadata, LExpr.getVars, ih_tr, ih_e]
  | app m e1 e2 ih1 ih2 => simp only [LExpr.replaceMetadata, LExpr.getVars, ih1, ih2]
  | ite m c t f ihc iht ihf => simp only [LExpr.replaceMetadata, LExpr.getVars, ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 => simp only [LExpr.replaceMetadata, LExpr.getVars, ih1, ih2]

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `getVars` is invariant under `applySubstT` (only type annotations change). -/
private theorem getVars_applySubstT (et : LExprT T.mono) (S : Subst) :
    LExpr.getVars (LExpr.applySubstT et S) = LExpr.getVars et := by
  unfold LExpr.applySubstT
  exact getVars_replaceMetadata et _

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `resolve`-wrapper version of `resolveAux_getVars_mem_knownVars`: whenever the
    input env already has a non-empty scope, every output fvar is a known var of
    the input context. -/
theorem resolve_getVars_mem_knownVars (C) (Env Env' : TEnv T.IDMeta) (e) (et)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactoryWF C.functions) :
    ∀ id ∈ LExpr.getVars et, id ∈ TContext.knownVars Env.context := by
  intro id hid
  have h_isEmpty : Env.context.types.isEmpty = false := by
    cases hEq : Env.context.types with
    | nil => exact absurd hEq h_ne
    | cons _ _ => rfl
  unfold LExpr.resolve at h
  simp only [h_isEmpty, if_false, Bool.false_eq_true, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i r h_aux; obtain ⟨et_aux, Env_aux⟩ := r
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, _⟩ := h
    subst h_et
    rw [getVars_applySubstT] at hid
    exact resolveAux_getVars_mem_knownVars e et_aux C Env Env_aux h_aux h_envwf h_ne h_fwf id hid

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Every known variable of `resolve`'s output context was already a known
    variable of the input context.  Direct consequence of
    `resolve_preserves_context` (`Env'.context.Equiv Env.context`, which is
    symmetric in `knownVars`): stated as a subset for the common use-case of
    transporting an "every known var satisfies `P`"-style invariant across a
    successful `resolve` call — e.g. when repeatedly resolving expressions
    against the previous call's output env, as `typeCheckConditions` does for
    successive procedure pre/postconditions. -/
theorem resolve_knownVars_subset (C) (Env Env' : TEnv T.IDMeta) (e) (et)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactoryWF C.functions) :
    ∀ v ∈ TContext.knownVars Env'.context, v ∈ TContext.knownVars Env.context := by
  intro v hv
  have h_eq : Env'.context.Equiv Env.context :=
    resolve_preserves_context e et C Env Env' h h_envwf h_ne h_fwf
  exact mem_knownVars_of_Equiv h_eq hv

end Proofs

end LExpr
end -- public section
end Lambda

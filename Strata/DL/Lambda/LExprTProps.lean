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
import all Strata.DL.Lambda.LExprTypeSpec
public meta import Init.Grind.Cases

/-! ## Properties of `LExprT` operators and of `resolve`

Properties of the `LExprT` operators defined in `Strata.DL.Lambda.LExprT`
concerning the free variables (`LExpr.getVars`) and operators of their output,
plus facts about `checkContextTypesClosed`, the type-variable generator, and
type annotations.

Two free-variable families live here:

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
  known var of the input context.
* `resolve_knownVars_subset` — every known var of `resolve`'s output context was
  already a known var of the input context, so any "every known var satisfies
  `P`" invariant transports across successive `resolve` calls.  (`resolve` also
  preserves `TEnvWF`, needed to chain such calls, via the existing
  `resolve_TEnvWF`.)
* `typeBoundVar_knownVars_reverse` — a var known after `typeBoundVar` is either
  the generated binder or was already known.
* `inferFVar_mem_knownVars` — `inferFVar` succeeds only for known vars.
* `getVars_replaceMetadata`, `getOps_replaceMetadata` — rewriting metadata
  keeps the free variables and the operators.
* The annotation lemmas — how the operators and the free-variable and binder
  annotations of the `unresolved` form change under type substitution and
  under closing a variable.
* `resolve_genState_tyGen_mono` — `resolve` never decreases the type-variable
  generator.
* `applySubstT_absorbs`, `applySubstT_varCloseT_comm` — applying a substitution
  to annotations makes an earlier substitution it absorbs redundant, and
  commutes with closing a variable.

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

/-- `LExpr.unresolved` never yields an unannotated free variable. -/
theorem unresolved_ne_fvar_none {Tt : LExprParamsT} (et : LExprT Tt) :
    ∀ m x, LExpr.unresolved et ≠ .fvar m x none := by
  intro m x
  cases et <;>
    simp only [LExpr.unresolved, ne_eq, reduceCtorEq, not_false_eq_true,
      LExpr.fvar.injEq, and_false]
  · split <;> simp

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
    simp only [pure, Except.pure]; intro h; elim_err h
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
theorem resolveAux_getVars_mem_knownVars (e) (et) (C) (Env Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions) :
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
theorem getVars_replaceMetadata {Tt : LExprParamsT} {NewMeta : Type}
    (e : LExpr Tt) (f : Tt.base.Metadata → NewMeta) :
    LExpr.getVars (LExpr.replaceMetadata e f) = LExpr.getVars e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs m name ty e ih => simp only [LExpr.replaceMetadata, LExpr.getVars, ih]
  | quant m qk name ty tr e ih_tr ih_e => simp only [LExpr.replaceMetadata, LExpr.getVars, ih_tr, ih_e]
  | app m e1 e2 ih1 ih2 => simp only [LExpr.replaceMetadata, LExpr.getVars, ih1, ih2]
  | ite m c t f ihc iht ihf => simp only [LExpr.replaceMetadata, LExpr.getVars, ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 => simp only [LExpr.replaceMetadata, LExpr.getVars, ih1, ih2]

/-- `getOps` is invariant under `replaceMetadata` (only metadata changes). -/
theorem getOps_replaceMetadata {Tt : LExprParamsT} {NewMeta : Type}
    (e : LExpr Tt) (f : Tt.base.Metadata → NewMeta) :
    LExpr.getOps (LExpr.replaceMetadata e f) = LExpr.getOps e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs m name ty e ih => simp only [LExpr.replaceMetadata, LExpr.getOps, ih]
  | quant m qk name ty tr e ih_tr ih_e =>
    simp only [LExpr.replaceMetadata, LExpr.getOps, ih_tr, ih_e]
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.replaceMetadata, LExpr.getOps, ih1, ih2]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.replaceMetadata, LExpr.getOps, ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.replaceMetadata, LExpr.getOps, ih1, ih2]

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `getVars` is invariant under `applySubstT` (only type annotations change). -/
theorem getVars_applySubstT (et : LExprT T.mono) (S : Subst) :
    LExpr.getVars (LExpr.applySubstT et S) = LExpr.getVars et := by
  unfold LExpr.applySubstT
  exact getVars_replaceMetadata et _

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata] in
/-- `getOps` is invariant under `applySubstT` (only type annotations change). -/
theorem getOps_applySubstT (et : LExprT T.mono) (S : Subst) :
    LExpr.getOps (LExpr.applySubstT et S) = LExpr.getOps et := by
  unfold LExpr.applySubstT
  exact getOps_replaceMetadata et _

omit [ToString T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta]
  [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Closing a variable into a bound variable does not change the operators. -/
theorem getOps_varCloseT (k : Nat) (xv : T.Identifier) (et : LExprT T.mono) :
    LExpr.getOps (LExpr.varCloseT k xv et) = LExpr.getOps et := by
  induction et generalizing k with
  | fvar m y yty =>
    simp only [LExpr.varCloseT]
    split <;> rfl
  | _ => simp_all [LExpr.varCloseT, LExpr.getOps]

/-- `LExpr.unresolved` does not change the operators. -/
theorem getOps_unresolved {Tt : LExprParamsT} (et : LExprT Tt) :
    LExpr.getOps (LExpr.unresolved et) = LExpr.getOps et := by
  induction et with
  | abs m name ty e ih =>
    simp only [LExpr.unresolved]
    split <;> simp [LExpr.getOps, ih]
  | _ => simp_all [LExpr.unresolved, LExpr.getOps]

/-- The `LExpr` form of a typed expression annotates every operator, free
    variable and quantifier. -/
theorem fullyAnnotated_unresolved {Tt : LExprParamsT} (et : LExprT Tt) :
    LExpr.fullyAnnotated (LExpr.unresolved et) = true := by
  induction et with
  | abs m name ty e ih =>
    simp only [LExpr.unresolved]
    split <;> simp [LExpr.fullyAnnotated, ih]
  | _ => simp_all [LExpr.unresolved, LExpr.fullyAnnotated]

omit [ToString T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta]
  [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Closing a variable into a bound variable keeps the annotated operators of
    the `LExpr` form. -/
theorem opAnnots_unresolved_varCloseT
    (k : Nat) (xv : T.Identifier) (et : LExprT T.mono) :
    LExpr.opAnnots (LExpr.unresolved (LExpr.varCloseT k xv et)) =
      LExpr.opAnnots (LExpr.unresolved et) := by
  induction et generalizing k with
  | fvar m y yty =>
    simp only [LExpr.varCloseT]
    split <;> rfl
  | abs m name ty e ih =>
    simp only [LExpr.varCloseT, LExpr.unresolved]
    split <;> simp [LExpr.opAnnots, ih]
  | _ => simp_all [LExpr.varCloseT, LExpr.unresolved, LExpr.opAnnots]

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata] in
/-- Substituting into the type annotations substitutes into the annotation of
    each annotated operator of the `LExpr` form. -/
theorem opAnnots_unresolved_applySubstT (et : LExprT T.mono) (S : Subst) :
    LExpr.opAnnots (LExpr.unresolved (LExpr.applySubstT et S)) =
      (LExpr.opAnnots (LExpr.unresolved et)).map
        (fun p => (p.1, LMonoTy.subst S p.2)) := by
  unfold LExpr.applySubstT
  induction et with
  | abs m name ty e ih =>
    simp only [LExpr.replaceMetadata, LExpr.unresolved]
    split <;> split <;> simp_all [LExpr.opAnnots]
  | _ => simp_all [LExpr.replaceMetadata, LExpr.unresolved, LExpr.opAnnots]

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata] in
/-- Substituting into the type annotations substitutes into the annotation of
    each free variable of the `LExpr` form. -/
theorem freeVars_unresolved_applySubstT (et : LExprT T.mono) (S : Subst) :
    LExpr.freeVars (LExpr.unresolved (LExpr.applySubstT et S)) =
      (LExpr.freeVars (LExpr.unresolved et)).map
        (fun p => (p.1, p.2.map (LMonoTy.subst S))) := by
  unfold LExpr.applySubstT
  induction et with
  | abs m name ty e ih =>
    simp only [LExpr.replaceMetadata, LExpr.unresolved]
    split <;> split <;> simp_all [LExpr.freeVars]
  | _ => simp_all [LExpr.replaceMetadata, LExpr.unresolved, LExpr.freeVars]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `resolve`-wrapper version of `resolveAux_getVars_mem_knownVars`: whenever the
    input env already has a non-empty scope, every output fvar is a known var of
    the input context. -/
theorem resolve_getVars_mem_knownVars (C) (Env Env' : TEnv T.IDMeta) (e) (et)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions) :
    ∀ id ∈ LExpr.getVars et, id ∈ TContext.knownVars Env.context := by
  intro id hid
  have h_isEmpty : Env.context.types.isEmpty = false := by
    cases hEq : Env.context.types with
    | nil => exact absurd hEq h_ne
    | cons _ _ => rfl
  unfold LExpr.resolve at h
  simp only [h_isEmpty, ite_false, Bool.false_eq_true, Bind.bind, Except.bind] at h
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
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactorySigWF C.functions) :
    ∀ v ∈ TContext.knownVars Env'.context, v ∈ TContext.knownVars Env.context := by
  intro v hv
  have h_eq : Env'.context.Equiv Env.context :=
    resolve_preserves_context e et C Env Env' h h_envwf h_ne h_fwf
  exact mem_knownVars_of_Equiv h_eq hv

end Proofs

end LExpr

/-! ### Closed context types, the type-variable generator, annotations -/

namespace LExpr

/-- The default environment's context is closed. -/
theorem checkContextTypesClosed_default {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] :
    checkContextTypesClosed (T := T) (TEnv.default (IDMeta := T.IDMeta)) := by
  simp [checkContextTypesClosed, TEnv.default, TEnv.context]

/-- `checkContextTypesClosed` depends on `Env` only through its context. -/
theorem checkContextTypesClosed_of_context_eq {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (E1 E2 : TEnv T.IDMeta)
    (h : E1.context = E2.context) :
    LExpr.checkContextTypesClosed (T := T) E1
      = LExpr.checkContextTypesClosed (T := T) E2 := by
  simp only [LExpr.checkContextTypesClosed, h]

end LExpr

section
open LExpr

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]

/-- Replacing the substitution preserves closedness of context types. -/
theorem TEnv.updateSubst_checkContextTypesClosed
    (Env : TEnv T.IDMeta) (S : SubstInfo) :
    checkContextTypesClosed (Env.updateSubst S) =
      checkContextTypesClosed Env := by
  rfl

end

/-- Adding an empty newest scope preserves closedness of all context types. -/
theorem pushEmptyContext_preserves_closed
    {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Env : TEnv T.IDMeta)
    (h_closed : LExpr.checkContextTypesClosed (T := T) Env) :
    LExpr.checkContextTypesClosed (T := T) (Env.pushEmptyContext) := by
  simp only [LExpr.checkContextTypesClosed, TEnv.context] at h_closed ⊢
  simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context,
    HMaps.push, List.all_cons, h_closed, Bool.and_true]
  simp only [HMap.all, HMap.empty, ← Std.HashMap.all_toList,
    Std.HashMap.toList_emptyWithCapacity, List.all_nil]

section
open LExpr

variable {T : LExprParams} [Std.ToFormat T.IDMeta]

section ResolveTyGenMono

variable [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
  [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- The recursive resolver never decreases the type-variable generator. -/
private theorem resolveAux_tyGen_mono (C : LContext T) :
    ∀ (e : LExpr T.mono) (Env Env' : TEnv T.IDMeta) (et : LExprT T.mono),
      resolveAux C Env e = .ok (et, Env') →
      Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen :=
  resolveAux_preserves C
    (fun E E' => E.genEnv.genState.tyGen ≤ E'.genEnv.genState.tyGen)
    (fun _ => Nat.le_refl _)
    (fun _ _ _ h12 h23 => Nat.le_trans h12 h23)
    (fun scheme E mty E' hinst =>
      LTy_instantiateWithCheck_tyGen_mono scheme C E mty E' hinst)
    (fun ann E mty E' hinst =>
      LMonoTy_instantiateWithCheck_tyGen_mono ann C E mty E' hinst)
    (fun E x fty mty E' hinfer => inferFVar_tyGen_mono C E x fty mty E' hinfer)
    (fun E n E' hgen => by rw [genTyVar_tyGen E n E' hgen]; omega)
    (fun _ _ _ _ => Nat.le_refl _)
    (fun _ _ _ _ _ _ => Nat.le_refl _)
    (fun E bty xv xty E1 _ hboundOk h12 =>
      Nat.le_trans (typeBoundVar_tyGen_mono C E bty xv xty E1 hboundOk) h12)

end ResolveTyGenMono

/-- `resolve` never decreases the type-variable generator counter. -/
theorem resolve_genState_tyGen_mono
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (e_typed, Env')) :
    Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen := by
  unfold LExpr.resolve at h
  simp only [bind, Except.bind] at h
  elim_err h with r haux
  obtain ⟨et, EnvR⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  split at haux
  · exact resolveAux_tyGen_mono C e
      (Env.updateContext { Env.context with types := [.empty] }) EnvR et haux
  · exact resolveAux_tyGen_mono C e Env EnvR et haux

end

namespace LExpr

/-- Applying `S` after `Sin` to the annotations of `et` is the same as applying
    `S` alone, provided `S` absorbs `Sin`. -/
theorem applySubstT_absorbs {T : LExprParamsT}
    (S Sin : Subst) (h : Subst.absorbs S Sin) (et : LExprT T) :
    LExpr.applySubstT (LExpr.applySubstT et Sin) S =
      LExpr.applySubstT et S := by
  induction et <;>
    simp_all [LExpr.applySubstT, LExpr.replaceMetadata,
      LMonoTy.subst_absorbs S Sin _ h]

/-- Applying a type substitution to the annotations of an expression commutes
    with closing a free variable into a bound variable. -/
theorem applySubstT_varCloseT_comm {T : LExprParams}
    [DecidableEq T.IDMeta] (k : Nat) (xv : T.Identifier)
    (et : LExprT T.mono) (S : Subst) :
    applySubstT (LExpr.varCloseT k xv et) S =
      LExpr.varCloseT k xv (applySubstT et S) := by
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

namespace Proofs

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]

omit [ToString T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta]
  [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Closing a binder of a resolved expression keeps the binder annotations of
    its `LExpr` form. -/
theorem binderAnnotations_unresolved_varCloseT (x : T.Identifier) :
    ∀ (k : Nat) (et : LExprT T.mono),
      binderAnnotations (LExpr.unresolved (LExpr.varCloseT k x et)) =
        binderAnnotations (LExpr.unresolved et) := by
  intro k et
  induction et generalizing k <;>
    simp only [LExpr.varCloseT, LExpr.unresolved, binderAnnotations, *] <;>
    split <;> simp only [LExpr.unresolved, binderAnnotations, *]

omit [ToString T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta]
  [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Closing a binder of a resolved expression adds no free-variable annotation
    to its `LExpr` form. -/
theorem fvarAnnotations_unresolved_varCloseT_subset (x : T.Identifier) :
    ∀ (k : Nat) (et : LExprT T.mono) (t : LMonoTy),
      t ∈ fvarAnnotations (LExpr.unresolved (LExpr.varCloseT k x et)) →
        t ∈ fvarAnnotations (LExpr.unresolved et) := by
  intro k et
  induction et generalizing k with
  | const _ _ | op _ _ _ | bvar _ _ => exact fun _ ht => ht
  | fvar _ y _ =>
    intro t ht
    simp only [LExpr.varCloseT] at ht
    split at ht
    · simp only [LExpr.unresolved, fvarAnnotations, List.not_mem_nil] at ht
    · exact ht
  | abs m name ty e ih =>
    have hfa : ∀ e' : LExprT T.mono,
        fvarAnnotations (LExpr.unresolved (.abs m name ty e')) =
          fvarAnnotations (LExpr.unresolved e') := by
      intro e'
      simp only [LExpr.unresolved]
      split <;> rfl
    intro t ht
    simp only [LExpr.varCloseT] at ht
    rw [hfa] at ht
    rw [hfa]
    exact ih _ t ht
  | quant m qk name ty tr e ihtr ih =>
    intro t ht
    simp only [LExpr.varCloseT, LExpr.unresolved, fvarAnnotations,
      List.mem_append] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl (ihtr _ t ht)
    · exact Or.inr (ih _ t ht)
  | app m e1 e2 ih1 ih2 =>
    intro t ht
    simp only [LExpr.varCloseT, LExpr.unresolved, fvarAnnotations,
      List.mem_append] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl (ih1 _ t ht)
    · exact Or.inr (ih2 _ t ht)
  | ite m c t f ihc iht ihf =>
    intro u hu
    simp only [LExpr.varCloseT, LExpr.unresolved, fvarAnnotations,
      List.mem_append] at hu ⊢
    rcases hu with (hu | hu) | hu
    · exact Or.inl (Or.inl (ihc _ u hu))
    · exact Or.inl (Or.inr (iht _ u hu))
    · exact Or.inr (ihf _ u hu)
  | eq m e1 e2 ih1 ih2 =>
    intro t ht
    simp only [LExpr.varCloseT, LExpr.unresolved, fvarAnnotations,
      List.mem_append] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl (ih1 _ t ht)
    · exact Or.inr (ih2 _ t ht)

end Proofs
end LExpr

end -- public section
end Lambda

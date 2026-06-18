/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.CommandTypeSpec
import all Strata.Languages.Core.CmdTypeSpecProps
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.StatementType
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Lambda.LExprTypeSpec

/-! ## Soundness of Command (CmdExt) Typechecker

This file relates the executable command typechecker `Statement.typeCheckCmd`
to the declarative typing relations `CmdExtHasType` and `CmdExtHasTypeA`.

* **`Command.typeCheckCmd_sound`** — if `typeCheckCmd` succeeds, then
  `CmdExtHasType` holds between the substituted input and output contexts.

* **`Command.typeCheckCmd_annotated_sound`** — if `typeCheckCmd` succeeds,
  the output command satisfies `CmdExtHasTypeA`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-! ### Well-formedness conditions on procedures -/

/-- A procedure's formal types only mention declared type parameters. -/
def ProcHeaderClosed (proc : Procedure) : Prop :=
  (∀ mty, mty ∈ proc.header.inputs.values →
    ∀ a, a ∈ LMonoTy.freeVars mty → a ∈ proc.header.typeArgs) ∧
  (∀ mty, mty ∈ proc.header.outputs.values →
    ∀ a, a ∈ LMonoTy.freeVars mty → a ∈ proc.header.typeArgs)

/-! ### Auxiliary lemmas for bridge -/

/-- The `i`-th pair of `as.zip bs` is `(as[i], bs[i])` and is a member of the zip. -/
theorem zip_getElem_mem {α β : Type} (as : List α) (bs : List β) (i : Nat)
    (ha : i < as.length) (hb : i < bs.length) :
    (as[i], bs[i]) ∈ as.zip bs := by
  have hlt : i < (as.zip bs).length := by simp [List.length_zip]; omega
  have h : (as.zip bs)[i]'hlt = (as[i], bs[i]) := List.getElem_zip
  exact h ▸ List.getElem_mem hlt

private theorem map_find?_zip_map_of_find [DecidableEq α]
    (keys : List α) (vals : List β) (f : β → γ) (x : α) (v : β)
    (h_find : Map.find? (keys.zip vals) x = some v) :
    Map.find? (keys.zip (vals.map f)) x = some (f v) := by
  induction keys generalizing vals with
  | nil => simp [List.zip, Map.find?] at h_find
  | cons k ks ih =>
    cases vals with
    | nil => simp [List.zip, Map.find?] at h_find
    | cons vl vls =>
      simp only [List.zip, List.zipWith, List.map, Map.find?] at h_find ⊢
      split at h_find <;> split <;> try grind
      · exact ih vls h_find

private theorem maps_find?_singleton [DecidableEq α] (m : Map α β) (x : α) :
    Maps.find? [m] x = Map.find? m x := by
  unfold Maps.find?
  cases Map.find? m x with
  | none => simp [Maps.find?]
  | some v => rfl

/-- The diagonal zip `ids.zip ids` maps each `x ∈ ids` to itself. -/
private theorem find_zip_diag {α : Type} [DecidableEq α] (ids : List α) (x : α)
    (h : x ∈ ids) : Map.find? (ids.zip ids) x = some x := by
  induction ids with
  | nil => simp at h
  | cons k ks ih =>
    simp only [List.zip, List.zipWith, Map.find?]
    split
    · rename_i h_eq; rw [h_eq]
    · rename_i h_ne
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm h_ne
      · exact ih h

/-! ### Diagonal substitution bridge -/

/-- The σ used in the `.call` obligations, written in `typeArgs`-form
    `zip typeArgs (typeArgs.map (fun a => subst S (subst tyArgSubst (ftvar a))))`,
    applied to a type whose free variables are all in `typeArgs`, equals the
    two-step substitution `subst S (subst tyArgSubst t)`. -/
theorem subst_diag_eq (typeArgs : List TyIdentifier) (S_final tyArgSubst : Subst)
    (t : LMonoTy) (h_closed : ∀ a, a ∈ LMonoTy.freeVars t → a ∈ typeArgs) :
    LMonoTy.subst
      [typeArgs.zip (typeArgs.map (fun a =>
        LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))))] t =
      LMonoTy.subst S_final (LMonoTy.subst tyArgSubst t) := by
  induction t with
  | ftvar x =>
    have hx : x ∈ typeArgs := h_closed x (by simp [LMonoTy.freeVars])
    have h_find := map_find?_zip_map_of_find typeArgs typeArgs
      (fun a => LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))) x x
      (find_zip_diag typeArgs x hx)
    have h_maps : Maps.find?
        [typeArgs.zip (typeArgs.map (fun a =>
          LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))))] x =
        some (LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar x))) := by
      rw [maps_find?_singleton]; exact h_find
    have h_ne : Subst.hasEmptyScopes
        [typeArgs.zip (typeArgs.map (fun a =>
          LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))))] = false := by
      cases typeArgs with
      | nil => simp at hx
      | cons k ks => simp [Subst.hasEmptyScopes, List.zip, Map.isEmpty]
    exact LMonoTy.subst_ftvar_eq _ x _ h_ne h_maps
  | bitvec n => simp [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    induction args with
    | nil => rw [LMonoTys.subst_nil, LMonoTys.subst_nil, LMonoTys.subst_nil]
    | cons a as ih_list =>
      have h_a_closed : ∀ x, x ∈ a.freeVars → x ∈ typeArgs :=
        fun x hx => h_closed x (by
          simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append]; left; exact hx)
      have h_as_closed : ∀ x, x ∈ (LMonoTy.tcons name as).freeVars → x ∈ typeArgs :=
        fun x hx => h_closed x (by
          simp only [LMonoTy.freeVars] at hx ⊢
          simp only [LMonoTys.freeVars, List.mem_append]
          right; exact hx)
      rw [LMonoTys.subst_cons_eq, LMonoTys.subst_cons_eq, LMonoTys.subst_cons_eq]
      congr 1
      · exact ih a (List.Mem.head as) h_a_closed
      · exact ih_list (fun ty hty hcl => ih ty (List.Mem.tail a hty) hcl) h_as_closed

/-- `LMonoTys.subst` is pointwise `LMonoTy.subst`. -/
theorem LMonoTys_subst_eq_map (S : Subst) (xs : LMonoTys) :
    LMonoTys.subst S xs = xs.map (LMonoTy.subst S) := by
  induction xs with
  | nil => simp [LMonoTys.subst_nil]
  | cons h t ih => rw [LMonoTys.subst_cons_eq, ih, List.map_cons]

/-- Shared kernel for the call input/output type lemmas: from a unify-derived
    equality `subst S_final a = subst S_final b` and an `AliasEquiv` relating
    `subst S_final b` to the two-step `subst S_final (subst tyArgSubst formal)`,
    conclude the `AliasEquiv` against the one-step `σ` substitution (in the
    `typeArgs`-form used by the `.call` obligations). -/
theorem call_type_bridge (aliases : List TypeAlias)
    (typeArgs : List TyIdentifier) (S_final tyArgSubst : Subst) (a b formal : LMonoTy)
    (h_closed : ∀ x, x ∈ LMonoTy.freeVars formal → x ∈ typeArgs)
    (h_eq : LMonoTy.subst S_final a = LMonoTy.subst S_final b)
    (h_ae : AliasEquiv aliases (LMonoTy.subst S_final b)
              (LMonoTy.subst S_final (LMonoTy.subst tyArgSubst formal))) :
    AliasEquiv aliases (LMonoTy.subst S_final a)
      (LMonoTy.subst
        [typeArgs.zip (typeArgs.map (fun a =>
          LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))))]
        formal) := by
  rw [subst_diag_eq typeArgs S_final tyArgSubst formal h_closed]
  rw [h_eq]; exact h_ae

/-! ### Context and WF preservation through instantiation -/

/-- Context preservation for the `go` loop inside `instantiateWithSubst`. -/
private theorem instantiateWithSubst_go_context (C : LContext CoreLParams)
    (tys : LTys) :
    ∀ (Env : TEnv Unit) (result : LMonoTys × TEnv Unit),
      LMonoTySignature.instantiateWithSubst.go C Env tys = .ok result →
      result.2.context = Env.context := by
  induction tys with
  | nil =>
    intro Env result h
    simp only [LMonoTySignature.instantiateWithSubst.go] at h
    injection h with h'; rw [← h']
  | cons t tr ih =>
    intro Env result h
    simp only [LMonoTySignature.instantiateWithSubst.go, Bind.bind, Except.bind] at h
    elim_err h with v1 h_iwc; obtain ⟨mt, Env_mid⟩ := v1
    elim_err h with v2 h_rest; obtain ⟨mtrest, Env_end⟩ := v2
    injection h with h'; rw [← h']
    rw [ih Env_mid (mtrest, Env_end) h_rest]
    exact LTy_instantiateWithCheck_context' t C Env mt Env_mid h_iwc

/-- Context preservation for `instantiateEnvWithSubst` (only `genEnv` changes). -/
private theorem instantiateEnvWithSubst_context
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv Unit)
    (result : LMonoTys × TEnv Unit × Subst)
    (h : LMonoTys.instantiateEnvWithSubst ids mtys Env = .ok result) :
    result.2.fst.context = Env.context := by
  simp only [LMonoTys.instantiateEnvWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_gen; obtain ⟨freshtvs, genEnv'⟩ := v1
  simp only [Except.ok.injEq] at h
  rw [← h]
  show genEnv'.context = Env.genEnv.context
  exact TGenEnv.genTyVars_context ids.length Env.genEnv freshtvs genEnv' h_gen

theorem instantiateWithSubst_preserves_context (C : LContext CoreLParams)
    (Env : TEnv Unit) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature Unit)
    (result : LMonoTySignature × TEnv Unit × Subst)
    (h : LMonoTySignature.instantiateWithSubst C Env tyArgs sig = .ok result) :
    result.2.fst.context = Env.context := by
  simp only [LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_env; obtain ⟨mtys, Env₁, S⟩ := v1
  elim_err h with v2 h_go; obtain ⟨newtys, Env₂⟩ := v2
  simp only [Except.ok.injEq] at h
  rw [← h]
  rw [instantiateWithSubst_go_context C _ Env₁ (newtys, Env₂) h_go]
  exact instantiateEnvWithSubst_context tyArgs (ListMap.values sig) Env (mtys, Env₁, S) h_env

/-- `stateSubstInfo` preservation for the `go` loop inside `instantiateWithSubst`. -/
private theorem instantiateWithSubst_go_stateSubstInfo (C : LContext CoreLParams)
    (tys : LTys) :
    ∀ (Env : TEnv Unit) (result : LMonoTys × TEnv Unit),
      LMonoTySignature.instantiateWithSubst.go C Env tys = .ok result →
      result.2.stateSubstInfo = Env.stateSubstInfo := by
  induction tys with
  | nil =>
    intro Env result h
    simp only [LMonoTySignature.instantiateWithSubst.go] at h
    injection h with h'; rw [← h']
  | cons t tr ih =>
    intro Env result h
    simp only [LMonoTySignature.instantiateWithSubst.go, Bind.bind, Except.bind] at h
    elim_err h with v1 h_iwc; obtain ⟨mt, Env_mid⟩ := v1
    elim_err h with v2 h_rest; obtain ⟨mtrest, Env_end⟩ := v2
    injection h with h'; rw [← h']
    rw [ih Env_mid (mtrest, Env_end) h_rest]
    exact LTy_instantiateWithCheck_preserves_stateSubstInfo t C Env mt Env_mid h_iwc

/-- `stateSubstInfo` preservation for `instantiateWithSubst` (only `genEnv` changes). -/
theorem instantiateWithSubst_preserves_stateSubstInfo (C : LContext CoreLParams)
    (Env : TEnv Unit) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature Unit)
    (result : LMonoTySignature × TEnv Unit × Subst)
    (h : LMonoTySignature.instantiateWithSubst C Env tyArgs sig = .ok result) :
    result.2.fst.stateSubstInfo = Env.stateSubstInfo := by
  simp only [LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_env; obtain ⟨mtys, Env₁, S⟩ := v1
  elim_err h with v2 h_go; obtain ⟨newtys, Env₂⟩ := v2
  simp only [Except.ok.injEq] at h
  rw [← h]
  rw [instantiateWithSubst_go_stateSubstInfo C _ Env₁ (newtys, Env₂) h_go]
  -- `instantiateEnvWithSubst` only changes `genEnv`.
  simp only [LMonoTys.instantiateEnvWithSubst, Bind.bind, Except.bind] at h_env
  elim_err h_env with vg h_gen; obtain ⟨freshtvs, genEnv'⟩ := vg
  simp only [Except.ok.injEq, Prod.mk.injEq] at h_env
  obtain ⟨_, h_env1, _⟩ := h_env; rw [← h_env1]

/-- Context preservation for a single `LTy.instantiateAndSubst`. -/
private theorem LTy_instantiateAndSubst_context
    (ty : LTy) (C : LContext CoreLParams) (E E' : TEnv Unit) (m : LMonoTy)
    (h : LTy.instantiateAndSubst ty C E = .ok (m, E')) :
    E'.context = E.context := by
  simp only [LTy.instantiateAndSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_iwc; obtain ⟨mt, Emid⟩ := v1
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, he⟩ := h; rw [← he]
  exact LTy_instantiateWithCheck_context' ty C E mt Emid h_iwc

/-- Context preservation for a single `Identifier.instantiateAndSubst`. -/
private theorem Identifier_instantiateAndSubst_context
    (x : CoreLParams.Identifier) (C : LContext CoreLParams) (E E' : TEnv Unit) (m : LMonoTy)
    (h : Identifier.instantiateAndSubst x C E = .ok (some (m, E'))) :
    E'.context = E.context := by
  simp only [Identifier.instantiateAndSubst] at h
  split at h
  · rename_i ty h_find
    simp only [Bind.bind, Except.bind] at h
    elim_err h with v1 h_ias; obtain ⟨mt, Emid⟩ := v1
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, he⟩ := h; rw [← he]
    exact LTy_instantiateAndSubst_context ty C E Emid mt h_ias
  · simp [pure, Except.pure] at h

/-- `stateSubstInfo` preservation for a single `LTy.instantiateAndSubst` (the
    `subst` step leaves the env unchanged, so this reduces to `instantiateWithCheck`). -/
private theorem LTy_instantiateAndSubst_stateSubstInfo
    (ty : LTy) (C : LContext CoreLParams) (E E' : TEnv Unit) (m : LMonoTy)
    (h : LTy.instantiateAndSubst ty C E = .ok (m, E')) :
    E'.stateSubstInfo = E.stateSubstInfo := by
  simp only [LTy.instantiateAndSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_iwc; obtain ⟨mt, Emid⟩ := v1
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, he⟩ := h; rw [← he]
  exact LTy_instantiateWithCheck_preserves_stateSubstInfo ty C E mt Emid h_iwc

/-- `stateSubstInfo` preservation for a single `Identifier.instantiateAndSubst`. -/
private theorem Identifier_instantiateAndSubst_stateSubstInfo
    (x : CoreLParams.Identifier) (C : LContext CoreLParams) (E E' : TEnv Unit) (m : LMonoTy)
    (h : Identifier.instantiateAndSubst x C E = .ok (some (m, E'))) :
    E'.stateSubstInfo = E.stateSubstInfo := by
  simp only [Identifier.instantiateAndSubst] at h
  split at h
  · rename_i ty h_find
    simp only [Bind.bind, Except.bind] at h
    elim_err h with v1 h_ias; obtain ⟨mt, Emid⟩ := v1
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, he⟩ := h; rw [← he]
    exact LTy_instantiateAndSubst_stateSubstInfo ty C E Emid mt h_ias
  · simp [pure, Except.pure] at h

/-- `stateSubstInfo` preservation for `Identifier.instantiateAndSubsts`. -/
private theorem instantiateAndSubsts_preserves_stateSubstInfo
    (xs : List CoreLParams.Identifier) (C : LContext CoreLParams) (Env : TEnv Unit)
    (tys : List LMonoTy) (Env' : TEnv Unit)
    (h : Identifier.instantiateAndSubsts xs C Env = .ok (some (tys, Env'))) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  induction xs generalizing Env tys Env' with
  | nil =>
    simp only [Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, he⟩ := h; rw [← he]
  | cons x xrest ih =>
    simp only [Identifier.instantiateAndSubsts, Bind.bind, Except.bind] at h
    elim_err h with ans h_step; cases ans with
    | none => simp [pure, Except.pure] at h
    | some p =>
      obtain ⟨xty, Env_mid⟩ := p
      simp only at h
      elim_err h with ans2 h_rest; cases ans2 with
      | none => simp [pure, Except.pure] at h
      | some p2 =>
        obtain ⟨xtys, Env_end⟩ := p2
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, he⟩ := h; rw [← he]
        have h_mid_subst : Env_mid.stateSubstInfo = Env.stateSubstInfo :=
          Identifier_instantiateAndSubst_stateSubstInfo x C Env Env_mid xty h_step
        rw [ih Env_mid xtys Env_end h_rest, h_mid_subst]

theorem instantiateAndSubsts_preserves_context (xs : List CoreLParams.Identifier)
    (C : LContext CoreLParams) (Env : TEnv Unit) (tys : List LMonoTy) (Env' : TEnv Unit)
    (h : Identifier.instantiateAndSubsts xs C Env = .ok (some (tys, Env'))) :
    Env'.context = Env.context := by
  induction xs generalizing Env tys Env' with
  | nil =>
    simp only [Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, he⟩ := h; rw [← he]
  | cons x xrest ih =>
    simp only [Identifier.instantiateAndSubsts, Bind.bind, Except.bind] at h
    elim_err h with ans h_step; cases ans with
    | none => simp [pure, Except.pure] at h
    | some p =>
      obtain ⟨xty, Env_mid⟩ := p
      simp only at h
      elim_err h with ans2 h_rest; cases ans2 with
      | none => simp [pure, Except.pure] at h
      | some p2 =>
        obtain ⟨xtys, Env_end⟩ := p2
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, he⟩ := h; rw [← he]
        have h_mid_ctx : Env_mid.context = Env.context :=
          Identifier_instantiateAndSubst_context x C Env Env_mid xty h_step
        rw [ih Env_mid xtys Env_end h_rest, h_mid_ctx]

/-- WF preservation for a single `LTy.instantiateAndSubst` (the `subst` step
    leaves the env unchanged, so this reduces to `instantiateWithCheck`). -/
private theorem LTy_instantiateAndSubst_TEnvWF
    (ty : LTy) (C : LContext CoreLParams) (E E' : TEnv Unit) (m : LMonoTy)
    (h : LTy.instantiateAndSubst ty C E = .ok (m, E'))
    (h_wf : TEnvWF (T := CoreLParams) E) :
    TEnvWF (T := CoreLParams) E' := by
  simp only [LTy.instantiateAndSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_iwc; obtain ⟨mt, Emid⟩ := v1
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, he⟩ := h; rw [← he]
  exact LTy_instantiateWithCheck_TEnvWF ty C E mt Emid h_iwc h_wf

/-- WF preservation for a single `Identifier.instantiateAndSubst`. -/
private theorem Identifier_instantiateAndSubst_TEnvWF
    (x : CoreLParams.Identifier) (C : LContext CoreLParams) (E E' : TEnv Unit) (m : LMonoTy)
    (h : Identifier.instantiateAndSubst x C E = .ok (some (m, E')))
    (h_wf : TEnvWF (T := CoreLParams) E) :
    TEnvWF (T := CoreLParams) E' := by
  simp only [Identifier.instantiateAndSubst] at h
  split at h
  · rename_i ty h_find
    simp only [Bind.bind, Except.bind] at h
    elim_err h with v1 h_ias; obtain ⟨mt, Emid⟩ := v1
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, he⟩ := h; rw [← he]
    exact LTy_instantiateAndSubst_TEnvWF ty C E Emid mt h_ias h_wf
  · simp [pure, Except.pure] at h

theorem instantiateAndSubsts_preserves_wf (xs : List CoreLParams.Identifier)
    (C : LContext CoreLParams) (Env : TEnv Unit) (tys : List LMonoTy) (Env' : TEnv Unit)
    (h : Identifier.instantiateAndSubsts xs C Env = .ok (some (tys, Env')))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) Env' := by
  induction xs generalizing Env tys Env' with
  | nil =>
    simp only [Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, he⟩ := h; rw [← he]; exact h_wf
  | cons x xrest ih =>
    simp only [Identifier.instantiateAndSubsts, Bind.bind, Except.bind] at h
    elim_err h with ans h_step; cases ans with
    | none => simp [pure, Except.pure] at h
    | some p =>
      obtain ⟨xty, Env_mid⟩ := p
      simp only at h
      elim_err h with ans2 h_rest; cases ans2 with
      | none => simp [pure, Except.pure] at h
      | some p2 =>
        obtain ⟨xtys, Env_end⟩ := p2
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, he⟩ := h; rw [← he]
        have h_mid_wf : TEnvWF (T := CoreLParams) Env_mid :=
          Identifier_instantiateAndSubst_TEnvWF x C Env Env_mid xty h_step h_wf
        exact ih Env_mid xtys Env_end h_rest h_mid_wf

/-- WF preservation for `instantiateEnvWithSubst`: only `genEnv` changes (via
    `genTyVars`), the context and `stateSubstInfo` are untouched, and genState
    is monotone. -/
private theorem instantiateEnvWithSubst_TEnvWF
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv Unit)
    (result : LMonoTys × TEnv Unit × Subst)
    (h : LMonoTys.instantiateEnvWithSubst ids mtys Env = .ok result)
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) result.2.fst := by
  simp only [LMonoTys.instantiateEnvWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_gen; obtain ⟨freshtvs, genEnv'⟩ := v1
  simp only [Except.ok.injEq] at h
  rw [← h]
  show TEnvWF (T := CoreLParams)
    ({ genEnv := genEnv', stateSubstInfo := Env.stateSubstInfo } : TEnv Unit)
  have h_ctx :
      ({ genEnv := genEnv', stateSubstInfo := Env.stateSubstInfo } : TEnv Unit).context
        = Env.context :=
    TGenEnv.genTyVars_context ids.length Env.genEnv freshtvs genEnv' h_gen
  have h_mono :
      ({ genEnv := genEnv', stateSubstInfo := Env.stateSubstInfo } : TEnv Unit).genEnv.genState.tyGen
        ≥ Env.genEnv.genState.tyGen :=
    genTyVars_tyGen_mono ids.length Env.genEnv freshtvs genEnv' h_gen
  have h_subst :
      ({ genEnv := genEnv', stateSubstInfo := Env.stateSubstInfo } : TEnv Unit).stateSubstInfo
        = Env.stateSubstInfo := rfl
  exact {
    aliasesWF := h_ctx ▸ h_wf.aliasesWF
    substFreshForGen := h_subst ▸ SubstFreshForGen.mono _ _ _ h_wf.substFreshForGen h_mono
    ctxFreshForGen := h_ctx ▸ ContextFreshForGen.mono _ _ _ h_wf.ctxFreshForGen h_mono
    boundVarsNodup := fun y xty hf => h_wf.boundVarsNodup y xty (h_ctx ▸ hf)
    boundVarsFresh := fun y xty hf v hv n hn =>
      h_wf.boundVarsFresh y xty (h_ctx ▸ hf) v hv n (Nat.le_trans h_mono hn)
  }

/-- WF preservation for the `go` loop inside `instantiateWithSubst`. -/
private theorem instantiateWithSubst_go_TEnvWF (C : LContext CoreLParams)
    (tys : LTys) :
    ∀ (Env : TEnv Unit) (result : LMonoTys × TEnv Unit),
      LMonoTySignature.instantiateWithSubst.go C Env tys = .ok result →
      TEnvWF (T := CoreLParams) Env →
      TEnvWF (T := CoreLParams) result.2 := by
  induction tys with
  | nil =>
    intro Env result h h_wf
    simp only [LMonoTySignature.instantiateWithSubst.go] at h
    injection h with h'; rw [← h']; exact h_wf
  | cons t tr ih =>
    intro Env result h h_wf
    simp only [LMonoTySignature.instantiateWithSubst.go, Bind.bind, Except.bind] at h
    elim_err h with v1 h_iwc; obtain ⟨mt, Env_mid⟩ := v1
    elim_err h with v2 h_rest; obtain ⟨mtrest, Env_end⟩ := v2
    injection h with h'; rw [← h']
    have h_mid_wf : TEnvWF (T := CoreLParams) Env_mid :=
      LTy_instantiateWithCheck_TEnvWF t C Env mt Env_mid h_iwc h_wf
    exact ih Env_mid (mtrest, Env_end) h_rest h_mid_wf

theorem instantiateWithSubst_preserves_wf (C : LContext CoreLParams)
    (Env : TEnv Unit) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature Unit)
    (result : LMonoTySignature × TEnv Unit × Subst)
    (h : LMonoTySignature.instantiateWithSubst C Env tyArgs sig = .ok result)
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) result.2.fst := by
  simp only [LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_env; obtain ⟨mtys, Env₁, S⟩ := v1
  elim_err h with v2 h_go; obtain ⟨newtys, Env₂⟩ := v2
  simp only [Except.ok.injEq] at h
  rw [← h]
  have h_env_wf : TEnvWF (T := CoreLParams) Env₁ :=
    instantiateEnvWithSubst_TEnvWF tyArgs (ListMap.values sig) Env (mtys, Env₁, S) h_env h_wf
  exact instantiateWithSubst_go_TEnvWF C _ Env₁ (newtys, Env₂) h_go h_env_wf

/-! ### Plumbing helpers for the call obligations -/

/-- `freeVarChecks` succeeding implies each expression is well-scoped. -/
theorem freeVarChecks_implies_WellScoped (Env : TEnv Unit)
    (es : List (LExpr CoreLParams.mono))
    (h : Env.freeVarChecks es = .ok ()) :
    ∀ e, e ∈ es → WellScoped e Env.context := by
  induction es with
  | nil => intro e he; simp at he
  | cons hd tl ih =>
    simp only [TEnv.freeVarChecks, Bind.bind, Except.bind] at h
    elim_err h with v1 h_hd
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact TEnv.freeVarCheck_implies_fvars_in_knownVars Env e _ h_hd
    · exact ih h e he

/-- `resolves.go` produces `acc.length + rest.length` results. -/
private theorem resolves_go_length (C : LContext CoreLParams)
    (es : List (LExpr CoreLParams.mono)) :
    ∀ (Env Env' : TEnv Unit) (acc ets : List (LExprT CoreLParams.mono)),
      LExpr.resolves.go C Env es acc = .ok (ets, Env') →
      ets.length = acc.length + es.length := by
  induction es with
  | nil =>
    intro Env Env' acc ets h
    simp only [LExpr.resolves.go] at h
    obtain ⟨h1, _⟩ := h
    simp [List.length_reverse]
  | cons hd tl ih =>
    intro Env Env' acc ets h
    simp only [LExpr.resolves.go, Bind.bind, Except.bind] at h
    elim_err h with v1 h_hd; obtain ⟨et, Env_mid⟩ := v1
    have h_ih := ih Env_mid Env' (et :: acc) ets h
    simp only [List.length_cons] at h_ih ⊢
    omega

/-- `resolves` preserves list length. -/
theorem resolves_preserves_length (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List (LExpr CoreLParams.mono)) (ets : List (LExprT CoreLParams.mono))
    (h : LExpr.resolves C Env es = .ok (ets, Env')) :
    ets.length = es.length := by
  simp only [LExpr.resolves] at h
  have := resolves_go_length C es Env Env' [] ets h
  simpa using this

/-- `LTy.instantiateWithCheck` on a `forAll []` scheme reduces to
    `LMonoTy.resolveAliases` (the `instantiate` step is a no-op for nil binders). -/
private theorem instantiateWithCheck_forAll_nil_resolveAliases
    (m : LMonoTy) (C : LContext CoreLParams) (Env Env' : TEnv Unit) (mt : LMonoTy)
    (h : LTy.instantiateWithCheck (LTy.forAll [] m) C Env = .ok (mt, Env')) :
    ∃ Env'', LMonoTy.resolveAliases m Env = .ok (mt, Env'') := by
  simp only [LTy.instantiateWithCheck, LTy.resolveAliases, LTy.instantiate,
    Bind.bind, Except.bind] at h
  elim_err h with v1 h_ra; obtain ⟨mty', Env1⟩ := v1
  simp only at h h_ra
  elim_errs h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h; subst h1 h2
  exact ⟨Env1, h_ra⟩

/-- Decomposition of `instantiateEnvWithSubst`: the returned substitution is
    `[zip ids (map ftvar freshtvs)]` with `freshtvs` generated from `ids.length`,
    the output monotypes are `subst S mtys`, and only `genEnv` changes. -/
private theorem instantiateEnvWithSubst_decompose
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv Unit)
    (result : LMonoTys × TEnv Unit × Subst)
    (h : LMonoTys.instantiateEnvWithSubst ids mtys Env = .ok result) :
    ∃ freshtvs genEnv',
      TGenEnv.genTyVars ids.length Env.genEnv = .ok (freshtvs, genEnv') ∧
      result.1 = LMonoTys.subst [ids.zip (freshtvs.map LMonoTy.ftvar)] mtys ∧
      result.2.2 = [ids.zip (freshtvs.map LMonoTy.ftvar)] ∧
      result.2.1.context = Env.context := by
  simp only [LMonoTys.instantiateEnvWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v1 h_gen; obtain ⟨freshtvs, genEnv'⟩ := v1
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨freshtvs, genEnv', h_gen, rfl, rfl, ?_⟩
  show genEnv'.context = Env.context
  exact TGenEnv.genTyVars_context ids.length Env.genEnv freshtvs genEnv' h_gen

/-- The `go` loop of `instantiateWithSubst` maps `instantiateWithCheck` over
    `forAll []`-wrapped monotypes, so each output is alias-equivalent to the
    corresponding input (aliases are preserved through the loop). -/
private theorem instantiateWithSubst_go_elem_aliasEquiv (C : LContext CoreLParams)
    (tys : LTys) (Env : TEnv Unit) (newtys : LMonoTys) (Env_out : TEnv Unit)
    (h : LMonoTySignature.instantiateWithSubst.go C Env tys = .ok (newtys, Env_out))
    (h_aw : TContext.AliasesWF Env.context) :
    newtys.length = tys.length ∧
    ∀ (i : Nat) (hi : i < tys.length) (hi' : i < newtys.length) (m : LMonoTy),
      tys[i] = .forAll [] m →
      AliasEquiv Env.context.aliases m (newtys[i]'hi') := by
  induction tys generalizing Env newtys Env_out with
  | nil =>
    simp only [LMonoTySignature.instantiateWithSubst.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    refine ⟨rfl, ?_⟩
    intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons t trest ih =>
    simp only [LMonoTySignature.instantiateWithSubst.go, Bind.bind, Except.bind] at h
    elim_err h with v1 h_iwc; obtain ⟨mt, Env_mid⟩ := v1
    elim_err h with v2 h_rest; obtain ⟨mtrest, Env_end⟩ := v2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_nt, _⟩ := h; subst h_nt
    have h_mid_ctx : Env_mid.context = Env.context :=
      LTy_instantiateWithCheck_context' t C Env mt Env_mid h_iwc
    obtain ⟨h_len_rest, h_ae_rest⟩ := ih Env_mid mtrest Env_end h_rest (h_mid_ctx ▸ h_aw)
    refine ⟨by simp only [List.length_cons, h_len_rest], ?_⟩
    intro i hi hi' m h_eq
    match i with
    | 0 =>
      simp only [List.getElem_cons_zero] at h_eq ⊢
      obtain ⟨Env'', h_ra⟩ :=
        instantiateWithCheck_forAll_nil_resolveAliases m C Env Env_mid mt (h_eq ▸ h_iwc)
      exact resolveAliases_aliasEquiv (T := CoreLParams) m Env mt Env'' h_ra rfl h_aw
    | k + 1 =>
      simp only [List.getElem_cons_succ] at h_eq ⊢
      have h_k_rest : k < trest.length := by
        simp only [List.length_cons] at hi; omega
      have h_k_new : k < mtrest.length := by
        rw [h_len_rest]; exact h_k_rest
      have h_ae := h_ae_rest k h_k_rest h_k_new m h_eq
      rw [h_mid_ctx] at h_ae
      exact h_ae

/-- Per-element decomposition of `instantiateWithSubst`: the returned type-arg
    substitution is `[zip typeArgs (map ftvar freshVars)]` for fresh vars matching
    `typeArgs` in count, and the i-th output signature value is alias-equivalent
    to the two-step substitution `subst tyArgSubst (sig.values[i])`. -/
theorem instantiateWithSubst_elem_aliasEquiv (C : LContext CoreLParams)
    (Env₁ : TEnv Unit) (typeArgs : List TyIdentifier) (sig : @LMonoTySignature Unit)
    (v2 : (@LMonoTySignature Unit) × TEnv Unit × Subst)
    (h : LMonoTySignature.instantiateWithSubst C Env₁ typeArgs sig = .ok v2)
    (i : Nat) (hj : i < (ListMap.values sig).length)
    (h_aw : TContext.AliasesWF Env₁.context) :
    ∃ (freshVars : List TyIdentifier) (hi2 : i < (ListMap.values v2.fst).length),
      freshVars.length = typeArgs.length ∧
      v2.2.snd = [typeArgs.zip (freshVars.map LMonoTy.ftvar)] ∧
      AliasEquiv Env₁.context.aliases
        (LMonoTy.subst v2.2.snd ((ListMap.values sig).get ⟨i, hj⟩))
        ((ListMap.values v2.fst).get ⟨i, hi2⟩) := by
  -- Unfold instantiateWithSubst: instantiateEnvWithSubst then the go loop.
  simp only [LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v_env h_env; obtain ⟨mtys, Env_e, S⟩ := v_env
  elim_err h with v_go h_go; obtain ⟨newtys, Env₂⟩ := v_go
  simp only [Except.ok.injEq] at h
  -- v2 = (sig.keys.zip newtys, Env₂, S)
  subst h
  -- Decompose instantiateEnvWithSubst: S = [zip typeArgs (map ftvar freshtvs)],
  -- mtys = subst S sig.values, and only genEnv changes.
  obtain ⟨freshtvs, genEnv', h_gen, h_mtys, h_S, h_ctx⟩ :=
    instantiateEnvWithSubst_decompose typeArgs (ListMap.values sig) Env₁ (mtys, Env_e, S) h_env
  simp only at h_mtys h_S h_ctx
  -- The go loop maps `instantiateWithCheck` over `mtys.map (forAll [] ·)`.
  have h_aw_e : TContext.AliasesWF Env_e.context := h_ctx ▸ h_aw
  obtain ⟨h_go_len, h_go_ae⟩ :=
    instantiateWithSubst_go_elem_aliasEquiv C (mtys.map (fun m => LTy.forAll [] m))
      Env_e newtys Env₂ h_go h_aw_e
  -- Length bookkeeping: newtys.length = mtys.length = sig.values.length.
  have h_mtys_len : mtys.length = (ListMap.values sig).length := by
    rw [h_mtys, LMonoTys_subst_eq_map, List.length_map]
  have h_nt_len : newtys.length = (ListMap.values sig).length := by
    rw [h_go_len, List.length_map, h_mtys_len]
  have h_keys_len : (ListMap.keys sig).length = (ListMap.values sig).length := by
    rw [ListMap.keys_eq_map_fst, ListMap.values_eq_map_snd, List.length_map, List.length_map]
  -- `v2.fst = sig.keys.zip newtys`, whose `values` is exactly `newtys`.
  have h_vals : ListMap.values ((ListMap.keys sig).zip newtys) = newtys := by
    rw [ListMap.values_eq_map_snd, List.map_snd_zip]
    rw [h_keys_len, h_nt_len]; exact Nat.le_refl _
  -- hi2 witness.
  have hi2 : i < (ListMap.values ((ListMap.keys sig).zip newtys)).length := by
    rw [h_vals, h_nt_len]; exact hj
  refine ⟨freshtvs, hi2, ?_, ?_, ?_⟩
  · exact TGenEnv.genTyVars_length typeArgs.length Env₁.genEnv freshtvs genEnv' h_gen
  · exact h_S
  · -- the AliasEquiv: rewrite both sides to `subst S sig.values[i]` and `newtys[i]`.
    have hi_nt : i < newtys.length := h_nt_len ▸ hj
    have hi_tys : i < (mtys.map (fun m => LTy.forAll [] m)).length := by
      rw [List.length_map, h_mtys_len]; exact hj
    have h_tys_i : (mtys.map (fun m => LTy.forAll [] m))[i]'hi_tys =
        LTy.forAll [] (mtys[i]'(by rw [h_mtys_len]; exact hj)) := by
      rw [List.getElem_map]
    have h_ae := h_go_ae i hi_tys hi_nt (mtys[i]'(by rw [h_mtys_len]; exact hj)) h_tys_i
    rw [h_ctx] at h_ae
    -- Reduce the goal's getElems.
    have h_lhs_get : ((ListMap.values ((ListMap.keys sig).zip newtys)).get ⟨i, hi2⟩) =
        newtys[i]'hi_nt := by
      rw [List.get_eq_getElem]; exact List.getElem_of_eq h_vals hi2
    rw [List.get_eq_getElem, h_lhs_get]
    -- `subst S sig.values[i] = mtys[i]`.
    have hi_mtys : i < mtys.length := by rw [h_mtys_len]; exact hj
    have h_subst_i : LMonoTy.subst S ((ListMap.values sig)[i]'hj) =
        mtys[i]'hi_mtys := by
      subst h_S h_mtys
      have h_map : LMonoTys.subst [typeArgs.zip (List.map LMonoTy.ftvar freshtvs)]
          (ListMap.values sig) =
          (ListMap.values sig).map
            (LMonoTy.subst [typeArgs.zip (List.map LMonoTy.ftvar freshtvs)]) :=
        LMonoTys_subst_eq_map _ _
      rw [List.getElem_of_eq h_map, List.getElem_map]
      rfl
    rw [h_subst_i]
    exact h_ae

/-- The i-th resolved input type, substituted by the final substitution, is
    alias-equivalent to the i-th procedure input type instantiated via `σ`.
    (The relation is `AliasEquiv` rather than `=` because `instantiateWithSubst`
    resolves aliases in the formal types.) -/
theorem call_input_type_eq (C : LContext CoreLParams) (Env_lhs : TEnv Unit)
    (proc : Procedure) (callArgs : List (CallArg Expression))
    (v1 : List LMonoTy) (v2 : (@LMonoTySignature Unit) × TEnv Unit × Subst)
    (v3 : List (LExprT CoreLParams.mono) × TEnv Unit) (v4 : SubstInfo)
    (i : Nat)
    (hi : i < (CallArg.getInputExprs callArgs).length)
    (hj : i < (ListMap.values proc.header.inputs).length)
    (h_len : v3.fst.length = (CallArg.getInputExprs callArgs).length)
    (h_inst : LMonoTySignature.instantiateWithSubst C Env_lhs proc.header.typeArgs proc.header.inputs = .ok v2)
    (h_unify : Constraints.unify
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
        v3.snd.stateSubstInfo = .ok v4)
    (h_closed : ProcHeaderClosed proc)
    (h_aliases_wf : TContext.AliasesWF Env_lhs.context)
    (h_absorbs_v2 : Subst.absorbs v4.subst v2.2.fst.stateSubstInfo.subst) :
    AliasEquiv Env_lhs.context.aliases
      (LMonoTy.subst (v3.snd.updateSubst v4).stateSubstInfo.subst
        ((v3.fst.get ⟨i, h_len ▸ hi⟩).toLMonoTy))
      (LMonoTy.subst
        [proc.header.typeArgs.zip
          (proc.header.typeArgs.map (fun a => LMonoTy.subst (v3.snd.updateSubst v4).stateSubstInfo.subst
            (LMonoTy.subst v2.2.snd (.ftvar a))))]
        ((ListMap.values proc.header.inputs).get ⟨i, hj⟩)) := by
  -- Abbreviations (definitionally; `S_final` is `v4.subst`).
  show AliasEquiv Env_lhs.context.aliases
    (LMonoTy.subst v4.subst ((v3.fst.get ⟨i, h_len ▸ hi⟩).toLMonoTy))
    (LMonoTy.subst
      [proc.header.typeArgs.zip
        (proc.header.typeArgs.map (fun a => LMonoTy.subst v4.subst
          (LMonoTy.subst v2.2.snd (.ftvar a))))]
      ((ListMap.values proc.header.inputs).get ⟨i, hj⟩))
  -- i-th input formal via the elem decomposition of instantiateWithSubst.
  obtain ⟨freshVars, hi2, h_fv_len, h_tyArgSubst, h_elem_ae⟩ :=
    instantiateWithSubst_elem_aliasEquiv C Env_lhs proc.header.typeArgs proc.header.inputs
      v2 h_inst i hj h_aliases_wf
  -- (1) unify_sound on the i-th input constraint gives the equality `h_eq`.
  have h_mem : ((List.map toLMonoTy v3.fst).get ⟨i, by rw [List.length_map]; exact h_len ▸ hi⟩,
      (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)).get
        ⟨i, by rw [LMonoTys_subst_eq_map, List.length_map]; exact hi2⟩) ∈
      ((List.map toLMonoTy v3.fst).zip
        (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
        v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
          (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs)))) := by
    apply List.mem_append_left
    exact zip_getElem_mem _ _ i (by rw [List.length_map]; exact h_len ▸ hi)
      (by rw [LMonoTys_subst_eq_map, List.length_map]; exact hi2)
  have h_eq := Constraints.unify_sound _ _ _ h_unify _ h_mem
  simp only [List.get_eq_getElem] at h_eq
  -- Rewrite the two getElems into the forms `call_type_bridge` expects.
  have hi_a : i < (List.map toLMonoTy v3.fst).length := by rw [List.length_map]; exact h_len ▸ hi
  have hi_b : i < (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)).length := by
    rw [LMonoTys_subst_eq_map, List.length_map]; exact hi2
  have h_a_eq : (List.map toLMonoTy v3.fst)[i]'hi_a = (v3.fst.get ⟨i, h_len ▸ hi⟩).toLMonoTy := by
    simp only [List.get_eq_getElem, List.getElem_map]
  have h_b_eq : (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst))[i]'hi_b =
      LMonoTy.subst v2.2.fst.stateSubstInfo.subst ((ListMap.values v2.fst).get ⟨i, hi2⟩) := by
    have h_map := LMonoTys_subst_eq_map v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)
    simp only [List.get_eq_getElem, h_map, List.getElem_map]
  rw [h_a_eq, h_b_eq] at h_eq
  -- h_eq : subst v4.subst (toLMonoTy v3.fst[i])
  --        = subst v4.subst (subst v2.2.fst.subst inp_sig.values[i])
  -- Collapse the inner v2.2.fst.subst via absorption.
  rw [LMonoTy.subst_absorbs v4.subst v2.2.fst.stateSubstInfo.subst _ h_absorbs_v2] at h_eq
  -- h_eq : subst v4.subst (toLMonoTy v3.fst[i]) = subst v4.subst inp_sig.values[i]
  -- (2) AliasEquiv from the instantiate elem decomposition, under v4.subst, symm.
  have h_ae_S := AliasEquiv_subst Env_lhs.context.aliases _ _ v4.subst h_elem_ae
    (fun a ha => h_aliases_wf a ha)
  -- h_ae_S : AliasEquiv aliases (subst v4.subst (subst v2.2.snd formal))
  --                             (subst v4.subst inp_sig.values[i])
  -- (3) Apply the shared kernel.
  exact call_type_bridge Env_lhs.context.aliases proc.header.typeArgs v4.subst v2.2.snd
    _ _ ((ListMap.values proc.header.inputs).get ⟨i, hj⟩)
    (fun x hx => h_closed.1 _ (List.get_mem _ _) x hx)
    h_eq
    (AliasEquiv.symm h_ae_S)

/-- Per-element decomposition of `Identifier.instantiateAndSubsts`: the i-th
    output type is the alias-resolved context type, substituted by the running
    `stateSubstInfo`. The context type `forAll [] mty_i` is monomorphic at the
    call site (`ContextMono`); we read off the raw `mty_i`, the resolved `mt_i`,
    and that they are alias-equivalent. -/
theorem instantiateAndSubsts_elem (xs : List CoreLParams.Identifier)
    (C : LContext CoreLParams) (Env Env_lhs : TEnv Unit) (v1 : List LMonoTy)
    (h : Identifier.instantiateAndSubsts xs C Env = .ok (some (v1, Env_lhs)))
    (i : Nat) (hi : i < xs.length)
    (h_mono : ContextMono Env.context)
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ (mty_i mt_i : LMonoTy) (hi' : i < v1.length),
      Env.context.types.find? xs[i] = some (LTy.forAll [] mty_i) ∧
      (v1[i]'hi') = LMonoTy.subst Env.stateSubstInfo.subst mt_i ∧
      AliasEquiv Env.context.aliases mty_i mt_i := by
  induction xs generalizing Env Env_lhs v1 i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons x xrest ih =>
    -- Decompose `instantiateAndSubsts (x :: xrest)`.
    simp only [Identifier.instantiateAndSubsts, Bind.bind, Except.bind] at h
    elim_err h with ans h_step; cases ans with
    | none => simp [pure, Except.pure] at h
    | some p =>
      obtain ⟨xty, Env_mid⟩ := p
      simp only at h
      elim_err h with ans2 h_rest; cases ans2 with
      | none => simp [pure, Except.pure] at h
      | some p2 =>
        obtain ⟨xtys, Env_end⟩ := p2
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h_v1, _⟩ := h; subst h_v1
        -- Head: `instantiateAndSubst x C Env = .ok (some (xty, Env_mid))`.
        -- find? x = some ty, and ty is mono so ty = forAll [] mty_x.
        simp only [Identifier.instantiateAndSubst] at h_step
        split at h_step
        · rename_i ty h_find
          -- ty is monomorphic.
          have h_bv : LTy.boundVars ty = [] := h_mono _ ty h_find
          obtain ⟨xsbv, body⟩ := ty
          simp only [LTy.boundVars] at h_bv; subst h_bv
          -- Peel the `Option`-lift: `instantiateAndSubst (forAll [] body) C Env = .ok (mt_x, Env_iwc)`.
          simp only [Bind.bind, Except.bind] at h_step
          elim_err h_step with v_ias h_ias; obtain ⟨mt_x, Env_iwc⟩ := v_ias
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_step
          obtain ⟨h_xty, h_envmid⟩ := h_step
          -- Decompose `LTy.instantiateAndSubst` into its `instantiateWithCheck` + subst steps.
          simp only [LTy.instantiateAndSubst, Bind.bind, Except.bind] at h_ias
          elim_err h_ias with v_iwc h_iwc; obtain ⟨mt_resolved, Env_resolved⟩ := v_iwc
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_ias
          obtain ⟨h_mtx, h_env_res⟩ := h_ias
          -- resolveAliases body Env = .ok (mt_resolved, _).
          obtain ⟨Env_ra, h_ra⟩ :=
            instantiateWithCheck_forAll_nil_resolveAliases body C Env Env_resolved mt_resolved h_iwc
          -- stateSubstInfo / context unchanged by instantiateWithCheck.
          have h_iwc_subst : Env_resolved.stateSubstInfo = Env.stateSubstInfo :=
            LTy_instantiateWithCheck_preserves_stateSubstInfo (LTy.forAll [] body) C Env mt_resolved
              Env_resolved h_iwc
          have h_iwc_ctx : Env_resolved.context = Env.context :=
            LTy_instantiateWithCheck_context' (LTy.forAll [] body) C Env mt_resolved Env_resolved h_iwc
          -- `mt_x = subst Env_resolved.subst mt_resolved` and `Env_iwc = Env_resolved`.
          have h_envmid_eq : Env_mid.stateSubstInfo = Env.stateSubstInfo := by
            rw [← h_envmid, ← h_env_res]; exact h_iwc_subst
          have h_envmid_ctx : Env_mid.context = Env.context := by
            rw [← h_envmid, ← h_env_res]; exact h_iwc_ctx
          -- `v1[0] = xty = mt_x = subst Env.subst mt_resolved`.
          have h_xty_eq : xty = LMonoTy.subst Env.stateSubstInfo.subst mt_resolved := by
            rw [← h_xty, ← h_mtx, h_iwc_subst]
          match i with
          | 0 =>
            refine ⟨body, mt_resolved, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
            · simpa only [List.getElem_cons_zero] using h_find
            · simp only [List.getElem_cons_zero]; exact h_xty_eq
            · exact resolveAliases_aliasEquiv (T := CoreLParams) body Env mt_resolved Env_ra h_ra rfl h_aw
          | k + 1 =>
            -- Recurse on xrest with Env_mid; rewrite Env_mid facts back to Env.
            have h_k : k < xrest.length := by
              simp only [List.length_cons] at hi; omega
            obtain ⟨mty_k, mt_k, hi'_k, h_find_k, h_v1_k, h_ae_k⟩ :=
              ih Env_mid Env_end xtys h_rest k h_k (h_envmid_ctx ▸ h_mono) (h_envmid_ctx ▸ h_aw)
            refine ⟨mty_k, mt_k, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
            · simp only [List.getElem_cons_succ]; rw [← h_envmid_ctx]; exact h_find_k
            · simp only [List.getElem_cons_succ]; rw [h_v1_k, h_envmid_eq]
            · rw [← h_envmid_ctx]; exact h_ae_k
        · simp [pure, Except.pure] at h_step

/-- The i-th lhs variable's substituted context type equals the i-th procedure
    output type instantiated via `σ`. -/
theorem call_output_type_eq (C : LContext CoreLParams) (Env Env_lhs : TEnv Unit)
    (proc : Procedure) (callArgs : List (CallArg Expression))
    (v1 : List LMonoTy) (v2 : (@LMonoTySignature Unit) × TEnv Unit × Subst)
    (v3 : List (LExprT CoreLParams.mono) × TEnv Unit) (v4 : SubstInfo)
    (i : Nat)
    (hi : i < (CallArg.getLhs callArgs).length)
    (hj : i < (ListMap.values proc.header.outputs).length)
    (h_mono : ContextMono Env.context)
    (h_inst_lhs : Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
      = .ok (some (v1, Env_lhs)))
    (h_unify : Constraints.unify
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
        v3.snd.stateSubstInfo = .ok v4)
    (h_closed : ProcHeaderClosed proc)
    (h_aw : TContext.AliasesWF Env.context)
    (h_subst_v2_env : v2.2.fst.stateSubstInfo.subst = Env.stateSubstInfo.subst)
    (h_absorbs_v2 : Subst.absorbs v4.subst v2.2.fst.stateSubstInfo.subst) :
    ∃ mty, AliasEquiv Env.context.aliases mty
        (LMonoTy.subst
          [proc.header.typeArgs.zip
            (proc.header.typeArgs.map (fun a => LMonoTy.subst (v3.snd.updateSubst v4).stateSubstInfo.subst
              (LMonoTy.subst v2.2.snd (.ftvar a))))]
          ((ListMap.values proc.header.outputs).get ⟨i, hj⟩)) ∧
      (Env.context.subst (v3.snd.updateSubst v4).stateSubstInfo.subst).types.find?
        (CallArg.getLhs callArgs)[i] = some (LTy.forAll [] mty) := by
  -- `S_final` is `v4.subst` definitionally.
  show ∃ mty, AliasEquiv Env.context.aliases mty
      (LMonoTy.subst
        [proc.header.typeArgs.zip
          (proc.header.typeArgs.map (fun a => LMonoTy.subst v4.subst
            (LMonoTy.subst v2.2.snd (.ftvar a))))]
        ((ListMap.values proc.header.outputs).get ⟨i, hj⟩)) ∧
    (Env.context.subst v4.subst).types.find?
      (CallArg.getLhs callArgs)[i] = some (LTy.forAll [] mty)
  -- (1) Decompose the i-th lhs element.
  obtain ⟨mty_i, mt_i, hi', h_find, h_v1_i, h_elem_ae⟩ :=
    instantiateAndSubsts_elem (CallArg.getLhs callArgs) C Env Env_lhs v1 h_inst_lhs i hi h_mono h_aw
  -- (2) The find side gives the witness `mty := subst v4.subst mty_i`.
  refine ⟨LMonoTy.subst v4.subst mty_i, ?_, ?_⟩
  case _ =>
    -- (3) unify_sound on the i-th OUTPUT constraint (right append).
    have hi_v1 : i < v1.length := hi'
    have hi_ret : i < (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
        (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))).length := by
      rw [LMonoTys_subst_eq_map, List.length_map, List.length_map]; exact hj
    have h_mem : (v1.get ⟨i, hi_v1⟩,
        (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
          (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))).get ⟨i, hi_ret⟩) ∈
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs)))) := by
      apply List.mem_append_right
      exact zip_getElem_mem _ _ i hi_v1 hi_ret
    have h_eq := Constraints.unify_sound _ _ _ h_unify _ h_mem
    simp only [List.get_eq_getElem] at h_eq
    -- Rewrite the i-th getElems into closed forms.
    have h_ret_i : (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
        (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs)))[i]'hi_ret =
        LMonoTy.subst v2.2.fst.stateSubstInfo.subst
          (LMonoTy.subst v2.2.snd ((ListMap.values proc.header.outputs).get ⟨i, hj⟩)) := by
      have h_map := LMonoTys_subst_eq_map v2.2.fst.stateSubstInfo.subst
        (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))
      simp only [List.get_eq_getElem, h_map, List.getElem_map]
    rw [h_ret_i] at h_eq
    -- (4) Collapse RHS: subst_absorbs then subst_diag_eq.
    rw [LMonoTy.subst_absorbs v4.subst v2.2.fst.stateSubstInfo.subst _ h_absorbs_v2] at h_eq
    -- h_eq : subst v4.subst v1[i] = subst v4.subst (subst v2.2.snd outputs[i])
    -- (5) Collapse LHS: v1[i] = subst Env.subst mt_i = subst v2.2.fst.subst mt_i.
    rw [h_v1_i, ← h_subst_v2_env,
      LMonoTy.subst_absorbs v4.subst v2.2.fst.stateSubstInfo.subst _ h_absorbs_v2] at h_eq
    -- h_eq : subst v4.subst mt_i = subst v4.subst (subst v2.2.snd outputs[i])
    -- (6) AliasEquiv from elem decomposition, under v4.subst.
    have h_ae_S := AliasEquiv_subst Env.context.aliases _ _ v4.subst h_elem_ae
      (fun a ha => h_aw a ha)
    -- h_ae_S : AliasEquiv aliases (subst v4.subst mty_i) (subst v4.subst mt_i)
    -- (7) Rewrite h_eq into h_ae_S's RHS, then subst_diag_eq for the σ-form.
    rw [h_eq] at h_ae_S
    rw [show LMonoTy.subst
        [proc.header.typeArgs.zip
          (proc.header.typeArgs.map (fun a => LMonoTy.subst v4.subst
            (LMonoTy.subst v2.2.snd (.ftvar a))))]
        ((ListMap.values proc.header.outputs).get ⟨i, hj⟩) =
        LMonoTy.subst v4.subst (LMonoTy.subst v2.2.snd
          ((ListMap.values proc.header.outputs).get ⟨i, hj⟩)) from
      subst_diag_eq proc.header.typeArgs v4.subst v2.2.snd _
        (fun x hx => h_closed.2 _ (List.get_mem _ _) x hx)]
    exact h_ae_S
  case _ =>
    -- find side: TContext.subst_find_some + subst_forAll_nil.
    have h_fs := TContext.subst_find_some Env.context v4.subst (CallArg.getLhs callArgs)[i]
      (LTy.forAll [] mty_i) h_find
    rw [LTy.subst_forAll_nil] at h_fs
    exact h_fs

/-- For an inout parameter (an input that also appears in outputs), the
    corresponding argument is a simple variable of the same name. -/
theorem areInoutArgsValid_implies_fvar (proc : Procedure) (args : List Expression.Expr)
    (h : Statement.areInoutArgsValid proc args = true)
    (i : Nat) (hi : i < (ListMap.keys proc.header.inputs).length)
    (h_contains : (ListMap.keys proc.header.outputs).contains
      (ListMap.keys proc.header.inputs)[i] = true)
    (h_arity : args.length = (ListMap.keys proc.header.inputs).length) :
    ∃ m ty, args[i]? = some (.fvar m (ListMap.keys proc.header.inputs)[i] ty) := by
  unfold Statement.areInoutArgsValid at h
  rw [List.all_eq_true] at h
  -- `toList` is the identity, and `keys = map Prod.fst`, so lengths line up.
  have h_toList_len : (proc.header.inputs.toList).length
      = (ListMap.keys proc.header.inputs).length := by
    rw [ListMap.keys_eq_map_fst, List.length_map]; rfl
  have hi_tl : i < (proc.header.inputs.toList).length := by rw [h_toList_len]; exact hi
  have hi_args : i < args.length := by rw [h_arity]; exact hi
  -- The i-th input key equals the first component of the i-th `toList` entry.
  have h_key_eq : ((proc.header.inputs.toList)[i]'hi_tl).1
      = (ListMap.keys proc.header.inputs)[i] := by
    simp only [ListMap.keys_eq_map_fst, List.getElem_map, ListMap.toList]
  -- The i-th zipped pair is a member, so the predicate holds there.
  have h_mem : ((proc.header.inputs.toList)[i]'hi_tl, args[i]'hi_args)
      ∈ (proc.header.inputs.toList).zip args :=
    zip_getElem_mem _ _ i hi_tl hi_args
  have h_pred := h _ h_mem
  -- `outputs.contains keys[i]` is true, so the left `!… ||` disjunct is false.
  simp only [List.get_eq_getElem, h_key_eq] at h_pred
  simp only [h_contains, Bool.not_true, Bool.false_or] at h_pred
  -- The `match arg` branch forces `arg = fvar _ keys[i] _`.
  split at h_pred
  · rename_i m id ty h_arg
    rw [beq_iff_eq] at h_pred; subst h_pred
    refine ⟨m, ty, ?_⟩
    rw [List.getElem?_eq_getElem hi_args, h_arg]
  · simp at h_pred

/-! ### Resolves soundness (lifted to lists) -/

/-- Accumulator-generalized core lemma for `resolves.go`. The output list is the
    reversed accumulator followed by the per-element results `res`, and each
    element of `es` is well-typed (under any absorbing extension of the final
    substitution) at the corresponding `res` entry. -/
private theorem resolves_go_HasType_core (C : LContext CoreLParams)
    (es : List (LExpr CoreLParams.mono)) :
    ∀ (Env Env' : TEnv Unit) (acc ets : List (LExprT CoreLParams.mono)),
      LExpr.resolves.go C Env es acc = .ok (ets, Env') →
      TEnvWF (T := CoreLParams) Env →
      FactoryWF C.functions →
      Env.context.types ≠ [] →
      (∀ e, e ∈ es → WellScoped e Env.context) →
      TEnvWF (T := CoreLParams) Env' ∧
      Env'.context = Env.context ∧
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst ∧
      ∃ (res : List (LExprT CoreLParams.mono)) (h_rlen : res.length = es.length),
        ets = acc.reverse ++ res ∧
        (∀ i (hi : i < es.length),
          ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
            Subst.polyKeysFresh (T := CoreLParams) S Env.context →
            HasType C (TContext.subst Env.context S) (es.get ⟨i, hi⟩)
              (.forAll [] (LMonoTy.subst S ((res.get ⟨i, h_rlen ▸ hi⟩).toLMonoTy)))) := by
  induction es with
  | nil =>
    intro Env Env' acc ets h h_wf h_fwf h_ne h_ws
    simp only [LExpr.resolves.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    refine ⟨h_wf, rfl, Subst.absorbs_refl _ Env.stateSubstInfo.isWF,
      [], rfl, by simp, ?_⟩
    intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons e erest ih =>
    intro Env Env' acc ets h h_wf h_fwf h_ne h_ws
    simp only [LExpr.resolves.go, Bind.bind, Except.bind] at h
    elim_err h with v_step h_step
    obtain ⟨et, Env_mid⟩ := v_step
    -- `h` is now the recursive `go` equation; `h_step` is the per-step `resolve`.
    -- Per-step facts for `e`.
    have h_ctx_mid : Env_mid.context = Env.context :=
      resolve_preserves_context e et C Env Env_mid h_step h_wf h_ne h_fwf
    have h_abs_mid : Subst.absorbs Env_mid.stateSubstInfo.subst Env.stateSubstInfo.subst :=
      resolve_absorbs e et C Env Env_mid h_step h_wf h_ne h_fwf
    have h_ws_e : WellScoped e Env.context := h_ws e List.mem_cons_self
    have h_core := resolve_HasType_core e et C Env Env_mid h_step h_wf h_fwf h_ws_e
    have h_wf_mid : TEnvWF (T := CoreLParams) Env_mid := h_core.2.2
    have h_ne_mid : Env_mid.context.types ≠ [] := by rw [h_ctx_mid]; exact h_ne
    have h_ws_rest : ∀ e', e' ∈ erest → WellScoped e' Env_mid.context := by
      rw [h_ctx_mid]; exact fun e' he' => h_ws e' (List.mem_cons_of_mem e he')
    -- Apply the IH to the tail.
    obtain ⟨h_wf', h_ctx', h_abs', res', h_rlen', h_ets', h_typ'⟩ :=
      ih Env_mid Env' (et :: acc) ets h h_wf_mid h_fwf h_ne_mid h_ws_rest
    refine ⟨h_wf', by rw [h_ctx', h_ctx_mid], ?_, et :: res', ?_, ?_, ?_⟩
    · exact Subst.absorbs_trans _ _ _ h_abs_mid h_abs'
    · simp only [List.length_cons, h_rlen']
    · simp only [List.reverse_cons] at h_ets'; simpa using h_ets'
    · intro i hi S h_abs_S h_swf h_pkf
      match i with
      | 0 =>
        have h_abs_S_mid : Subst.absorbs S Env_mid.stateSubstInfo.subst :=
          Subst.absorbs_trans _ _ _ h_abs' h_abs_S
        have h_ty := h_core.1 S h_abs_S_mid h_swf h_pkf
        simpa only [List.get_eq_getElem, List.getElem_cons_zero] using h_ty
      | k + 1 =>
        have h_k : k < erest.length := by
          simp only [List.length_cons] at hi; omega
        have h_pkf_mid : Subst.polyKeysFresh (T := CoreLParams) S Env_mid.context := by
          rw [h_ctx_mid]; exact h_pkf
        have h_ty := h_typ' k h_k S h_abs_S h_swf h_pkf_mid
        rw [h_ctx_mid] at h_ty
        simpa only [List.get_eq_getElem, List.getElem_cons_succ] using h_ty

/-- Accumulator-generalized alias-equivalence core for `resolves.go`, threading
    `ContextMono`. For each bare input free variable (`fvar m x none`, as emitted
    for inout call arguments), the resolved monotype is alias-equivalent to the
    (monomorphic) context type of `x`, under any substitution absorbing the final
    environment's substitution. Separate from `resolves_go_HasType_core` so that
    callers needing only context preservation/typing need not provide `h_mono`. -/
private theorem resolves_go_fvar_aliasEquiv_core (C : LContext CoreLParams)
    (es : List (LExpr CoreLParams.mono)) :
    ∀ (Env Env' : TEnv Unit) (acc ets : List (LExprT CoreLParams.mono)),
      LExpr.resolves.go C Env es acc = .ok (ets, Env') →
      TEnvWF (T := CoreLParams) Env →
      FactoryWF C.functions →
      Env.context.types ≠ [] →
      ContextMono Env.context →
      (∀ e, e ∈ es → WellScoped e Env.context) →
      ∃ (res : List (LExprT CoreLParams.mono)) (h_rlen : res.length = es.length),
        ets = acc.reverse ++ res ∧
        (∀ i (hi : i < es.length) m x,
          es.get ⟨i, hi⟩ = .fvar m x none →
          ∃ mty_ctx, Env.context.types.find? x = some (.forAll [] mty_ctx) ∧
            ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst →
              AliasEquiv Env.context.aliases (LMonoTy.subst S mty_ctx)
                (LMonoTy.subst S ((res.get ⟨i, h_rlen ▸ hi⟩).toLMonoTy))) := by
  induction es with
  | nil =>
    intro Env Env' acc ets h _ _ _ _ _
    simp only [LExpr.resolves.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    refine ⟨[], rfl, by simp, ?_⟩
    intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons e erest ih =>
    intro Env Env' acc ets h h_wf h_fwf h_ne h_mono h_ws
    simp only [LExpr.resolves.go, Bind.bind, Except.bind] at h
    elim_err h with v_step h_step
    obtain ⟨et, Env_mid⟩ := v_step
    have h_ctx_mid : Env_mid.context = Env.context :=
      resolve_preserves_context e et C Env Env_mid h_step h_wf h_ne h_fwf
    have h_abs_mid : Subst.absorbs Env_mid.stateSubstInfo.subst Env.stateSubstInfo.subst :=
      resolve_absorbs e et C Env Env_mid h_step h_wf h_ne h_fwf
    have h_wf_mid : TEnvWF (T := CoreLParams) Env_mid :=
      (resolve_HasType_core e et C Env Env_mid h_step h_wf h_fwf
        (h_ws e List.mem_cons_self)).2.2
    have h_ne_mid : Env_mid.context.types ≠ [] := by rw [h_ctx_mid]; exact h_ne
    have h_mono_mid : ContextMono Env_mid.context := by rw [h_ctx_mid]; exact h_mono
    have h_ws_rest : ∀ e', e' ∈ erest → WellScoped e' Env_mid.context := by
      rw [h_ctx_mid]; exact fun e' he' => h_ws e' (List.mem_cons_of_mem e he')
    -- `Env'` absorbs `Env_mid` (from the tail `go`); needed to transfer the
    -- absorption condition on the head element's alias-equivalence.
    have h_abs_tail : Subst.absorbs Env'.stateSubstInfo.subst Env_mid.stateSubstInfo.subst :=
      (resolves_go_HasType_core C erest Env_mid Env' (et :: acc) ets h h_wf_mid h_fwf
        h_ne_mid h_ws_rest).2.2.1
    obtain ⟨res', h_rlen', h_ets', h_ae'⟩ :=
      ih Env_mid Env' (et :: acc) ets h h_wf_mid h_fwf h_ne_mid h_mono_mid h_ws_rest
    refine ⟨et :: res', by simp only [List.length_cons, h_rlen'], ?_, ?_⟩
    · simp only [List.reverse_cons] at h_ets'; simpa using h_ets'
    · intro i hi m x h_fvar
      match i with
      | 0 =>
        -- Head element: use Layer 2 on the per-step `resolve`.
        simp only [List.get_eq_getElem, List.getElem_cons_zero] at h_fvar
        subst h_fvar
        obtain ⟨mty_ctx, h_find, h_ae_et⟩ :=
          resolve_fvar_none_find_aliasEquiv C Env Env_mid m x et
            h_step h_wf h_ne h_fwf h_mono
        refine ⟨mty_ctx, h_find, ?_⟩
        intro S h_abs_S
        have h_abs_S_mid : Subst.absorbs S Env_mid.stateSubstInfo.subst :=
          Subst.absorbs_trans _ _ _ h_abs_tail h_abs_S
        have h_ae := h_ae_et S h_abs_S_mid
        simpa only [List.get_eq_getElem, List.getElem_cons_zero] using h_ae
      | k + 1 =>
        have h_k : k < erest.length := by
          simp only [List.length_cons] at hi; omega
        simp only [List.get_eq_getElem, List.getElem_cons_succ] at h_fvar
        obtain ⟨mty_ctx, h_find, h_ae_S⟩ :=
          h_ae' k h_k m x (by simp only [List.get_eq_getElem]; exact h_fvar)
        rw [h_ctx_mid] at h_find
        refine ⟨mty_ctx, h_find, ?_⟩
        intro S h_abs_S
        have h_ae := h_ae_S S h_abs_S
        rw [h_ctx_mid] at h_ae
        simpa only [List.get_eq_getElem, List.getElem_cons_succ] using h_ae

/-- If `resolves` succeeds, each element satisfies `HasType` under any absorbing
    extension of the final substitution. -/
theorem resolves_HasType_core (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List (LExpr CoreLParams.mono)) (ets : List (LExprT CoreLParams.mono))
    (h : LExpr.resolves C Env es = .ok (ets, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_ws : ∀ e, e ∈ es → WellScoped e Env.context)
    (h_len : ets.length = es.length) :
    TEnvWF (T := CoreLParams) Env' ∧
    Env'.context = Env.context ∧
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst ∧
    (∀ i (hi : i < es.length),
      ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := CoreLParams) S Env.context →
        HasType C (TContext.subst Env.context S) (es.get ⟨i, hi⟩)
          (.forAll [] (LMonoTy.subst S ((ets.get ⟨i, h_len ▸ hi⟩).toLMonoTy)))) := by
  unfold LExpr.resolves at h
  obtain ⟨h_wf', h_ctx', h_abs', res, h_rlen, h_ets, h_typ⟩ :=
    resolves_go_HasType_core C es Env Env' [] ets h h_wf h_fwf h_ne h_ws
  simp only [List.reverse_nil, List.nil_append] at h_ets
  subst h_ets
  refine ⟨h_wf', h_ctx', h_abs', ?_⟩
  intro i hi S h_abs_S h_swf h_pkf
  simp only [List.get_eq_getElem]
  exact h_typ i hi S h_abs_S h_swf h_pkf

/-- Accumulator-generalized annotated-soundness core for `resolves.go`. Each
    resolved element satisfies `HasTypeA` between its erased form and its monotype
    (the S-independent annotation-consistency property from `resolve_HasTypeA`).
    Requires only `AliasesResolved` (preserved across steps via context
    preservation), not the closure/freshness conditions `resolves_go_HasType_core`
    needs. -/
private theorem resolves_go_HasTypeA_core (C : LContext CoreLParams)
    (es : List (LExpr CoreLParams.mono)) :
    ∀ (Env Env' : TEnv Unit) (acc ets : List (LExprT CoreLParams.mono)),
      LExpr.resolves.go C Env es acc = .ok (ets, Env') →
      TEnvWF (T := CoreLParams) Env →
      FactoryWF C.functions →
      Env.context.types ≠ [] →
      TContext.AliasesResolved Env.context →
      ∃ (res : List (LExprT CoreLParams.mono)) (h_rlen : res.length = es.length),
        ets = acc.reverse ++ res ∧
        (∀ i (hi : i < es.length),
          LExpr.HasTypeA [] ((res.get ⟨i, h_rlen ▸ hi⟩).unresolved)
            ((res.get ⟨i, h_rlen ▸ hi⟩).toLMonoTy)) := by
  induction es with
  | nil =>
    intro Env Env' acc ets h _ _ _ _
    simp only [LExpr.resolves.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    refine ⟨[], rfl, by simp, ?_⟩
    intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons e erest ih =>
    intro Env Env' acc ets h h_wf h_fwf h_ne h_resolved
    simp only [LExpr.resolves.go, Bind.bind, Except.bind] at h
    elim_err h with v_step h_step
    obtain ⟨et, Env_mid⟩ := v_step
    have h_ctx_mid : Env_mid.context = Env.context :=
      resolve_preserves_context e et C Env Env_mid h_step h_wf h_ne h_fwf
    have h_wf_mid : TEnvWF (T := CoreLParams) Env_mid :=
      resolve_TEnvWF e et C Env Env_mid h_step h_wf h_fwf
    have h_ne_mid : Env_mid.context.types ≠ [] := by rw [h_ctx_mid]; exact h_ne
    have h_resolved_mid : TContext.AliasesResolved Env_mid.context := by
      rw [h_ctx_mid]; exact h_resolved
    have h_hta_e : LExpr.HasTypeA [] et.unresolved et.toLMonoTy :=
      resolve_HasTypeA e et C Env Env_mid h_step h_wf h_fwf h_resolved
    obtain ⟨res', h_rlen', h_ets', h_typ'⟩ :=
      ih Env_mid Env' (et :: acc) ets h h_wf_mid h_fwf h_ne_mid h_resolved_mid
    refine ⟨et :: res', ?_, ?_, ?_⟩
    · simp only [List.length_cons, h_rlen']
    · simp only [List.reverse_cons] at h_ets'; simpa using h_ets'
    · intro i hi
      match i with
      | 0 =>
        simpa only [List.get_eq_getElem, List.getElem_cons_zero] using h_hta_e
      | k + 1 =>
        have h_k : k < erest.length := by
          simp only [List.length_cons] at hi; omega
        have h_ty := h_typ' k h_k
        simpa only [List.get_eq_getElem, List.getElem_cons_succ] using h_ty

/-- If `resolves` succeeds, each resolved element satisfies `HasTypeA` between its
    erased form and its monotype. Wrapper over `resolves_go_HasTypeA_core`. -/
theorem resolves_HasTypeA (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List (LExpr CoreLParams.mono)) (ets : List (LExprT CoreLParams.mono))
    (h : LExpr.resolves C Env es = .ok (ets, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_len : ets.length = es.length) :
    ∀ i (hi : i < es.length),
      LExpr.HasTypeA [] ((ets.get ⟨i, h_len ▸ hi⟩).unresolved)
        ((ets.get ⟨i, h_len ▸ hi⟩).toLMonoTy) := by
  unfold LExpr.resolves at h
  obtain ⟨res, h_rlen, h_ets, h_typ⟩ :=
    resolves_go_HasTypeA_core C es Env Env' [] ets h h_wf h_fwf h_ne h_resolved
  simp only [List.reverse_nil, List.nil_append] at h_ets
  subst h_ets
  intro i hi
  simp only [List.get_eq_getElem]
  exact h_typ i hi

/-- Resolving a free variable `fvar m x fty` yields an `LExprT` free variable with
    the *same name* `x` (only its metadata/type are recomputed). -/
private theorem resolve_fvar_eq_fvar (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (m : Unit) (x : Identifier Unit) (fty : Option LMonoTy) (et : LExprT CoreLParams.mono)
    (h : (LExpr.fvar m x fty).resolve C Env = .ok (et, Env')) :
    ∃ m' ty', et = .fvar m' x ty' := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  elim_err h with v h_aux
  obtain ⟨et_aux, Env_r⟩ := v
  simp only [resolveAux, Bind.bind, Except.bind] at h_aux
  elim_err h_aux with v_if h_inf
  obtain ⟨ty, Env_inf⟩ := v_if
  simp only [Except.ok.injEq, Prod.mk.injEq] at h h_aux
  obtain ⟨h_et, _⟩ := h
  obtain ⟨h_etaux, _⟩ := h_aux
  rw [← h_et, ← h_etaux]
  simp only [applySubstT, replaceMetadata]
  exact ⟨_, _, rfl⟩

/-- Accumulator-generalized "resolves preserves fvar name" core for `resolves.go`.
    If the `i`-th input is a free variable `fvar m x fty`, the corresponding
    resolved element is a free variable with the *same name* `x`. -/
private theorem resolves_go_fvar_name_core (C : LContext CoreLParams)
    (es : List (LExpr CoreLParams.mono)) :
    ∀ (Env Env' : TEnv Unit) (acc ets : List (LExprT CoreLParams.mono)),
      LExpr.resolves.go C Env es acc = .ok (ets, Env') →
      TEnvWF (T := CoreLParams) Env →
      FactoryWF C.functions →
      Env.context.types ≠ [] →
      ∃ (res : List (LExprT CoreLParams.mono)) (h_rlen : res.length = es.length),
        ets = acc.reverse ++ res ∧
        (∀ i (hi : i < es.length) m x fty,
          es.get ⟨i, hi⟩ = .fvar m x fty →
          ∃ m' ty', res.get ⟨i, h_rlen ▸ hi⟩ = .fvar m' x ty') := by
  induction es with
  | nil =>
    intro Env Env' acc ets h _ _ _
    simp only [LExpr.resolves.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    refine ⟨[], rfl, by simp, ?_⟩
    intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons e erest ih =>
    intro Env Env' acc ets h h_wf h_fwf h_ne
    simp only [LExpr.resolves.go, Bind.bind, Except.bind] at h
    elim_err h with v_step h_step
    obtain ⟨et, Env_mid⟩ := v_step
    have h_ctx_mid : Env_mid.context = Env.context :=
      resolve_preserves_context e et C Env Env_mid h_step h_wf h_ne h_fwf
    have h_wf_mid : TEnvWF (T := CoreLParams) Env_mid :=
      resolve_TEnvWF e et C Env Env_mid h_step h_wf h_fwf
    have h_ne_mid : Env_mid.context.types ≠ [] := by rw [h_ctx_mid]; exact h_ne
    obtain ⟨res', h_rlen', h_ets', h_fvar'⟩ :=
      ih Env_mid Env' (et :: acc) ets h h_wf_mid h_fwf h_ne_mid
    refine ⟨et :: res', ?_, ?_, ?_⟩
    · simp only [List.length_cons, h_rlen']
    · simp only [List.reverse_cons] at h_ets'; simpa using h_ets'
    · intro i hi m x fty h_node
      match i with
      | 0 =>
        simp only [List.get_eq_getElem, List.getElem_cons_zero] at h_node ⊢
        exact resolve_fvar_eq_fvar C Env Env_mid m x fty et (h_node ▸ h_step)
      | k + 1 =>
        have h_k : k < erest.length := by
          simp only [List.length_cons] at hi; omega
        simp only [List.get_eq_getElem, List.getElem_cons_succ] at h_node ⊢
        exact h_fvar' k h_k m x fty (by simp only [List.get_eq_getElem]; exact h_node)

/-- If `resolves` succeeds and the `i`-th input is a free variable `fvar m x fty`,
    then the `i`-th resolved element is a free variable with the same name `x`.
    Wrapper over `resolves_go_fvar_name_core`. -/
theorem resolves_fvar_name (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List (LExpr CoreLParams.mono)) (ets : List (LExprT CoreLParams.mono))
    (h : LExpr.resolves C Env es = .ok (ets, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_len : ets.length = es.length) :
    ∀ i (hi : i < es.length) m x fty,
      es.get ⟨i, hi⟩ = .fvar m x fty →
      ∃ m' ty', ets.get ⟨i, h_len ▸ hi⟩ = .fvar m' x ty' := by
  unfold LExpr.resolves at h
  obtain ⟨res, h_rlen, h_ets, h_fvar⟩ :=
    resolves_go_fvar_name_core C es Env Env' [] ets h h_wf h_fwf h_ne
  simp only [List.reverse_nil, List.nil_append] at h_ets
  subst h_ets
  intro i hi m x fty h_node
  simp only [List.get_eq_getElem]
  have := h_fvar i hi m x fty h_node
  simpa only [List.get_eq_getElem] using this

/-- For each bare input free variable (`fvar m x none`, the form emitted for inout
    call arguments), the resolved monotype is alias-equivalent to the monomorphic
    context type of `x`, under any substitution absorbing `Env'`'s substitution.
    Wrapper over `resolves_go_fvar_aliasEquiv_core`. -/
theorem resolves_fvar_aliasEquiv (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List (LExpr CoreLParams.mono)) (ets : List (LExprT CoreLParams.mono))
    (h : LExpr.resolves C Env es = .ok (ets, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_ws : ∀ e, e ∈ es → WellScoped e Env.context)
    (h_len : ets.length = es.length) :
    ∀ i (hi : i < es.length) m x,
      es.get ⟨i, hi⟩ = .fvar m x none →
      ∃ mty_ctx, Env.context.types.find? x = some (.forAll [] mty_ctx) ∧
        ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst →
          AliasEquiv Env.context.aliases (LMonoTy.subst S mty_ctx)
            (LMonoTy.subst S ((ets.get ⟨i, h_len ▸ hi⟩).toLMonoTy)) := by
  unfold LExpr.resolves at h
  obtain ⟨res, h_rlen, h_ets, h_ae⟩ :=
    resolves_go_fvar_aliasEquiv_core C es Env Env' [] ets h h_wf h_fwf h_ne h_mono h_ws
  simp only [List.reverse_nil, List.nil_append] at h_ets
  subst h_ets
  intro i hi m x h_fvar
  simp only [List.get_eq_getElem]
  exact h_ae i hi m x h_fvar

/-! ### Shared facts for the call obligations

All three `CmdExtHasType'.call` obligations (input typing, lhs/output typing,
and inout-arg validity) — in both the unannotated and annotated proofs — depend
on the same bundle of index-independent facts derived from the successful
typechecking steps. `CallFacts` packages them and `callFacts` derives them once,
so each obligation can read off `F.field` instead of re-deriving the preamble. -/

/-- Bundled, index-independent facts shared by every `.call` typing obligation,
    derived from the five successful intermediate steps (lhs instantiation, input
    signature instantiation, free-var checks, input resolution, and unification).
    `Env_lhs` is the environment after lhs instantiation; `v2`/`v3`/`v4` are the
    results of input-signature instantiation, input resolution, and unification. -/
structure CallFacts (C : LContext CoreLParams) (Env Env_lhs : TEnv Unit)
    (proc : Procedure) (callArgs : List (CallArg Expression)) (v1 : List LMonoTy)
    (v2 : (@LMonoTySignature Unit) × TEnv Unit × Subst)
    (v3 : List (LExprT CoreLParams.mono) × TEnv Unit) (v4 : SubstInfo) : Prop where
  inst_lhs_raw : Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
    = .ok (some (v1, Env_lhs))
  inst_inp_raw : LMonoTySignature.instantiateWithSubst C Env_lhs
    proc.header.typeArgs proc.header.inputs = .ok v2
  resolves_raw : LExpr.resolves C v2.2.fst (CallArg.getInputExprs callArgs) = .ok v3
  unify : Constraints.unify
      ((List.map toLMonoTy v3.fst).zip
        (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
        v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
          (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
      v3.snd.stateSubstInfo = .ok v4
  ctx_eq : v2.2.fst.context = Env.context
  ctx_lhs_env : Env_lhs.context = Env.context
  ctx_v2_lhs : v2.2.fst.context = Env_lhs.context
  subst_v2_env : v2.2.fst.stateSubstInfo.subst = Env.stateSubstInfo.subst
  wf_lhs : TEnvWF (T := CoreLParams) Env_lhs
  wf_v2 : TEnvWF (T := CoreLParams) v2.2.fst
  aliases_wf_lhs : TContext.AliasesWF Env_lhs.context
  ws : ∀ e, e ∈ (CallArg.getInputExprs callArgs) → WellScoped e v2.2.fst.context
  len : v3.fst.length = (CallArg.getInputExprs callArgs).length
  ne_v2 : v2.2.fst.context.types ≠ []
  absorbs_v2 : Subst.absorbs v4.subst v2.2.fst.stateSubstInfo.subst

/-- Derive the shared `CallFacts` bundle from the five raw (`mapError`-stripped)
    step equations together with the ambient well-formedness hypotheses. -/
theorem callFacts (C : LContext CoreLParams) (Env Env_lhs : TEnv Unit)
    (proc : Procedure) (callArgs : List (CallArg Expression)) (v1 : List LMonoTy)
    (v2 : (@LMonoTySignature Unit) × TEnv Unit × Subst)
    (v3 : List (LExprT CoreLParams.mono) × TEnv Unit) (v4 : SubstInfo)
    (h_inst_lhs_raw : Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
      = .ok (some (v1, Env_lhs)))
    (h_inst_inp_raw : LMonoTySignature.instantiateWithSubst C Env_lhs
      proc.header.typeArgs proc.header.inputs = .ok v2)
    (h_fvc_raw : Env_lhs.freeVarChecks (CallArg.getInputExprs callArgs) = .ok ())
    (h_resolves_raw : LExpr.resolves C v2.2.fst (CallArg.getInputExprs callArgs) = .ok v3)
    (h_unify : Constraints.unify
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
        v3.snd.stateSubstInfo = .ok v4)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    CallFacts C Env Env_lhs proc callArgs v1 v2 v3 v4 := by
  have h_ctx_v2_lhs : v2.2.fst.context = Env_lhs.context :=
    instantiateWithSubst_preserves_context C Env_lhs proc.header.typeArgs
      proc.header.inputs v2 h_inst_inp_raw
  have h_ctx_lhs_env : Env_lhs.context = Env.context :=
    instantiateAndSubsts_preserves_context (CallArg.getLhs callArgs) C Env v1 Env_lhs
      h_inst_lhs_raw
  have h_ctx_eq : v2.2.fst.context = Env.context := by rw [h_ctx_v2_lhs, h_ctx_lhs_env]
  have h_subst_lhs_env : Env_lhs.stateSubstInfo = Env.stateSubstInfo :=
    instantiateAndSubsts_preserves_stateSubstInfo (CallArg.getLhs callArgs) C Env v1
      Env_lhs h_inst_lhs_raw
  have h_subst_v2_lhs : v2.2.fst.stateSubstInfo = Env_lhs.stateSubstInfo :=
    instantiateWithSubst_preserves_stateSubstInfo C Env_lhs proc.header.typeArgs
      proc.header.inputs v2 h_inst_inp_raw
  have h_subst_v2_env : v2.2.fst.stateSubstInfo.subst = Env.stateSubstInfo.subst := by
    rw [h_subst_v2_lhs, h_subst_lhs_env]
  have h_wf_lhs : TEnvWF (T := CoreLParams) Env_lhs :=
    instantiateAndSubsts_preserves_wf (CallArg.getLhs callArgs) C Env v1 Env_lhs
      h_inst_lhs_raw h_wf
  have h_wf_v2 : TEnvWF (T := CoreLParams) v2.2.fst :=
    instantiateWithSubst_preserves_wf C Env_lhs proc.header.typeArgs
      proc.header.inputs v2 h_inst_inp_raw h_wf_lhs
  have h_ws : ∀ e, e ∈ (CallArg.getInputExprs callArgs) → WellScoped e v2.2.fst.context := by
    rw [h_ctx_v2_lhs]
    exact freeVarChecks_implies_WellScoped Env_lhs (CallArg.getInputExprs callArgs) h_fvc_raw
  have h_len : v3.fst.length = (CallArg.getInputExprs callArgs).length :=
    resolves_preserves_length C v2.2.fst v3.snd (CallArg.getInputExprs callArgs) v3.fst
      h_resolves_raw
  have h_ne_v2 : v2.2.fst.context.types ≠ [] := h_ctx_eq ▸ h_ne
  have h_res_sound := resolves_HasType_core C v2.2.fst v3.snd
    (CallArg.getInputExprs callArgs) v3.fst h_resolves_raw h_wf_v2 h_fwf h_ne_v2 h_ws h_len
  have h_absorbs : Subst.absorbs v4.subst v3.snd.stateSubstInfo.subst :=
    Constraints.unify_absorbs _ _ _ h_unify
  have h_absorbs_v2 : Subst.absorbs v4.subst v2.2.fst.stateSubstInfo.subst :=
    Subst.absorbs_trans v2.2.fst.stateSubstInfo.subst v3.snd.stateSubstInfo.subst v4.subst
      h_res_sound.2.2.1 h_absorbs
  have h_aliases_wf_lhs : TContext.AliasesWF Env_lhs.context := h_ctx_lhs_env ▸ h_wf.aliasesWF
  exact {
    inst_lhs_raw := h_inst_lhs_raw
    inst_inp_raw := h_inst_inp_raw
    resolves_raw := h_resolves_raw
    unify := h_unify
    ctx_eq := h_ctx_eq
    ctx_lhs_env := h_ctx_lhs_env
    ctx_v2_lhs := h_ctx_v2_lhs
    subst_v2_env := h_subst_v2_env
    wf_lhs := h_wf_lhs
    wf_v2 := h_wf_v2
    aliases_wf_lhs := h_aliases_wf_lhs
    ws := h_ws
    len := h_len
    ne_v2 := h_ne_v2
    absorbs_v2 := h_absorbs_v2
  }

/-! ### Context preservation for call typechecking -/

/-- The call branch of `typeCheckCmd` preserves the context. -/
theorem typeCheckCmd_call_preserves_context (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (pname : String) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P (.call pname callArgs md) = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    Env'.context = Env.context := by
  unfold Statement.typeCheckCmd at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch] at h; contradiction
  · rename_i proc heq_find
    simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch,
               MonadExceptOf.tryCatch, Except.tryCatch] at h
    elim_err h with h_inner h_eq
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
    subst h2; clear h
    -- Eliminate the 4 if-checks.
    elim_err h_eq with h_lhs_exist
    elim_err h_eq with h_out_arity
    elim_err h_eq with h_inp_arity
    elim_err h_eq with h_inout_check
    elim_err h_eq with h_inout_valid
    elim_err h_eq with v1 h_inst_lhs
    elim_err h_eq with lhs_tys Env1
    elim_err h_eq with v2 h_fvc
    elim_err h_eq with v3 h_inst_inputs
    elim_err h_eq with v4 h_resolves
    cases h_eq
    -- Raw (mapError-stripped) step equations.
    have h_unify : Constraints.unify
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
        v3.snd.stateSubstInfo = .ok v4 := by
      revert h_resolves; simp only [Except.mapError]; split <;> simp_all
    have h_resolves_raw : LExpr.resolves C v2.2.fst
        (CallArg.getInputExprs callArgs) = .ok v3 := by
      revert h_inst_inputs; simp only [Except.mapError]; split <;> simp_all
    have h_inst_lhs_raw : Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
        = .ok (some (v1, h_inst_lhs)) := by
      revert h_inout_valid; simp only [Except.mapError]; split <;> simp_all
    have h_inst_inp_raw : LMonoTySignature.instantiateWithSubst C h_inst_lhs
        proc.header.typeArgs proc.header.inputs = .ok v2 := by
      revert h_fvc; simp only [Except.mapError]; split <;> simp_all
    have h_fvc_raw : h_inst_lhs.freeVarChecks (CallArg.getInputExprs callArgs) = .ok () := by
      revert Env1; simp only [Except.mapError]; split <;> simp_all
    -- The shared, index-independent fact bundle.
    have F := callFacts C Env h_inst_lhs proc callArgs v1 v2 v3 v4
      h_inst_lhs_raw h_inst_inp_raw h_fvc_raw h_resolves_raw h_unify h_wf h_fwf h_ne
    -- Context preservation through resolves: v3.snd.context = v2.2.fst.context = Env.context.
    have h_res_sound := resolves_HasType_core C v2.2.fst v3.snd
      (CallArg.getInputExprs callArgs) v3.fst F.resolves_raw F.wf_v2 h_fwf F.ne_v2 F.ws F.len
    show (v3.snd.updateSubst v4).context = Env.context
    rw [show (v3.snd.updateSubst v4).context = v3.snd.context from rfl,
      h_res_sound.2.1, F.ctx_eq]

/-! ### Call case auxiliary -/

/-- Core lemma for the `.call` case: if `typeCheckCmd` succeeds on a call,
    then there exists a procedure and a typing derivation. -/
theorem typeCheckCmd_call_sound_aux (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (pname : String) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P (.call pname callArgs md) = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_closed : ∀ proc,
      Program.Procedure.find? P ⟨pname, ()⟩ = some proc →
      ProcHeaderClosed proc) :
    ∃ proc, Program.Procedure.find? P ⟨pname, ()⟩ = some proc ∧
      CmdExtHasType C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
        (.call pname callArgs md)
        (TContext.subst Env.context Env'.stateSubstInfo.subst) := by
  unfold Statement.typeCheckCmd at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch] at h; contradiction
  · rename_i proc heq_find
    simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch,
               MonadExceptOf.tryCatch, Except.tryCatch] at h
    -- inner computation succeeded
    elim_err h with h_inner h_eq
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
    subst h1; subst h2; clear h
    refine ⟨proc, heq_find, ?_⟩
    -- Eliminate the 4 if-checks
    elim_err h_eq with h_lhs_exist
    elim_err h_eq with h_out_arity
    elim_err h_eq with h_inp_arity
    elim_err h_eq with h_inout_check
    elim_err h_eq with h_inout_valid
    -- Now h_eq is the match chain = .ok h_inner
    elim_err h_eq with v1 h_inst_lhs
    elim_err h_eq with lhs_tys Env1
    elim_err h_eq with v2 h_fvc
    elim_err h_eq with v3 h_inst_inputs
    elim_err h_eq with v4 h_resolves
    cases h_eq
    show CmdExtHasType C P (Env.context.subst (v3.snd.updateSubst v4).stateSubstInfo.subst)
      (.call pname callArgs md) (Env.context.subst (v3.snd.updateSubst v4).stateSubstInfo.subst)
    let S_final := (v3.snd.updateSubst v4).stateSubstInfo.subst
    let tyArgSubst : Subst := v2.2.snd
    let σ : List (TyIdentifier × LMonoTy) :=
      List.zip proc.header.typeArgs
        (proc.header.typeArgs.map (fun a => LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))))
    -- Raw (mapError-stripped) step equations, derived once.
    have h_unify : Constraints.unify
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
        v3.snd.stateSubstInfo = .ok v4 := by
      revert h_resolves; simp only [Except.mapError]; split <;> simp_all
    have h_resolves_raw : LExpr.resolves C v2.2.fst
        (CallArg.getInputExprs callArgs) = .ok v3 := by
      revert h_inst_inputs; simp only [Except.mapError]; split <;> simp_all
    have h_inst_lhs_raw : Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
        = .ok (some (v1, h_inst_lhs)) := by
      revert h_inout_valid; simp only [Except.mapError]; split <;> simp_all
    have h_inst_inp_raw : LMonoTySignature.instantiateWithSubst C h_inst_lhs
        proc.header.typeArgs proc.header.inputs = .ok v2 := by
      revert h_fvc; simp only [Except.mapError]; split <;> simp_all
    have h_fvc_raw : h_inst_lhs.freeVarChecks (CallArg.getInputExprs callArgs) = .ok () := by
      revert Env1; simp only [Except.mapError]; split <;> simp_all
    -- The shared, index-independent fact bundle for all call obligations.
    have F := callFacts C Env h_inst_lhs proc callArgs v1 v2 v3 v4
      h_inst_lhs_raw h_inst_inp_raw h_fvc_raw h_resolves_raw h_unify h_wf h_fwf h_ne
    apply CmdExtHasType'.call (Γ := Env.context.subst S_final) (σ := σ) (proc := proc)
    · exact heq_find
    · -- input arity
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_inp_arity
      exact h_inp_arity
    · -- output arity
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_out_arity
      exact h_out_arity
    · -- lhs vars exist in substituted context
      intro v hv
      have h_not_none : ¬(Env.context.types.find? v).isNone = true := by
        intro h_none
        exact h_lhs_exist (List.any_eq_true.mpr ⟨v, hv, h_none⟩)
      cases h_opt : Env.context.types.find? v with
      | none => simp [h_opt] at h_not_none
      | some ty =>
        simp only [Option.isSome_iff_exists]
        exact ⟨_, TContext.subst_find_some Env.context S_final v ty h_opt⟩
    · -- HasType for inputs
      intro i hi hj
      have h_absorbs_final : Subst.absorbs S_final v3.snd.stateSubstInfo.subst :=
        Constraints.unify_absorbs _ _ _ F.unify
      have h_res_sound := resolves_HasType_core C v2.2.fst v3.snd
        (CallArg.getInputExprs callArgs) v3.fst F.resolves_raw F.wf_v2 h_fwf F.ne_v2 F.ws F.len
      have h_pkf : Subst.polyKeysFresh (T := CoreLParams) S_final v2.2.fst.context :=
        Subst.polyKeysFresh_of_mono S_final v2.2.fst.context (F.ctx_eq ▸ h_mono)
      have h_resolves_typing := h_res_sound.2.2.2 i hi S_final h_absorbs_final v4.isWF h_pkf
      have h_alias_equiv := call_input_type_eq C h_inst_lhs proc callArgs v1 v2 v3 v4 i hi hj F.len
          F.inst_inp_raw F.unify (h_closed proc heq_find) F.aliases_wf_lhs F.absorbs_v2
      rw [F.ctx_eq] at h_resolves_typing
      simp only [List.get_eq_getElem] at h_resolves_typing h_alias_equiv
      -- The shared `∃ mty` witness must satisfy BOTH the AliasEquiv conjunct and
      -- the node-dependent second conjunct. For a bare inout fvar the second
      -- conjunct (`find? x = some (forAll [] mty)`) forces `mty` to be the
      -- (substituted) context type; for any other node it forces the resolved
      -- type. The two are alias-equivalent but not equal, so we split on the node
      -- first and pick the branch's forced witness.
      by_cases h_is_inout : ∃ m x, (CallArg.getInputExprs callArgs)[i] = .fvar m x none
      · -- Inout argument: witness is the (substituted) context type of `x`.
        obtain ⟨m, x, h_node⟩ := h_is_inout
        have h_node' : (CallArg.getInputExprs callArgs).get ⟨i, hi⟩ = .fvar m x none := by
          simp only [List.get_eq_getElem]; exact h_node
        obtain ⟨mty_ctx, h_find_ctx, h_ae_ctx⟩ :=
          resolves_fvar_aliasEquiv C v2.2.fst v3.snd (CallArg.getInputExprs callArgs) v3.fst
            F.resolves_raw F.wf_v2 h_fwf F.ne_v2 (F.ctx_eq ▸ h_mono) F.ws F.len i hi m x h_node'
        rw [h_node]
        refine ⟨LMonoTy.subst S_final mty_ctx, ?_, ?_⟩
        · -- AliasEquiv via trans(Layer-3 @ S_final, call_input_type_eq).
          rw [TContext.subst_aliases, ← F.ctx_lhs_env]
          have h_ae_S := h_ae_ctx S_final h_absorbs_final
          simp only [List.get_eq_getElem] at h_ae_S
          rw [F.ctx_eq, ← F.ctx_lhs_env] at h_ae_S
          exact AliasEquiv.trans h_ae_S h_alias_equiv
        · -- find? side: lift the context lookup through `TContext.subst`.
          have h_find_env : Env.context.types.find? x = some (.forAll [] mty_ctx) :=
            F.ctx_eq ▸ h_find_ctx
          have h_find_subst := TContext.subst_find_some Env.context S_final x
            (.forAll [] mty_ctx) h_find_env
          rw [LTy.subst_forAll_nil] at h_find_subst
          exact h_find_subst
      · -- Any other node: witness is the resolved/substituted input type.
        refine ⟨LMonoTy.subst S_final ((v3.fst[i]'(F.len ▸ hi)).toLMonoTy), ?_, ?_⟩
        · rw [TContext.subst_aliases, ← F.ctx_lhs_env]
          exact h_alias_equiv
        · split
          · rename_i m x h_eq
            exact absurd ⟨m, x, h_eq⟩ h_is_inout
          · exact h_resolves_typing
    · -- lhs types match outputs
      intro i hi hj
      rw [TContext.subst_aliases]
      exact call_output_type_eq C Env h_inst_lhs proc callArgs v1 v2 v3 v4 i hi hj
        h_mono F.inst_lhs_raw F.unify (h_closed proc heq_find)
        h_wf.aliasesWF F.subst_v2_env F.absorbs_v2
    · -- inout args are simple vars
      intro i hi h_contains
      have h_inout_raw : Statement.areInoutArgsValid proc (CallArg.getInputExprs callArgs) = true := by
        revert h_inout_check
        cases Statement.areInoutArgsValid proc (CallArg.getInputExprs callArgs) <;> simp
      have h_arity : (CallArg.getInputExprs callArgs).length
          = (ListMap.keys proc.header.inputs).length := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_inp_arity
        rw [h_inp_arity, ListMap.keys.length]
      exact areInoutArgsValid_implies_fvar proc (CallArg.getInputExprs callArgs)
        h_inout_raw i hi h_contains h_arity

/-! ### Part I — Unannotated soundness -/

/--
Soundness of the command typechecker for `Command` (CmdExt):
if `typeCheckCmd` succeeds, then `CmdExtHasType` holds between the
substituted input and output contexts.
-/
theorem Command.typeCheckCmd_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (cmd cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : ∀ proc pname callArgs md,
      cmd = .call pname callArgs md →
      Program.Procedure.find? P pname = some proc →
      ProcHeaderClosed proc) :
    CmdExtHasType C P (TContext.subst Env.context Env'.stateSubstInfo.subst) cmd
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | cmd c =>
    unfold Statement.typeCheckCmd at h
    simp only [Bind.bind, Except.bind] at h
    elim_err h with v h_tc
    obtain ⟨c', Env'_inner⟩ := v
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_cmd_eq, h_env_eq⟩ := h
    subst h_cmd_eq; subst h_env_eq
    have h_sound := Cmd.typeCheck_sound C Env c c' Env'_inner h_tc
      h_wf h_fwf h_ne h_mono h_rigid_inv
    exact CmdExtHasType'.cmd _ _ c h_sound
  | call pname callArgs md =>
    have h_ctx := typeCheckCmd_call_preserves_context C Env P pname callArgs md cmd' Env' h
      h_wf h_fwf h_ne
    rw [h_ctx]
    have h_closed' := h_closed
    simp only [CmdExt.call.injEq] at h_closed'
    -- Extract proc from the successful typechecking
    have ⟨proc, h_find, h_call_sound⟩ :=
      typeCheckCmd_call_sound_aux C Env P pname callArgs md cmd' Env' h h_wf h_fwf h_ne h_mono
        (fun proc h_find => h_closed' proc pname callArgs md ⟨rfl, rfl, rfl⟩ h_find)
    exact h_call_sound

/-! ### Annotated case helpers -/

/-- `Command.subst S (.cmd c')` satisfies `CmdExtHasTypeA` when
    `Cmd.subst S c'` satisfies `CmdHasTypeA`.
    Trivial since `Command.subst S (.cmd c') = .cmd (Cmd.subst S c')` by definition. -/
theorem Command_subst_cmd_HasTypeA (C : LContext CoreLParams) (P : Program)
    (Env : TEnv Unit) (Env' : TEnv Unit) (c' : Cmd Expression)
    (h_sound : CmdHasTypeA C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Core.Statement.Cmd.subst Env'.stateSubstInfo.subst c')
      (TContext.subst Env'.context Env'.stateSubstInfo.subst)) :
    CmdExtHasTypeA C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Statement.Command.subst Env'.stateSubstInfo.subst (.cmd c'))
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  exact CmdExtHasType'.cmd _ _ _ h_sound

/-! ### Structural bridges for the annotated (transformed) command

The annotated `.call` obligations are stated about the *transformed* argument
list `(replaceInArgs callArgs es).map substCallArgFn` (where `es` are the
unresolved, resolved expressions and `substCallArgFn` is the per-arg map inside
`Command.subst`). Both `replaceInArgs` and `substCallArgFn` preserve the *kind*
of every argument (`inArg`/`inoutArg`/`outArg`) — only `inArg` payloads change —
so `getLhs` (which collects `inoutArg`/`outArg` ids) is invariant under both. -/

/-- The per-argument map applied inside `Command.subst` for the `.call` case. -/
private def substCallArgFn (S : Subst) : CallArg Expression → CallArg Expression
  | .inArg e => .inArg (e.applySubst S)
  | .inoutArg id => .inoutArg id
  | .outArg id => .outArg id

/-- `Command.subst` on a `.call` rewrites every argument by `substCallArgFn`.
    Stating it this way (rather than unfolding into the anonymous `match`
    lambda) lets the structural bridge lemmas fire with plain `rw`. -/
private theorem Command_subst_call (S : Subst) (pname : String)
    (args : List (CallArg Expression)) (md : MetaData Expression) :
    Statement.Command.subst S (.call pname args md)
      = .call pname (args.map (substCallArgFn S)) md := by
  simp only [Statement.Command.subst]
  congr 1

/-- `getLhs` is invariant under the per-argument `Command.subst` map. -/
private theorem getLhs_map_substCallArgFn (args : List (CallArg Expression)) (S : Subst) :
    CallArg.getLhs (args.map (substCallArgFn S)) = CallArg.getLhs args := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    unfold CallArg.getLhs at ih ⊢
    cases a <;>
      simp only [List.map_cons, substCallArgFn, List.filterMap_cons, ih]

/-- `getLhs` is invariant under `replaceInArgs` (it only rewrites `inArg`
    payloads, never `inoutArg`/`outArg` ids). -/
private theorem getLhs_replaceInArgs (args : List (CallArg Expression))
    (es : List Expression.Expr) :
    CallArg.getLhs (CallArg.replaceInArgs args es) = CallArg.getLhs args := by
  simp only [CallArg.replaceInArgs]
  suffices h : ∀ es, CallArg.getLhs (CallArg.replaceInArgs.go args es) = CallArg.getLhs args
    from h es
  induction args with
  | nil => intro es; rfl
  | cons a rest ih =>
    intro es
    unfold CallArg.getLhs at ih ⊢
    match a, es with
    | .inArg _, e :: es => simp only [CallArg.replaceInArgs.go, List.filterMap_cons, ih]
    | .inArg _, [] => simp only [CallArg.replaceInArgs.go, List.filterMap_cons, ih]
    | .inoutArg id, e :: es => simp only [CallArg.replaceInArgs.go, List.filterMap_cons, ih]
    | .inoutArg id, [] => simp only [CallArg.replaceInArgs.go, List.filterMap_cons, ih]
    | .outArg id, es => simp only [CallArg.replaceInArgs.go, List.filterMap_cons, ih]

/-- Combined: `getLhs` of the transformed argument list equals `getLhs` of the
    original. -/
private theorem getLhs_transformed (callArgs : List (CallArg Expression))
    (es : List Expression.Expr) (S : Subst) :
    CallArg.getLhs ((CallArg.replaceInArgs callArgs es).map (substCallArgFn S))
      = CallArg.getLhs callArgs := by
  rw [getLhs_map_substCallArgFn, getLhs_replaceInArgs]

/-- `getInputExprs` length is invariant under the per-argument `Command.subst`
    map (it preserves each argument's kind, so the same positions are emitted). -/
private theorem getInputExprs_map_substCallArgFn_length (args : List (CallArg Expression))
    (S : Subst) :
    (CallArg.getInputExprs (args.map (substCallArgFn S))).length
      = (CallArg.getInputExprs args).length := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    unfold CallArg.getInputExprs at ih ⊢
    cases a <;>
      simp only [List.map_cons, substCallArgFn, List.filterMap_cons, List.length_cons, ih]

/-- `getInputExprs` length is invariant under `replaceInArgs` (it preserves each
    argument's kind: `inArg`↦`inArg`, `inoutArg`↦`inoutArg`, `outArg`↦`outArg`). -/
private theorem getInputExprs_replaceInArgs_length (args : List (CallArg Expression))
    (es : List Expression.Expr) :
    (CallArg.getInputExprs (CallArg.replaceInArgs args es)).length
      = (CallArg.getInputExprs args).length := by
  simp only [CallArg.replaceInArgs]
  suffices h : ∀ es, (CallArg.getInputExprs (CallArg.replaceInArgs.go args es)).length
      = (CallArg.getInputExprs args).length from h es
  induction args with
  | nil => intro es; rfl
  | cons a rest ih =>
    intro es
    unfold CallArg.getInputExprs at ih ⊢
    match a, es with
    | .inArg _, e :: es => simp only [CallArg.replaceInArgs.go, List.filterMap_cons,
        List.length_cons, ih]
    | .inArg _, [] => simp only [CallArg.replaceInArgs.go, List.filterMap_cons,
        List.length_cons, ih]
    | .inoutArg id, e :: es => simp only [CallArg.replaceInArgs.go, List.filterMap_cons,
        List.length_cons, ih]
    | .inoutArg id, [] => simp only [CallArg.replaceInArgs.go, List.filterMap_cons,
        List.length_cons, ih]
    | .outArg id, es => simp only [CallArg.replaceInArgs.go, List.filterMap_cons, ih]

/-- Combined: `getInputExprs` length of the transformed argument list equals that
    of the original. -/
private theorem getInputExprs_transformed_length (callArgs : List (CallArg Expression))
    (es : List Expression.Expr) (S : Subst) :
    (CallArg.getInputExprs ((CallArg.replaceInArgs callArgs es).map (substCallArgFn S))).length
      = (CallArg.getInputExprs callArgs).length := by
  rw [getInputExprs_map_substCallArgFn_length, getInputExprs_replaceInArgs_length]

/-- `getInputExprs` reduction lemmas (the `filterMap` match-lambda does not fire
    under `simp only`, so we expose the per-constructor equations explicitly). -/
private theorem getInputExprs_inArg (e : Expression.Expr) (rest : List (CallArg Expression)) :
    CallArg.getInputExprs (.inArg e :: rest) = e :: CallArg.getInputExprs rest := rfl

private theorem getInputExprs_inoutArg (id : Expression.Ident)
    (rest : List (CallArg Expression)) :
    CallArg.getInputExprs (.inoutArg id :: rest)
      = Lambda.LExpr.fvar () id none :: CallArg.getInputExprs rest := rfl

private theorem getInputExprs_outArg (id : Expression.Ident)
    (rest : List (CallArg Expression)) :
    CallArg.getInputExprs (.outArg id :: rest) = CallArg.getInputExprs rest := rfl

/-- Combined reduction of `getInputExprs ∘ map (substCallArgFn S) ∘ replaceInArgs.go`
    on each constructor. These hold by `rfl` (definitional unfolding of all three
    layers), and drive the per-element bridge induction below. -/
private theorem getInputExprs_tr_inArg (S : Subst) (e e0 : Expression.Expr)
    (rest : List (CallArg Expression)) (nes' : List Expression.Expr) :
    CallArg.getInputExprs ((CallArg.replaceInArgs.go (.inArg e :: rest) (e0 :: nes')).map
      (substCallArgFn S))
      = e0.applySubst S
        :: CallArg.getInputExprs ((CallArg.replaceInArgs.go rest nes').map (substCallArgFn S)) :=
  rfl

private theorem getInputExprs_tr_inoutArg (S : Subst) (id : Expression.Ident)
    (e0 : Expression.Expr) (rest : List (CallArg Expression)) (nes' : List Expression.Expr) :
    CallArg.getInputExprs ((CallArg.replaceInArgs.go (.inoutArg id :: rest) (e0 :: nes')).map
      (substCallArgFn S))
      = Lambda.LExpr.fvar () id none
        :: CallArg.getInputExprs ((CallArg.replaceInArgs.go rest nes').map (substCallArgFn S)) :=
  rfl

private theorem getInputExprs_tr_outArg (S : Subst) (id : Expression.Ident)
    (rest : List (CallArg Expression)) (nes : List Expression.Expr) :
    CallArg.getInputExprs ((CallArg.replaceInArgs.go (.outArg id :: rest) nes).map
      (substCallArgFn S))
      = CallArg.getInputExprs ((CallArg.replaceInArgs.go rest nes).map (substCallArgFn S)) :=
  rfl

/-- Per-element characterization of the transformed input nodes (`.go` form).
    At each position `i`, the transformed `getInputExprs` node is **either** the
    substituted, re-annotated by-value node `(nes[i]).applySubst S` (which is never
    a bare `fvar _ _ none`), **or** a bare `fvar () x none` that is *identical* to
    the original `getInputExprs` node at `i` (the inout case). This is exactly the
    split the annotated input obligation needs. `nes` is the per-position newExpr
    list (length = original `getInputExprs` length), consumed in lockstep with the
    `getInputExprs` entries (one per `inArg`/`inoutArg`, none per `outArg`). -/
private theorem getInputExprs_go_transformed_node (callArgs : List (CallArg Expression))
    (nes : List Expression.Expr) (S : Subst)
    (h_len : nes.length = (CallArg.getInputExprs callArgs).length)
    (i : Nat)
    (hi : i < (CallArg.getInputExprs
        ((CallArg.replaceInArgs.go callArgs nes).map (substCallArgFn S))).length) :
    (∃ (hi_e : i < nes.length),
        (CallArg.getInputExprs
          ((CallArg.replaceInArgs.go callArgs nes).map (substCallArgFn S)))[i]
          = (nes[i]'hi_e).applySubst S)
    ∨ (∃ x, ∃ (hi_o : i < (CallArg.getInputExprs callArgs).length),
        (CallArg.getInputExprs
          ((CallArg.replaceInArgs.go callArgs nes).map (substCallArgFn S)))[i]
          = .fvar () x none
        ∧ (CallArg.getInputExprs callArgs)[i]'hi_o = .fvar () x none) := by
  induction callArgs generalizing nes i with
  | nil =>
    simp only [CallArg.replaceInArgs.go, List.map_nil, CallArg.getInputExprs,
      List.filterMap_nil, List.length_nil] at hi
    exact absurd hi (Nat.not_lt_zero i)
  | cons a rest ih =>
    match a with
    | .inArg e =>
      cases nes with
      | nil =>
        exfalso
        rw [getInputExprs_inArg, List.length_cons, List.length_nil] at h_len
        omega
      | cons e0 nes' =>
        rw [getInputExprs_inArg, List.length_cons, List.length_cons] at h_len
        -- `transformed (inArg e :: rest)` defeq `e0.applySubst S :: transformed rest`.
        have h_tr_len : (CallArg.getInputExprs
            ((CallArg.replaceInArgs.go (.inArg e :: rest) (e0 :: nes')).map (substCallArgFn S))).length
            = (CallArg.getInputExprs
                ((CallArg.replaceInArgs.go rest nes').map (substCallArgFn S))).length + 1 := rfl
        match i with
        | 0 =>
          left
          exact ⟨by simp only [List.length_cons]; omega, rfl⟩
        | k + 1 =>
          have h_len' : nes'.length = (CallArg.getInputExprs rest).length := by omega
          have hi' : k < (CallArg.getInputExprs
              ((CallArg.replaceInArgs.go rest nes').map (substCallArgFn S))).length := by
            rw [h_tr_len] at hi; omega
          rcases ih nes' h_len' k hi' with ⟨hk, h_eq⟩ | ⟨x, hk, h_eq1, h_eq2⟩
          · left
            exact ⟨by simp only [List.length_cons]; omega, h_eq⟩
          · right
            refine ⟨x, ?_, h_eq1, h_eq2⟩
            rw [getInputExprs_inArg, List.length_cons]
            exact Nat.succ_lt_succ hk
    | .inoutArg id =>
      cases nes with
      | nil =>
        exfalso
        rw [getInputExprs_inoutArg, List.length_cons, List.length_nil] at h_len
        omega
      | cons e0 nes' =>
        rw [getInputExprs_inoutArg, List.length_cons, List.length_cons] at h_len
        have h_tr_len : (CallArg.getInputExprs
            ((CallArg.replaceInArgs.go (.inoutArg id :: rest) (e0 :: nes')).map (substCallArgFn S))).length
            = (CallArg.getInputExprs
                ((CallArg.replaceInArgs.go rest nes').map (substCallArgFn S))).length + 1 := rfl
        match i with
        | 0 =>
          right
          exact ⟨id, by rw [getInputExprs_inoutArg, List.length_cons]; omega, rfl, rfl⟩
        | k + 1 =>
          have h_len' : nes'.length = (CallArg.getInputExprs rest).length := by omega
          have hi' : k < (CallArg.getInputExprs
              ((CallArg.replaceInArgs.go rest nes').map (substCallArgFn S))).length := by
            rw [h_tr_len] at hi; omega
          rcases ih nes' h_len' k hi' with ⟨hk, h_eq⟩ | ⟨x, hk, h_eq1, h_eq2⟩
          · left
            exact ⟨by simp only [List.length_cons]; omega, h_eq⟩
          · right
            refine ⟨x, ?_, h_eq1, h_eq2⟩
            rw [getInputExprs_inoutArg, List.length_cons]
            exact Nat.succ_lt_succ hk
    | .outArg id =>
      rw [getInputExprs_outArg] at h_len
      -- `transformed (outArg id :: rest)` defeq `transformed rest`.
      have h_tr_len : (CallArg.getInputExprs
          ((CallArg.replaceInArgs.go (.outArg id :: rest) nes).map (substCallArgFn S))).length
          = (CallArg.getInputExprs
              ((CallArg.replaceInArgs.go rest nes).map (substCallArgFn S))).length := rfl
      have hi' : i < (CallArg.getInputExprs
          ((CallArg.replaceInArgs.go rest nes).map (substCallArgFn S))).length := by
        rw [h_tr_len] at hi; exact hi
      rcases ih nes h_len i hi' with ⟨hi_e, h_eq⟩ | ⟨x, hi_o, h_eq1, h_eq2⟩
      · left
        exact ⟨hi_e, h_eq⟩
      · right
        exact ⟨x, by rw [getInputExprs_outArg]; exact hi_o, h_eq1, h_eq2⟩

/-- `unresolved` always produces an annotated `fvar` (`some` type), and
    `applySubst` only rewrites the existing annotation, so a transformed by-value
    node is never the bare `fvar _ _ none` that the input obligation's `fvar`
    branch matches. -/
private theorem unresolved_applySubst_ne_fvar_none (et : LExprT CoreLParams.mono) (S : Subst) :
    ∀ m x, (LExpr.unresolved et).applySubst S ≠ .fvar m x none := by
  intro m x
  cases et <;> rw [LExpr.applySubst_eq_replaceUserProvidedType] <;>
    simp [LExpr.unresolved, LExpr.replaceUserProvidedType] <;>
    split <;> simp [LExpr.replaceUserProvidedType]

/-- Wrapper of `getInputExprs_go_transformed_node` specialized to the actual
    transformed input list `replaceInArgs callArgs (map unresolved ets)`. The
    by-value disjunct exposes the node as `(unresolved ets[i]).applySubst S`. -/
private theorem getInputExprs_transformed_node (callArgs : List (CallArg Expression))
    (ets : List (LExprT CoreLParams.mono)) (S : Subst)
    (h_len : ets.length = (CallArg.getInputExprs callArgs).length)
    (i : Nat)
    (hi : i < (CallArg.getInputExprs
        ((CallArg.replaceInArgs callArgs (List.map LExpr.unresolved ets)).map
          (substCallArgFn S))).length) :
    (∃ (hi_e : i < ets.length),
        (CallArg.getInputExprs
          ((CallArg.replaceInArgs callArgs (List.map LExpr.unresolved ets)).map
            (substCallArgFn S)))[i]
          = (LExpr.unresolved (ets[i]'hi_e)).applySubst S)
    ∨ (∃ x, ∃ (hi_o : i < (CallArg.getInputExprs callArgs).length),
        (CallArg.getInputExprs
          ((CallArg.replaceInArgs callArgs (List.map LExpr.unresolved ets)).map
            (substCallArgFn S)))[i]
          = .fvar () x none
        ∧ (CallArg.getInputExprs callArgs)[i]'hi_o = .fvar () x none) := by
  have h_len' : (List.map LExpr.unresolved ets).length
      = (CallArg.getInputExprs callArgs).length := by
    rw [List.length_map]; exact h_len
  simp only [CallArg.replaceInArgs] at hi ⊢
  rcases getInputExprs_go_transformed_node callArgs (List.map LExpr.unresolved ets) S
    h_len' i hi with ⟨he, h_eq⟩ | ⟨x, ho, h_eq1, h_eq2⟩
  · left
    have he' : i < ets.length := by rw [List.length_map] at he; exact he
    refine ⟨he', ?_⟩
    rw [h_eq]
    congr 1
    simp only [List.getElem_map]
  · right
    exact ⟨x, ho, h_eq1, h_eq2⟩

/-- Core lemma for the annotated `.call` case. -/
theorem typeCheckCmd_call_annotated_sound_aux (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (pname : String) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P (.call pname callArgs md) = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : ∀ proc,
      Program.Procedure.find? P ⟨pname, ()⟩ = some proc →
      ProcHeaderClosed proc) :
    CmdExtHasTypeA C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Statement.Command.subst Env'.stateSubstInfo.subst cmd')
      (TContext.subst Env.context Env'.stateSubstInfo.subst) := by
  unfold Statement.typeCheckCmd at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch] at h; contradiction
  · rename_i proc heq_find
    simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch,
               MonadExceptOf.tryCatch, Except.tryCatch] at h
    elim_err h with h_inner h_eq
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
    subst h1; subst h2; clear h
    -- Eliminate the 4 if-checks.
    elim_err h_eq with h_lhs_exist
    elim_err h_eq with h_out_arity
    elim_err h_eq with h_inp_arity
    elim_err h_eq with h_inout_check
    elim_err h_eq with h_inout_valid
    elim_err h_eq with v1 h_inst_lhs
    elim_err h_eq with lhs_tys Env1
    elim_err h_eq with v2 h_fvc
    elim_err h_eq with v3 h_inst_inputs
    elim_err h_eq with v4 h_resolves
    cases h_eq
    show CmdExtHasTypeA C P (Env.context.subst (v3.snd.updateSubst v4).stateSubstInfo.subst)
      (Statement.Command.subst (v3.snd.updateSubst v4).stateSubstInfo.subst
        (.call pname (CallArg.replaceInArgs callArgs (List.map LExpr.unresolved v3.fst)) md))
      (Env.context.subst (v3.snd.updateSubst v4).stateSubstInfo.subst)
    let S_final := (v3.snd.updateSubst v4).stateSubstInfo.subst
    let tyArgSubst : Subst := v2.2.snd
    let σ : List (TyIdentifier × LMonoTy) :=
      List.zip proc.header.typeArgs
        (proc.header.typeArgs.map (fun a => LMonoTy.subst S_final (LMonoTy.subst tyArgSubst (.ftvar a))))
    -- Raw (mapError-stripped) step equations, derived once.
    have h_unify : Constraints.unify
        ((List.map toLMonoTy v3.fst).zip
          (LMonoTys.subst v2.2.fst.stateSubstInfo.subst (ListMap.values v2.fst)) ++
          v1.zip (LMonoTys.subst v2.2.fst.stateSubstInfo.subst
            (List.map (LMonoTy.subst v2.2.snd) (ListMap.values proc.header.outputs))))
        v3.snd.stateSubstInfo = .ok v4 := by
      revert h_resolves; simp only [Except.mapError]; split <;> simp_all
    have h_resolves_raw : LExpr.resolves C v2.2.fst
        (CallArg.getInputExprs callArgs) = .ok v3 := by
      revert h_inst_inputs; simp only [Except.mapError]; split <;> simp_all
    have h_inst_lhs_raw : Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
        = .ok (some (v1, h_inst_lhs)) := by
      revert h_inout_valid; simp only [Except.mapError]; split <;> simp_all
    have h_inst_inp_raw : LMonoTySignature.instantiateWithSubst C h_inst_lhs
        proc.header.typeArgs proc.header.inputs = .ok v2 := by
      revert h_fvc; simp only [Except.mapError]; split <;> simp_all
    have h_fvc_raw : h_inst_lhs.freeVarChecks (CallArg.getInputExprs callArgs) = .ok () := by
      revert Env1; simp only [Except.mapError]; split <;> simp_all
    -- The shared, index-independent fact bundle for all call obligations.
    have F := callFacts C Env h_inst_lhs proc callArgs v1 v2 v3 v4
      h_inst_lhs_raw h_inst_inp_raw h_fvc_raw h_resolves_raw h_unify h_wf h_fwf h_ne
    rw [Command_subst_call]
    apply CmdExtHasType'.call (Γ := Env.context.subst S_final) (σ := σ) (proc := proc)
    · exact heq_find
    · -- input arity
      rw [getInputExprs_transformed_length]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_inp_arity
      exact h_inp_arity
    · -- output arity
      rw [getLhs_transformed]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_out_arity
      exact h_out_arity
    · -- lhs vars exist in substituted context
      rw [getLhs_transformed]
      intro v hv
      have h_not_none : ¬(Env.context.types.find? v).isNone = true := by
        intro h_none
        exact h_lhs_exist (List.any_eq_true.mpr ⟨v, hv, h_none⟩)
      cases h_opt : Env.context.types.find? v with
      | none => simp [h_opt] at h_not_none
      | some ty =>
        simp only [Option.isSome_iff_exists]
        exact ⟨_, TContext.subst_find_some Env.context S_final v ty h_opt⟩
    · -- HasTypeA for inputs
      intro i hi hj
      -- The original `getInputExprs[i]` index, transported across the bridge.
      have h_hi_orig : i < (CallArg.getInputExprs callArgs).length := by
        rw [getInputExprs_transformed_length] at hi; exact hi
      have h_alias_equiv := call_input_type_eq C h_inst_lhs proc callArgs v1 v2 v3 v4 i h_hi_orig hj
          F.len F.inst_inp_raw F.unify (h_closed proc heq_find) F.aliases_wf_lhs F.absorbs_v2
      simp only [List.get_eq_getElem] at h_alias_equiv
      rw [TContext.subst_aliases, ← F.ctx_lhs_env]
      -- Split on the transformed node: by-value (annotated) vs inout (bare fvar).
      rcases getInputExprs_transformed_node callArgs v3.fst S_final F.len i hi with
        ⟨hi_e, h_node⟩ | ⟨x, hi_o, h_node_tr, h_node_orig⟩
      · -- Branch B: by-value position. Witness = subst S_final (v3.fst[i].toLMonoTy).
        refine ⟨LMonoTy.subst S_final ((v3.fst[i]'(F.len ▸ h_hi_orig)).toLMonoTy), ?_, ?_⟩
        · -- AliasEquiv via call_input_type_eq.
          have h_get_eq : (v3.fst.get ⟨i, F.len ▸ h_hi_orig⟩).toLMonoTy
              = (v3.fst[i]'(F.len ▸ h_hi_orig)).toLMonoTy := by simp only [List.get_eq_getElem]
          rw [← h_get_eq]; exact h_alias_equiv
        · -- HasTypeA for the transformed by-value node.
          rw [h_node]
          have h_hta_raw : LExpr.HasTypeA []
              ((v3.fst[i]'(F.len ▸ h_hi_orig)).unresolved)
              ((v3.fst[i]'(F.len ▸ h_hi_orig)).toLMonoTy) := by
            have h_hta := resolves_HasTypeA C v2.2.fst v3.snd
              (CallArg.getInputExprs callArgs) v3.fst F.resolves_raw F.wf_v2 h_fwf F.ne_v2
              (F.ctx_eq ▸ h_resolved) F.len i h_hi_orig
            simpa only [List.get_eq_getElem] using h_hta
          have h_hta_subst := applySubst_typeCheck S_final h_hta_raw
          simp only [List.map_nil] at h_hta_subst
          -- The transformed by-value node is never a bare fvar, so the match
          -- reduces to its `e` arm (`exprTyped = HasTypeA [] e mty`, embed = id).
          split
          · rename_i m y h_eq
            exact absurd h_eq (unresolved_applySubst_ne_fvar_none _ S_final m y)
          · exact h_hta_subst
      · -- Branch A: inout position. Witness = subst S_final mty_ctx (relation-indep).
        obtain ⟨mty_ctx, h_find_ctx, h_ae_ctx⟩ :=
          resolves_fvar_aliasEquiv C v2.2.fst v3.snd (CallArg.getInputExprs callArgs) v3.fst
            F.resolves_raw F.wf_v2 h_fwf F.ne_v2 (F.ctx_eq ▸ h_mono) F.ws F.len i h_hi_orig () x
            (by simp only [List.get_eq_getElem]; exact h_node_orig)
        rw [h_node_tr]
        refine ⟨LMonoTy.subst S_final mty_ctx, ?_, ?_⟩
        · -- AliasEquiv via trans(Layer-3 @ S_final, call_input_type_eq).
          have h_absorbs_final : Subst.absorbs S_final v3.snd.stateSubstInfo.subst :=
            Constraints.unify_absorbs _ _ _ F.unify
          have h_ae_S := h_ae_ctx S_final h_absorbs_final
          simp only [List.get_eq_getElem] at h_ae_S
          rw [F.ctx_eq, ← F.ctx_lhs_env] at h_ae_S
          exact AliasEquiv.trans h_ae_S h_alias_equiv
        · -- find? side: lift the context lookup through `TContext.subst`.
          show (h_inst_lhs.context.subst S_final).types.find? x
            = some (LTy.forAll [] (LMonoTy.subst S_final mty_ctx))
          rw [F.ctx_lhs_env]
          have h_find_env : Env.context.types.find? x = some (.forAll [] mty_ctx) :=
            F.ctx_eq ▸ h_find_ctx
          have h_find_subst := TContext.subst_find_some Env.context S_final x
            (.forAll [] mty_ctx) h_find_env
          rw [LTy.subst_forAll_nil] at h_find_subst
          exact h_find_subst
    · -- lhs types match outputs
      rw [getLhs_transformed]
      intro i hi hj
      rw [TContext.subst_aliases]
      exact call_output_type_eq C Env h_inst_lhs proc callArgs v1 v2 v3 v4 i hi hj
        h_mono F.inst_lhs_raw F.unify (h_closed proc heq_find)
        h_wf.aliasesWF F.subst_v2_env F.absorbs_v2
    · -- inout args are simple vars
      intro i hi h_contains
      have h_inout_raw : Statement.areInoutArgsValid proc (CallArg.getInputExprs callArgs) = true := by
        revert h_inout_check
        cases Statement.areInoutArgsValid proc (CallArg.getInputExprs callArgs) <;> simp
      have h_arity : (CallArg.getInputExprs callArgs).length
          = (ListMap.keys proc.header.inputs).length := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_inp_arity
        rw [h_inp_arity, ListMap.keys.length]
      -- The original input node at `i` is a simple variable named `keys[i]`.
      have hi_orig : i < (CallArg.getInputExprs callArgs).length := by rw [h_arity]; exact hi
      obtain ⟨m_o, ty_o, h_orig_get⟩ := areInoutArgsValid_implies_fvar proc
        (CallArg.getInputExprs callArgs) h_inout_raw i (h_arity ▸ hi) h_contains h_arity
      rw [List.getElem?_eq_getElem hi_orig] at h_orig_get
      have h_orig_get' : (CallArg.getInputExprs callArgs)[i] =
          .fvar m_o (ListMap.keys proc.header.inputs)[i] ty_o :=
        Option.some.inj h_orig_get
      -- Transform the `[i]?` goal into a `[i]` claim (index is in range).
      have hi_tr : i < (CallArg.getInputExprs
          ((CallArg.replaceInArgs callArgs (List.map LExpr.unresolved v3.fst)).map
            (substCallArgFn S_final))).length := by
        rw [getInputExprs_transformed_length, h_arity]; exact hi
      rw [List.getElem?_eq_getElem hi_tr]
      -- Bridge: transformed node is annotated by-value or bare inout fvar.
      rcases getInputExprs_transformed_node callArgs v3.fst S_final F.len i hi_tr with
        ⟨hi_e, h_node⟩ | ⟨x, hi_o, h_node_tr, h_node_orig⟩
      · -- By-value: the resolved node `v3.fst[i]` is a fvar named `keys[i]`.
        have h_get : (CallArg.getInputExprs callArgs).get ⟨i, hi_orig⟩
            = .fvar m_o (ListMap.keys proc.header.inputs)[i] ty_o := by
          simp only [List.get_eq_getElem]; exact h_orig_get'
        obtain ⟨m', ty', h_v3_fvar⟩ := resolves_fvar_name C v2.2.fst v3.snd
          (CallArg.getInputExprs callArgs) v3.fst F.resolves_raw F.wf_v2 h_fwf F.ne_v2 F.len
          i hi_orig m_o (ListMap.keys proc.header.inputs)[i] ty_o h_get
        simp only [List.get_eq_getElem] at h_v3_fvar
        rw [h_node, h_v3_fvar]
        -- `(unresolved (fvar ..)).applySubst S` is a fvar with the same name.
        rw [LExpr.applySubst_eq_replaceUserProvidedType]
        simp only [LExpr.unresolved, LExpr.replaceUserProvidedType]
        exact ⟨_, _, rfl⟩
      · -- Inout: transformed node is the bare `fvar () x none`; `x = keys[i]`.
        rw [h_node_tr]
        have h_x_eq : x = (ListMap.keys proc.header.inputs)[i] := by
          have h_eq := h_node_orig.symm.trans h_orig_get'
          simp only [LExpr.fvar.injEq] at h_eq
          exact h_eq.2.1
        rw [h_x_eq]
        exact ⟨_, _, rfl⟩

/-! ### Part II — Annotated soundness -/

/--
Annotated soundness of the command typechecker for `Command` (CmdExt):
if `typeCheckCmd` succeeds, the output command satisfies `CmdExtHasTypeA`.
-/
theorem Command.typeCheckCmd_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (cmd cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : ∀ proc pname callArgs md,
      cmd = .call pname callArgs md →
      Program.Procedure.find? P pname = some proc →
      ProcHeaderClosed proc) :
    CmdExtHasTypeA C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Statement.Command.subst Env'.stateSubstInfo.subst cmd')
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | cmd c =>
    unfold Statement.typeCheckCmd at h
    simp only [Bind.bind, Except.bind] at h
    elim_err h with v h_tc
    obtain ⟨c', Env'_inner⟩ := v
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_cmd_eq, h_env_eq⟩ := h
    subst h_cmd_eq; subst h_env_eq
    have h_sound := Cmd.typeCheck_annotated_sound C Env c c' Env'_inner h_tc
      h_wf h_fwf h_ne h_mono h_resolved
    exact Command_subst_cmd_HasTypeA C P Env Env'_inner c' h_sound
  | call pname callArgs md =>
    have h_ctx := typeCheckCmd_call_preserves_context C Env P pname callArgs md cmd' Env' h
      h_wf h_fwf h_ne
    rw [h_ctx]
    have h_closed' := h_closed
    simp only [CmdExt.call.injEq] at h_closed'
    exact typeCheckCmd_call_annotated_sound_aux C Env P pname callArgs md cmd' Env' h
      h_wf h_fwf h_ne h_mono h_resolved
      (fun proc h_find => h_closed' proc pname callArgs md ⟨rfl, rfl, rfl⟩ h_find)

end TypeSpec
end Core

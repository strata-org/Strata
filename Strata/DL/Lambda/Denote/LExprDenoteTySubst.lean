/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.LExprDenoteProps

/-!
## Type Substitution and Denotation

Proves that `applySubst` (applying a type substitution to annotations) commutes
with denotation — changing annotations is equivalent to changing the type variable
valuation.

- `applySubst_typeCheck` — `applySubst` preserves typing, mapping types through `subst S`
- `denote_applySubst` — denotation of `applySubst S e` equals denotation of `e` under modified valuation
-/

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)


/-! ## `substTyVars` commutation lemmas -/

theorem substTyVars_mkArrow' (vt : TyVarVal) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.mkArrow' ret ins) =
    LSort.mkArrow (LMonoTy.substTyVars vt ret) (ins.map (LMonoTy.substTyVars vt)) := by
  induction ins with
  | nil => simp [LMonoTy.mkArrow'_nil, LSort.mkArrow]
  | cons x xs ih =>
    rw [LMonoTy.mkArrow'_cons]
    simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map]
    rw [ih]
    rfl

theorem substTyVars_subst (vt : TyVarVal) (S : Subst) (ty : LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.subst S ty) =
    LMonoTy.substTyVars
      (fun x => match S.find? x with | some t => LMonoTy.substTyVars vt t | none => vt x)
      ty := by
  induction ty with
  | ftvar x =>
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.substTyVars]
    split <;> rename_i heq <;>
    -- For some reason, Lean does not unify theses
    split <;> rename_i heq1 <;> rw[heq] at heq1 <;> try grind
    simp[LMonoTy.substTyVars]
  | bitvec n =>
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.substTyVars]
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.substTyVars]
    congr 1
    induction args with
    | nil => rfl
    | cons a as iha =>
      simp only [List.map, LMonoTy.substTyVars.map]
      congr 1
      · exact ih a (List.Mem.head _)
      · exact iha (fun t ht => ih t (List.Mem.tail _ ht))

private theorem LConst.subst_ty (S : Subst) (c : LConst) : LMonoTy.subst S c.ty = c.ty := by
  cases c <;> simp [LConst.ty, LMonoTy.int, LMonoTy.real, LMonoTy.string, LMonoTy.bool] <;> try rw [LMonoTy.subst_tcons, LMonoTys.subst_nil]<;> rfl
  apply LMonoTy.subst_bitvec

/-- `applySubst` preserves typing, mapping types through `subst S`. -/
theorem applySubst_typeCheck (S : Subst)
    {e : LExpr T.mono} {τ : LMonoTy} {Δ : List LMonoTy}
    (h : LExpr.HasTypeA Δ e τ)
    : LExpr.HasTypeA (Δ.map (LMonoTy.subst S)) (e.applySubst S) (LMonoTy.subst S τ) := by
  rw [LExpr.applySubst_eq_replaceUserProvidedType]
  induction h with
  | const =>
    simp only [LExpr.replaceUserProvidedType]
    rename_i c
    rw [LConst.subst_ty S c]; exact .const
  | op => simp [LExpr.replaceUserProvidedType, Option.map]; exact .op
  | fvar => simp [LExpr.replaceUserProvidedType, Option.map]; exact .fvar
  | bvar h_lookup =>
    simp [LExpr.replaceUserProvidedType]
    exact .bvar (by simp [List.getElem?_map, h_lookup])
  | abs _ ih =>
    simp only [LExpr.replaceUserProvidedType, Option.map]
    simp only [LMonoTy.arrow]
    rw [LMonoTy.subst_tcons_pair]
    exact .abs ih
  | quant _ _ ih_tr ih_body =>
    simp only [LExpr.replaceUserProvidedType, Option.map]
    have h_bool := LMonoTy.subst_bool S
    rw [h_bool]
    exact .quant ih_tr (h_bool ▸ ih_body)
  | app _ _ ih_fn ih_arg =>
    simp only [LExpr.replaceUserProvidedType]
    rename_i aty rty _ _ _ _
    have h_arrow : LMonoTy.subst S (aty.arrow rty) = (LMonoTy.subst S aty).arrow (LMonoTy.subst S rty) := by
      simp only [LMonoTy.arrow]; exact LMonoTy.subst_tcons_pair S "arrow" aty rty
    exact .app (h_arrow ▸ ih_fn) ih_arg
  | ite _ _ _ ih_c ih_t ih_e =>
    simp only [LExpr.replaceUserProvidedType]
    exact .ite (LMonoTy.subst_bool S ▸ ih_c) ih_t ih_e
  | eq _ _ ih_1 ih_2 =>
    simp only [LExpr.replaceUserProvidedType]
    rw [LMonoTy.subst_bool]
    exact .eq ih_1 ih_2

/-- `applySubst` transforms `fvars_annotated_by` consistently. -/
theorem applySubst_fvars_annotated [DecidableEq T.IDMeta] {S : Subst}
    {e : LExpr T.mono} {tyMap : Map T.Identifier LMonoTy}
    (h : fvars_annotated_by tyMap e)
    : fvars_annotated_by (tyMap.map (fun (k, v) => (k, LMonoTy.subst S v))) (e.applySubst S) := by
  rw [LExpr.applySubst_eq_replaceUserProvidedType]
  induction e with
  | fvar m name uty =>
    cases uty with
    | none => exact absurd h id
    | some ty =>
      simp only [LExpr.replaceUserProvidedType, Option.map, fvars_annotated_by] at *
      intro ty' h_find
      -- tyMap.map (fun x => (x.fst, subst S x.snd)) = tyMap.fmap (subst S)
      have h_fmap : List.map (fun x => (x.fst, LMonoTy.subst S x.snd)) tyMap = Map.fmap (LMonoTy.subst S) tyMap := rfl
      rw [h_fmap] at h_find
      rw [Map.find?_fmap] at h_find
      cases h_orig : Map.find? tyMap name with
      | none => simp [h_orig] at h_find
      | some v => simp [h_orig] at h_find; rw [← h_find, h v h_orig]
  | const | bvar | op => trivial
  | app _ fn arg ih_fn ih_arg =>
    simp only [LExpr.replaceUserProvidedType, fvars_annotated_by] at *
    exact ⟨ih_fn h.1, ih_arg h.2⟩
  | abs _ _ _ body ih =>
    simp only [LExpr.replaceUserProvidedType, fvars_annotated_by] at *
    exact ih h
  | ite _ c t f ih_c ih_t ih_f =>
    simp only [LExpr.replaceUserProvidedType, fvars_annotated_by] at *
    exact ⟨ih_c h.1, ih_t h.2.1, ih_f h.2.2⟩
  | eq _ e1 e2 ih1 ih2 =>
    simp only [LExpr.replaceUserProvidedType, fvars_annotated_by] at *
    exact ⟨ih1 h.1, ih2 h.2⟩
  | quant _ _ _ _ tr body ih_tr ih_body =>
    simp only [LExpr.replaceUserProvidedType, fvars_annotated_by] at *
    exact ⟨ih_tr h.1, ih_body h.2⟩

/-- Extend `h_bvar_compat` when pushing a new bound variable onto the context.
Used in the `abs` and `quant` cases of `denote_applySubst_gen`. -/
private theorem bvar_compat_cons
    {S : Subst} {vt vt' : TyVarVal}
    (hvt' : vt' = fun x => match S.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x)
    {Δ : List LMonoTy} {ty : LMonoTy}
    {bvarVal : BVarVal tcInterp vt (Δ.map (LMonoTy.subst S))}
    {bvarVal' : BVarVal tcInterp vt' Δ}
    (h_bvar_compat : ∀ (i : Nat) (τ_b : LMonoTy)
        (hb : Δ[i]? = some τ_b)
        (hb' : (Δ.map (LMonoTy.subst S))[i]? = some (LMonoTy.subst S τ_b)),
        cast (congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S τ_b))
          (bvarVal.get i hb') = bvarVal'.get i hb)
    (y : TyDenote tcInterp vt' ty)
    (h_td_ty : TyDenote tcInterp vt (LMonoTy.subst S ty) = TyDenote tcInterp vt' ty)
    : ∀ (i : Nat) (τ_b : LMonoTy)
        (hb : (ty :: Δ)[i]? = some τ_b)
        (hb' : ((ty :: Δ).map (LMonoTy.subst S))[i]? = some (LMonoTy.subst S τ_b)),
        cast (congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S τ_b))
          ((HList.cons (f := TyDenote tcInterp vt) (cast h_td_ty.symm y) bvarVal).get i hb') =
        (HList.cons (f := TyDenote tcInterp vt') y bvarVal').get i hb := by
  intro i τ_b hb hb'
  cases i with
  | zero => simp [HList.get]; grind
  | succ j =>
    simp only [List.getElem?_cons_succ, List.map_cons, List.getElem?_cons_succ] at hb hb'
    simp only [HList.get]
    exact h_bvar_compat j τ_b hb hb'

/-- Generalized `denote_applySubst` for arbitrary bvar contexts.
The induction for `abs` and `quant` extends the context, so we need this
generalized form as the workhorse. -/
private theorem denote_applySubst_gen
    {S : Subst} {vt vt' : TyVarVal}
    (hvt' : vt' = fun x => match S.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x)
    {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h_body : LExpr.HasTypeA Δ e τ)
    (h_subst : LExpr.HasTypeA (Δ.map (LMonoTy.subst S)) (e.applySubst S) (LMonoTy.subst S τ))
    (h_td : TyDenote tcInterp vt (LMonoTy.subst S τ) = TyDenote tcInterp vt' τ)
    {bvarVal : BVarVal tcInterp vt (Δ.map (LMonoTy.subst S))}
    {bvarVal' : BVarVal tcInterp vt' Δ}
    (h_bvar_compat : ∀ (i : Nat) (τ_b : LMonoTy)
        (hb : Δ[i]? = some τ_b)
        (hb' : (Δ.map (LMonoTy.subst S))[i]? = some (LMonoTy.subst S τ_b)),
        cast (congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S τ_b))
          (bvarVal.get i hb') = bvarVal'.get i hb)
    : cast h_td
        (LExpr.denote tcInterp opInterp fvarVal vt bvarVal (e.applySubst S) (LMonoTy.subst S τ) h_subst) =
      LExpr.denote tcInterp opInterp fvarVal vt' bvarVal' e τ h_body := by
  have h_eq : e.applySubst S = LExpr.replaceUserProvidedType e (LMonoTy.subst S) :=
    LExpr.applySubst_eq_replaceUserProvidedType e S
  revert h_subst h_eq
  generalize e.applySubst S = e'
  intros h_subst h_eq
  subst h_eq
  -- Induct on e
  revert Δ τ bvarVal bvarVal' h_bvar_compat h_body h_subst h_td
  induction e with
  | const m c =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    rw [denote_const, denote_const]
    have h_inv := HasTypeA.const_inv h_body      -- c.ty = τ
    subst h_inv
    have h_inv_s := HasTypeA.const_inv h_subst
    -- Relate denoteConst at vt vs vt'
    rw [denoteConst_cast_vt (tcInterp := tcInterp) vt vt' c]
    · grind
    · exact (h_inv_s ▸ h_td).symm
  | op m o uty =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType, Option.map] at h_subst ⊢
    cases uty with
    | none => exact absurd h_body (by intro h; cases h)
    | some ty =>
      rw [denote_op, denote_op]
      have h_inv := HasTypeA.op_inv h_body
      subst h_inv
      have h_sorts : LMonoTy.substTyVars vt (LMonoTy.subst S τ) = LMonoTy.substTyVars vt' τ :=
        hvt' ▸ substTyVars_subst vt S τ
      grind
  | bvar m i =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    rw [denote_bvar, denote_bvar]
    have hb := HasTypeA.bvar_inv h_body
    have hb' := HasTypeA.bvar_inv h_subst
    have h_compat := h_bvar_compat i τ hb hb'
    rw [show cast h_td (bvarVal.get i (HasTypeA.bvar_inv h_subst)) =
            cast h_td (bvarVal.get i hb') from rfl]
    rw [show HList.get bvarVal' i (HasTypeA.bvar_inv h_body) =
            HList.get bvarVal' i hb from rfl]
    rw [← h_compat]
  | fvar m x uty =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType, Option.map] at h_subst ⊢
    cases uty with
    | none => exact absurd h_body (by intro h; cases h)
    | some ty =>
      rw [denote_fvar, denote_fvar]
      have h_inv := HasTypeA.fvar_inv h_body
      subst h_inv
      have h_sorts : LMonoTy.substTyVars vt (LMonoTy.subst S τ) = LMonoTy.substTyVars vt' τ :=
        hvt' ▸ substTyVars_subst vt S τ
      grind
  | abs m name uty body ih =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    cases uty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some aty =>
    have ⟨rty, h_eq, h_body'⟩ := HasTypeA.abs_inv h_body
    have ⟨rty_s, h_eq_s, h_body_s⟩ := HasTypeA.abs_inv h_subst
    subst h_eq
    have h_subst_arrow : LMonoTy.subst S (aty.arrow rty) = (LMonoTy.subst S aty).arrow (LMonoTy.subst S rty) :=
      LMonoTy.subst_tcons_pair S "arrow" aty rty
    have h_rty_s : rty_s = LMonoTy.subst S rty := by
      have h_eq_arrow := h_subst_arrow ▸ h_eq_s; cases h_eq_arrow; rfl
    subst h_rty_s
    -- Use denote_cast_ty, then denote_abs on both sides
    have h_subst' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.abs m name (some (LMonoTy.subst S aty)) (body.replaceUserProvidedType (LMonoTy.subst S)))
        ((LMonoTy.subst S aty).arrow (LMonoTy.subst S rty)) :=
      h_subst_arrow ▸ h_subst
    simp only [Option.map] at *
    change LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.abs m name (some (LMonoTy.subst S aty)) (body.replaceUserProvidedType (LMonoTy.subst S)))
        (LMonoTy.subst S (aty.arrow rty)) at h_subst
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_subst_arrow h_subst h_subst' bvarVal]
    rw [denote_abs bvarVal h_body_s h_subst', denote_abs bvarVal' h_body' h_body]
    simp only [cast_cast]
    -- Decompose cast through arrow type and apply IH
    have h_td_aty : TyDenote tcInterp vt (LMonoTy.subst S aty) = TyDenote tcInterp vt' aty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S aty)
    have h_td_rty : TyDenote tcInterp vt (LMonoTy.subst S rty) = TyDenote tcInterp vt' rty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S rty)
    funext y
    have h_fn_eq : (TyDenote tcInterp vt (LMonoTy.subst S aty) → TyDenote tcInterp vt (LMonoTy.subst S rty)) =
        (TyDenote tcInterp vt' aty → TyDenote tcInterp vt' rty) := by
      rw [h_td_aty, h_td_rty]
    have h_cast_fn := cast_fn_apply h_fn_eq h_td_aty h_td_rty
        (fun x => LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal)
          (body.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S rty) h_body_s) y
    apply Eq.trans h_cast_fn
    apply ih h_body' h_td_rty
    exact bvar_compat_cons (tcInterp := tcInterp) hvt' h_bvar_compat y h_td_aty
  | app m fn arg ih_fn ih_arg =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h_body
    have ⟨aty_s, h_fn_s, h_arg_s⟩ := HasTypeA.app_inv h_subst
    rw [denote_app bvarVal h_fn_s h_arg_s, denote_app bvarVal' h_fn h_arg]
    -- Establish aty_s = subst S aty
    have h_subst_arrow : LMonoTy.subst S (aty.arrow τ) = (LMonoTy.subst S aty).arrow (LMonoTy.subst S τ) :=
      LMonoTy.subst_tcons_pair S "arrow" aty τ
    have h_aty_s : aty_s = LMonoTy.subst S aty := by
      have h_fn_s' := applySubst_typeCheck S h_fn
      rw [LExpr.applySubst_eq_replaceUserProvidedType, h_subst_arrow] at h_fn_s'
      have h_unique := HasTypeA_unique h_fn_s h_fn_s'
      cases h_unique; rfl
    subst h_aty_s
    have h_td_fn : TyDenote tcInterp vt ((LMonoTy.subst S aty).arrow (LMonoTy.subst S τ)) =
                   TyDenote tcInterp vt' (aty.arrow τ) :=
      h_subst_arrow ▸ congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S (aty.arrow τ))
    have h_td_arg : TyDenote tcInterp vt (LMonoTy.subst S aty) = TyDenote tcInterp vt' aty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S aty)
    rw [← cast_app h_td_fn h_td_arg h_td]
    -- Use denote_cast_ty to normalize fn's type index
    have h_fn_s' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (fn.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S (aty.arrow τ)) :=
      h_subst_arrow ▸ h_fn_s
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_subst_arrow.symm h_fn_s h_fn_s' bvarVal]
    set_option backward.isDefEq.respectTransparency false in simp only [cast_cast]
    have h_td_fn' : TyDenote tcInterp vt (LMonoTy.subst S (aty.arrow τ)) = TyDenote tcInterp vt' (aty.arrow τ) :=
      h_subst_arrow ▸ h_td_fn
    have h_ih_fn := ih_fn h_fn h_td_fn' h_bvar_compat h_fn_s'
    have h_ih_arg := ih_arg h_arg h_td_arg h_bvar_compat h_arg_s
    set_option backward.isDefEq.respectTransparency false in rw [h_ih_arg, h_ih_fn]
  | ite m c t e ih_c ih_t ih_e =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    have ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h_body
    have ⟨h_c_s, h_t_s, h_e_s⟩ := HasTypeA.ite_inv h_subst
    rw [denote_ite bvarVal h_c_s h_t_s h_e_s, denote_ite bvarVal' h_c h_t h_e]
    -- Apply IH on condition, converting between subst S .bool and .bool
    have h_subst_bool : LMonoTy.subst S .bool = .bool := LMonoTy.subst_bool S
    have h_c_s' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (c.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S .bool) :=
      h_subst_bool.symm ▸ h_c_s
    have h_td_bool : TyDenote tcInterp vt (LMonoTy.subst S .bool) = TyDenote tcInterp vt' .bool :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S .bool)
    have h_ih_c := ih_c h_c h_td_bool h_bvar_compat h_c_s'
    have h_cond_eq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (c.replaceUserProvidedType (LMonoTy.subst S)) .bool h_c_s =
      cast (congrArg (TyDenote tcInterp vt) h_subst_bool)
        (LExpr.denote tcInterp opInterp fvarVal vt bvarVal
          (c.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S .bool) h_c_s') :=
      denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_subst_bool.symm h_c_s h_c_s' bvarVal
    rw [h_cond_eq]
    grind
  | eq m e1 e2 ih1 ih2 =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    have ⟨ty', h_τ, h_1, h_2⟩ := HasTypeA.eq_inv h_body
    have ⟨ty_s, h_τ_s, h_1_s, h_2_s⟩ := HasTypeA.eq_inv h_subst
    subst h_τ
    have h_ty_s : ty_s = LMonoTy.subst S ty' := by
      have h_applySubst := applySubst_typeCheck S h_1
      rw [LExpr.applySubst_eq_replaceUserProvidedType] at h_applySubst
      exact HasTypeA_unique h_1_s h_applySubst
    subst h_ty_s
    have h_td_ty : TyDenote tcInterp vt (LMonoTy.subst S ty') = TyDenote tcInterp vt' ty' :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S ty')
    have h_ih1 := ih1 h_1 h_td_ty h_bvar_compat h_1_s
    have h_ih2 := ih2 h_2 h_td_ty h_bvar_compat h_2_s
    -- Convert type index from subst S .bool to .bool via denote_cast_ty
    have h_subst' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.eq m (e1.replaceUserProvidedType (LMonoTy.subst S)) (e2.replaceUserProvidedType (LMonoTy.subst S))) .bool :=
      h_τ_s ▸ h_subst
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_τ_s h_subst h_subst' bvarVal]
    by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (e1.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S ty') h_1_s =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (e2.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S ty') h_2_s
    · rw [denote_eq_true bvarVal h_1_s h_2_s h_subst' heq,
          denote_eq_true bvarVal' h_1 h_2 h_body (by rw [← h_ih1, ← h_ih2]; exact congrArg (cast h_td_ty) heq)]
      grind
    · rw [denote_eq_false bvarVal h_1_s h_2_s h_subst' heq,
          denote_eq_false bvarVal' h_1 h_2 h_body (by
            intro h; apply heq
            have h1 := h_ih1.symm; have h2 := h_ih2.symm
            rw [h] at h1
            exact cast_injective h_td_ty (h1.symm.trans h2))]
      grind
  | quant m qk name argTy tr body ih_tr ih_body =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    cases argTy with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h_body) (by simp [LExpr.typeCheck])
    | some qty =>
    have ⟨τ_tr, h_τ, h_tr, h_body_q⟩ := HasTypeA.quant_inv h_body
    have ⟨τ_tr_s, h_τ_s, h_tr_s, h_body_q_s⟩ := HasTypeA.quant_inv h_subst
    subst h_τ
    simp only [Option.map] at *
    -- Convert type index from subst S .bool to .bool
    change LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.quant m qk name (some (LMonoTy.subst S qty)) (tr.replaceUserProvidedType (LMonoTy.subst S))
          (body.replaceUserProvidedType (LMonoTy.subst S)))
        (LMonoTy.subst S .bool) at h_subst
    have h_subst' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.quant m qk name (some (LMonoTy.subst S qty)) (tr.replaceUserProvidedType (LMonoTy.subst S))
          (body.replaceUserProvidedType (LMonoTy.subst S))) .bool :=
      h_τ_s ▸ h_subst
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_τ_s h_subst h_subst' bvarVal]
    have h_td_qty : TyDenote tcInterp vt (LMonoTy.subst S qty) = TyDenote tcInterp vt' qty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S qty)
    have h_td_bool : TyDenote tcInterp vt (LMonoTy.subst S .bool) = TyDenote tcInterp vt' .bool :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S .bool)
    simp only [cast_cast]
    have h_body_q_s' : LExpr.HasTypeA ((qty :: Δ).map (LMonoTy.subst S))
        (body.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S .bool) := by grind
    -- Case split on quantifier kind
    cases qk with
    | all =>
      by_cases hall : ∀ x : TyDenote tcInterp vt (LMonoTy.subst S qty),
          (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal)
            (body.replaceUserProvidedType (LMonoTy.subst S)) .bool h_body_q_s : Bool) = true
      · rw [denote_quant_all_true bvarVal h_body_q_s h_subst' hall,
            denote_quant_all_true bvarVal' h_body_q h_body (by
              intro y
              have h_ih := ih_body h_body_q h_td_bool
                  (bvar_compat_cons (tcInterp := tcInterp) hvt' h_bvar_compat y h_td_qty) h_body_q_s'
              simp at h_ih; grind)]
        grind
      · have ⟨w, hw⟩ := Classical.not_forall.mp hall
        have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal)
            (body.replaceUserProvidedType (LMonoTy.subst S)) .bool h_body_q_s : Bool) = false :=
          Bool.eq_false_iff.mpr hw
        rw [denote_quant_all_false bvarVal h_body_q_s h_subst' w hwf,
            denote_quant_all_false bvarVal' h_body_q h_body (cast h_td_qty w) (by
              have h_ih := ih_body h_body_q h_td_bool
                  (bvar_compat_cons (tcInterp := tcInterp) hvt' h_bvar_compat (cast h_td_qty w) h_td_qty) h_body_q_s'
              simp at h_ih; grind)]
        grind
    | exist =>
      by_cases hexist : ∃ x : TyDenote tcInterp vt (LMonoTy.subst S qty),
          (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal)
            (body.replaceUserProvidedType (LMonoTy.subst S)) .bool h_body_q_s : Bool) = true
      · obtain ⟨w, hw⟩ := hexist
        rw [denote_quant_exist_true bvarVal h_body_q_s h_subst' w hw,
            denote_quant_exist_true bvarVal' h_body_q h_body (cast h_td_qty w) (by
              have h_ih := ih_body h_body_q h_td_bool
                  (bvar_compat_cons (tcInterp := tcInterp) hvt' h_bvar_compat (cast h_td_qty w) h_td_qty) h_body_q_s'
              simp at h_ih; grind)]
        grind
      · have hexist_f : ∀ x : TyDenote tcInterp vt (LMonoTy.subst S qty),
            (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal)
              (body.replaceUserProvidedType (LMonoTy.subst S)) .bool h_body_q_s : Bool) = false :=
          fun x => Bool.eq_false_iff.mpr (fun h => hexist ⟨x, h⟩)
        rw [denote_quant_exist_false bvarVal h_body_q_s h_subst' hexist_f,
            denote_quant_exist_false bvarVal' h_body_q h_body (by
              intro y
              have h_ih := ih_body h_body_q h_td_bool
                  (bvar_compat_cons (tcInterp := tcInterp) hvt' h_bvar_compat y h_td_qty) h_body_q_s'
              simp at h_ih; grind)]
        grind

/-- Applying a type substitution to annotations is equivalent to changing the
type variable valuation. Specialization of `denote_applySubst_gen` to `Δ = []`. -/
theorem denote_applySubst
    {S : Subst} {vt vt' : TyVarVal}
    (hvt' : vt' = fun x => match S.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x)
    {e : LExpr T.mono} {τ : LMonoTy}
    (h_body : LExpr.HasTypeA [] e τ)
    (h_subst : LExpr.HasTypeA [] (e.applySubst S) (LMonoTy.subst S τ))
    (h_td : TyDenote tcInterp vt (LMonoTy.subst S τ) = TyDenote tcInterp vt' τ)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil (e.applySubst S) (LMonoTy.subst S τ) h_subst =
      cast h_td.symm (LExpr.denote tcInterp opInterp fvarVal vt' .nil e τ h_body) := by
  have h_gen := denote_applySubst_gen tcInterp opInterp fvarVal hvt' h_body h_subst h_td
    (bvarVal := .nil) (bvarVal' := .nil)
    (fun i _ hb _ => absurd hb (by simp))
  set_option backward.isDefEq.respectTransparency false in rw [← h_gen, cast_cast, cast_eq]

end Lambda

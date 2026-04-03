/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteSubst

namespace Lambda

/-- When a sort `s` decomposes as `mkArrow ret args` and as `mkArrow ret' args'`
with `args = args'`, then `applyArgs` agrees up to a cast on the return type. -/
theorem applyArgs_cast_eq
    {s : LSort} {ret ret' : LSort} {args args' : List LSort}
    (h₁ : s = LSort.mkArrow ret args)
    (h₂ : s = LSort.mkArrow ret' args')
    (h_args : args = args')
    (h_ret : ret = ret')
    -- (h_ret : SortDenote tcInterp ret = SortDenote tcInterp ret')
    (v : SortDenote tcInterp s)
    (da : HList (SortDenote tcInterp) args)
    : SortDenote.applyArgs tcInterp (cast (congrArg (SortDenote tcInterp) h₁) v) da
      = cast (congrArg (SortDenote tcInterp) h_ret.symm)
          (SortDenote.applyArgs tcInterp (cast (congrArg (SortDenote tcInterp) h₂) v) (HList.cast h_args da)) := by
  subst_vars; rfl

/-! ## `OpsConsistent` — every `.op` annotation is a valid instantiation -/

/-- Every call in `e` has a valid type substitution derivable by `computeTypeSubst`,
and the `.op` annotation is consistent with that substitution applied to the
function's generic type. -/
def OpsConsistent (F : @Factory T) : LExpr T.mono → Prop := fun e =>
  (match F.callOfLFunc e with
   | some (callee, args, fn) =>
       match LFunc.computeTypeSubst fn callee args with
       | some tySubst =>
           match callee with
           | .op _ _ (some ty_op) =>
               ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst
           | _ => False
       | none => False
   | none => True)
  ∧
  (match e with
   | .app _ fn arg => OpsConsistent F fn ∧ OpsConsistent F arg
   | .abs _ _ _ body => OpsConsistent F body
   | .ite _ c t f => OpsConsistent F c ∧ OpsConsistent F t ∧ OpsConsistent F f
   | .eq _ e1 e2 => OpsConsistent F e1 ∧ OpsConsistent F e2
   | .quant _ _ _ _ tr body => OpsConsistent F tr ∧ OpsConsistent F body
   | _ => True)

/-! ## `substTyVars` commutation lemmas -/

theorem substTyVars_mkArrow' (vt : TyVarVal) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.mkArrow' ret ins) =
    LSort.mkArrow (LMonoTy.substTyVars vt ret) (ins.map (LMonoTy.substTyVars vt)) := by
  sorry

theorem substTyVars_subst (vt : TyVarVal) (S : Subst) (ty : LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.subst S ty) =
    LMonoTy.substTyVars
      (fun x => match S.find? x with | some t => LMonoTy.substTyVars vt t | none => vt x)
      ty := by
  sorry

/-! ## `getLFuncCall` typing and denotation -/

/-- Helper: `mkArrow' τ (xs ++ ys) = mkArrow' (mkArrow' τ ys) xs` -/
theorem mkArrow'_append (τ : LMonoTy) (xs ys : List LMonoTy) :
    LMonoTy.mkArrow' τ (xs ++ ys) = LMonoTy.mkArrow' (LMonoTy.mkArrow' τ ys) xs := by
  sorry

private theorem getLFuncCall_go_spec
    {T : LExprParams}
    {e : LExpr T.mono} {τ : LMonoTy}
    {acc : List (LExpr T.mono)} {accTys : List LMonoTy}
    (h_e : LExpr.HasTypeA [] e (LMonoTy.mkArrow' τ accTys))
    (h_acc : List.Forall₂ (LExpr.HasTypeA []) acc accTys)
    : let (op, allArgs) := getLFuncCall.go e acc
      ∃ opArgTys,
        List.Forall₂ (LExpr.HasTypeA []) allArgs opArgTys ∧
        LExpr.HasTypeA [] op (LMonoTy.mkArrow' τ opArgTys) := by
  sorry

theorem getLFuncCall_spec
    {T : LExprParams}
    {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] e τ)
    : let (op, args) := getLFuncCall e
      ∃ argTys,
        List.Forall₂ (LExpr.HasTypeA []) args argTys ∧
        LExpr.HasTypeA [] op (LMonoTy.mkArrow' τ argTys) := by
  sorry

/-! ## `callOfLFunc` output type and denotation -/

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

private theorem denote_app_chain
    {e : LExpr T.mono} {τ : LMonoTy}
    {op : LExpr T.mono} {args : List (LExpr T.mono)}
    {argTys : List LMonoTy}
    (h_e : LExpr.HasTypeA [] e τ)
    (h_chain : getLFuncCall e = (op, args))
    (h_op : LExpr.HasTypeA [] op (LMonoTy.mkArrow' τ argTys))
    (h_args : List.Forall₂ (LExpr.HasTypeA []) args argTys)
    : let inputSorts := argTys.map (LMonoTy.substTyVars vt)
      let h_eq := substTyVars_mkArrow' vt τ argTys
      LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h_e =
      SortDenote.applyArgs tcInterp
        (h_eq ▸ LExpr.denote tcInterp opInterp fvarVal vt .nil op (LMonoTy.mkArrow' τ argTys) h_op)
        (denoteArgs tcInterp opInterp fvarVal vt .nil args argTys h_args) := by
  sorry

theorem callOfLFunc_output_type
    {F : @Factory T}
    {e : LExpr T.mono} {τ : LMonoTy}
    {callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    (h : LExpr.HasTypeA [] e τ)
    : ∃ argTys ty_op m name,
        callee = .op m name (some ty_op) ∧
        List.Forall₂ (LExpr.HasTypeA []) args argTys ∧
        ty_op = LMonoTy.mkArrow' τ argTys ∧
        args.length = fn.inputs.length := by
  sorry

/-- The denotation of a factory function call equals `opInterp` applied to the
denotations of the arguments. The `name` here is the identifier from the `.op`
node (not `fn.name`), matching what `denote_op` produces. -/
theorem callOfLFunc_denote
    {F : @Factory T}
    {e : LExpr T.mono} {τ : LMonoTy}
    {callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    (h : LExpr.HasTypeA [] e τ)
    : ∃ (argTys : List LMonoTy) (ty_op : LMonoTy) (m : T.mono.base.Metadata)
        (name : Identifier T.IDMeta)
        (h_args : List.Forall₂ (LExpr.HasTypeA []) args argTys)
        (hty_op: ty_op = LMonoTy.mkArrow' τ argTys),
        callee = .op m name (some ty_op) ∧
        let h_eq : LMonoTy.substTyVars vt ty_op =
              LSort.mkArrow (LMonoTy.substTyVars vt τ) (argTys.map (LMonoTy.substTyVars vt)) :=
            hty_op ▸ substTyVars_mkArrow' vt τ argTys
        LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h =
          SortDenote.applyArgs tcInterp
            (h_eq ▸ opInterp name.name (LMonoTy.substTyVars vt ty_op))
            (denoteArgs tcInterp opInterp fvarVal vt .nil args argTys h_args) := by
  sorry

/-! ## `subst` / `mkArrow'` structural lemmas -/

/-- `subst` distributes over `mkArrow'`. -/
theorem subst_mkArrow' (S : Subst) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.subst S (LMonoTy.mkArrow' ret ins) =
    LMonoTy.mkArrow' (LMonoTy.subst S ret) (ins.map (LMonoTy.subst S)) := by
  sorry

/-- `mkArrow'` is injective when the argument lists have equal length. -/
theorem mkArrow'_injective {ret₁ ret₂ : LMonoTy} {ins₁ ins₂ : List LMonoTy}
    (h_len : ins₁.length = ins₂.length)
    (h : LMonoTy.mkArrow' ret₁ ins₁ = LMonoTy.mkArrow' ret₂ ins₂)
    : ret₁ = ret₂ ∧ ins₁ = ins₂ := by
  sorry

/-- If `getFactoryLFunc` finds a function, its name matches the query. -/
theorem getFactoryLFunc_name {F : @Factory T} {s : String} {fn : LFunc T}
    (h : Factory.getFactoryLFunc F s = some fn) : fn.name.name = s := by
  sorry

/-- `callOfLFunc` ensures the number of args equals the number of inputs. -/
theorem callOfLFunc_arity
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : args.length = fn.inputs.length := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

/-- `callOfLFunc` ensures `fn ∈ F`. -/
theorem callOfLFunc_mem
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : fn ∈ F := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  rename_i hget hlen
  unfold Factory.getFactoryLFunc at hget
  grind

/-- The callee of `callOfLFunc` is an `.op` whose name resolves to `fn` via `getFactoryLFunc`. -/
theorem callOfLFunc_getFactoryLFunc
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∃ m name ty, callee = .op m name ty ∧ F.getFactoryLFunc name.name = some fn := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

-- /-- `OpsConsistent` propagates to the callee of a `callOfLFunc` decomposition. -/
-- theorem OpsConsistent_callOfLFunc_callee
--     {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
--     (hOps : OpsConsistent F e)
--     (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
--     : OpsConsistent F callee := by
--   sorry

/-- Extract the top-level `callOfLFunc` consistency from `OpsConsistent`. -/
theorem OpsConsistent_callOfLFunc
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hOps : OpsConsistent F e)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∃ tySubst,
        LFunc.computeTypeSubst fn callee args = some tySubst ∧
        ∀ m name ty_op, callee = .op m name (some ty_op) →
          ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst := by
  sorry

/-! ## `applySubst` lemmas -/

/-- If all scopes in `S` are empty, then `S.find?` returns `none` for any key. -/
theorem Subst.find?_hasEmptyScopes (h : Subst.hasEmptyScopes S) (x : TyIdentifier) :
    Maps.find? S x = none := by
  sorry

/-- `applySubst` preserves typing, mapping types through `subst S`. -/
theorem applySubst_typeCheck (S : Subst)
    {e : LExpr T.mono} {τ : LMonoTy} {Δ : List LMonoTy}
    (h : LExpr.HasTypeA Δ e τ)
    : LExpr.HasTypeA (Δ.map (LMonoTy.subst S)) (e.applySubst S) (LMonoTy.subst S τ) := by
  sorry

/-- `applySubst` transforms `fvars_annotated_by` consistently. -/
theorem applySubst_fvars_annotated [DecidableEq T.IDMeta] {S : Subst}
    {e : LExpr T.mono} {tyMap : Map T.Identifier LMonoTy}
    (h : fvars_annotated_by tyMap e)
    : fvars_annotated_by (tyMap.map (fun (k, v) => (k, LMonoTy.subst S v))) (e.applySubst S) := by
  sorry

/-- `denote` is invariant under changing the type index by an equality proof. -/
private theorem denote_cast_ty {Δ : List LMonoTy} {e : LExpr T.mono} {τ₁ τ₂ : LMonoTy}
    (h_eq : τ₁ = τ₂) (h₁ : LExpr.HasTypeA Δ e τ₁) (h₂ : LExpr.HasTypeA Δ e τ₂)
    (bv : BVarVal tcInterp vt Δ)
    : LExpr.denote tcInterp opInterp fvarVal vt bv e τ₁ h₁ =
      cast (congrArg (TyDenote tcInterp vt) h_eq.symm)
        (LExpr.denote tcInterp opInterp fvarVal vt bv e τ₂ h₂) := by
  subst h_eq; rfl
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
  -- Now the goal is in terms of replaceUserProvidedType
  -- Induction on e, generalizing Δ, τ, bvarVal, bvarVal', h_bvar_compat, h_body, h_subst, h_td
  revert Δ τ bvarVal bvarVal' h_bvar_compat h_body h_subst h_td
  induction e with
  | const m c =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    rw [denote_const, denote_const]
    have h_inv := HasTypeA.const_inv h_body      -- c.ty = τ
    subst h_inv
    have h_inv_s := HasTypeA.const_inv h_subst  -- c.ty = LMonoTy.subst S c.ty
    -- Both ▸ are now from c.ty = c.ty (RHS) and c.ty = subst S c.ty (LHS)
    -- Use denoteConst_cast_vt to relate denoteConst at vt vs vt'
    rw [denoteConst_cast_vt (tcInterp := tcInterp) vt vt' c]
    · -- Main goal: cast h_td (... ▸ cast ? (denoteConst vt' c)) = ... ▸ denoteConst vt' c
      -- All casts compose to identity since both sides are denoteConst vt' c
      grind
    · -- Side goal: TyDenote vt' c.ty = TyDenote vt c.ty
      exact (h_inv_s ▸ h_td).symm
  | op m o uty =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType, Option.map] at h_subst ⊢
    cases uty with
    | none => exact absurd h_body (by intro h; cases h)
    | some ty =>
      rw [denote_op, denote_op]
      have h_inv := HasTypeA.op_inv h_body      -- ty = τ
      subst h_inv
      -- Goal: cast h_td (⋯ ▸ opInterp o.name (substTyVars vt (subst S ty))) = ⋯ ▸ opInterp o.name (substTyVars vt' ty)
      have h_sorts : LMonoTy.substTyVars vt (LMonoTy.subst S τ) = LMonoTy.substTyVars vt' τ :=
        hvt' ▸ substTyVars_subst vt S τ
      grind
  | bvar m i =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    rw [denote_bvar, denote_bvar]
    have hb := HasTypeA.bvar_inv h_body   -- Δ[i]? = some τ
    have hb' := HasTypeA.bvar_inv h_subst -- (Δ.map (subst S))[i]? = some (subst S τ)
    have h_compat := h_bvar_compat i τ hb hb'
    -- h_compat : cast (congrArg SortDenote (hvt' ▸ substTyVars_subst vt S τ)) (bvarVal.get i hb') = bvarVal'.get i hb
    -- Goal: cast h_td (bvarVal.get i hb') = bvarVal'.get i hb
    -- Both casts are on the same value with proofs of the same type equality, so they agree
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
      have := h_subst_arrow ▸ h_eq_s; cases this; rfl
    subst h_rty_s
    -- Use denote_cast_ty to convert type index, then denote_abs on both sides
    have h_subst' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.abs m name (some (LMonoTy.subst S aty)) (body.replaceUserProvidedType (LMonoTy.subst S)))
        ((LMonoTy.subst S aty).arrow (LMonoTy.subst S rty)) :=
      h_subst_arrow ▸ h_subst
    simp only [Option.map] at *
    -- Fix h_subst: normalize Option.map to some
    change LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (.abs m name (some (LMonoTy.subst S aty)) (body.replaceUserProvidedType (LMonoTy.subst S)))
        (LMonoTy.subst S (aty.arrow rty)) at h_subst
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_subst_arrow h_subst h_subst' bvarVal]
    rw [denote_abs bvarVal h_body_s h_subst', denote_abs bvarVal' h_body' h_body]
    simp only [cast_cast]
    -- Decompose cast through arrow type
    have h_td_aty : TyDenote tcInterp vt (LMonoTy.subst S aty) = TyDenote tcInterp vt' aty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S aty)
    have h_td_rty : TyDenote tcInterp vt (LMonoTy.subst S rty) = TyDenote tcInterp vt' rty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S rty)
    funext y
    -- cast (A → B = A' → B') f y = cast (B = B') (f (cast (A = A').symm y))
    have h_fn_eq : (TyDenote tcInterp vt (LMonoTy.subst S aty) → TyDenote tcInterp vt (LMonoTy.subst S rty)) =
        (TyDenote tcInterp vt' aty → TyDenote tcInterp vt' rty) := by
      rw [h_td_aty, h_td_rty]
    have h_cast_fn := cast_fn_apply h_fn_eq h_td_aty h_td_rty
        (fun x => LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal)
          (body.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S rty) h_body_s) y
    rw [h_cast_fn]
    -- Apply IH with extended bvar context
    apply ih h_body' h_td_rty
    exact bvar_compat_cons (tcInterp := tcInterp) hvt' h_bvar_compat y h_td_aty
  | app m fn arg ih_fn ih_arg =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h_body
    have ⟨aty_s, h_fn_s, h_arg_s⟩ := HasTypeA.app_inv h_subst
    rw [denote_app bvarVal h_fn_s h_arg_s, denote_app bvarVal' h_fn h_arg]
    -- Need aty_s = subst S aty to apply IHs
    have h_subst_arrow : LMonoTy.subst S (aty.arrow τ) = (LMonoTy.subst S aty).arrow (LMonoTy.subst S τ) :=
      LMonoTy.subst_tcons_pair S "arrow" aty τ
    have h_aty_s : aty_s = LMonoTy.subst S aty := by
      have h_fn_s' := applySubst_typeCheck S h_fn
      rw [LExpr.applySubst_eq_replaceUserProvidedType, h_subst_arrow] at h_fn_s'
      have := HasTypeA_unique h_fn_s h_fn_s'
      cases this; rfl
    subst h_aty_s
    -- TyDenote equalities from substTyVars_subst
    have h_td_fn : TyDenote tcInterp vt ((LMonoTy.subst S aty).arrow (LMonoTy.subst S τ)) =
                   TyDenote tcInterp vt' (aty.arrow τ) :=
      h_subst_arrow ▸ congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S (aty.arrow τ))
    have h_td_arg : TyDenote tcInterp vt (LMonoTy.subst S aty) = TyDenote tcInterp vt' aty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S aty)
    rw [← cast_app h_td_fn h_td_arg h_td]
    -- Goal: (cast h_td_fn (denote fn ((subst S aty).arrow (subst S τ)) h_fn_s))
    --         (cast h_td_arg (denote arg (subst S aty) h_arg_s))
    --       = (denote fn (aty.arrow τ) h_fn) (denote arg aty h_arg)
    -- Use denote_cast_ty to convert denote fn from (subst S aty).arrow (subst S τ) to subst S (aty.arrow τ)
    have h_fn_s' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (fn.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S (aty.arrow τ)) :=
      h_subst_arrow ▸ h_fn_s
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_subst_arrow.symm h_fn_s h_fn_s' bvarVal]
    -- Now the two casts on fn compose, and ih_fn / ih_arg apply
    simp only [cast_cast]
    -- Goal: cast _ (denote fn (subst S (aty.arrow τ)) h_fn_s') (cast h_td_arg (denote arg ...)) = ...
    have h_td_fn' : TyDenote tcInterp vt (LMonoTy.subst S (aty.arrow τ)) = TyDenote tcInterp vt' (aty.arrow τ) :=
      h_subst_arrow ▸ h_td_fn
    have h_ih_fn := ih_fn h_fn h_td_fn' h_bvar_compat h_fn_s'
    have h_ih_arg := ih_arg h_arg h_td_arg h_bvar_compat h_arg_s
    rw [h_ih_arg, h_ih_fn]
  | ite m c t e ih_c ih_t ih_e =>
    intro Δ τ h_body h_td bvarVal bvarVal' h_bvar_compat h_subst
    simp only [LExpr.replaceUserProvidedType] at h_subst ⊢
    have ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h_body
    have ⟨h_c_s, h_t_s, h_e_s⟩ := HasTypeA.ite_inv h_subst
    rw [denote_ite bvarVal h_c_s h_t_s h_e_s, denote_ite bvarVal' h_c h_t h_e]
    -- Use IH on c to relate conditions. h_c_s is at .bool, need subst S .bool version.
    have h_subst_bool : LMonoTy.subst S .bool = .bool := LMonoTy.subst_bool S
    have h_c_s' : LExpr.HasTypeA (Δ.map (LMonoTy.subst S))
        (c.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S .bool) :=
      h_subst_bool.symm ▸ h_c_s
    have h_td_bool : TyDenote tcInterp vt (LMonoTy.subst S .bool) = TyDenote tcInterp vt' .bool :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S .bool)
    have h_ih_c := ih_c h_c h_td_bool h_bvar_compat h_c_s'
    -- h_ih_c relates denote at (subst S .bool), but goal has denote at .bool
    -- Use denote_cast_ty to connect them
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
      have := applySubst_typeCheck S h_1
      rw [LExpr.applySubst_eq_replaceUserProvidedType] at this
      exact HasTypeA_unique h_1_s this
    subst h_ty_s
    have h_td_ty : TyDenote tcInterp vt (LMonoTy.subst S ty') = TyDenote tcInterp vt' ty' :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S ty')
    have h_ih1 := ih1 h_1 h_td_ty h_bvar_compat h_1_s
    have h_ih2 := ih2 h_2 h_td_ty h_bvar_compat h_2_s
    -- The LHS denote is at subst S .bool. Need to convert to .bool for denote_eq_true/false.
    -- Use h_τ_s to rewrite h_subst, then denote_cast_ty to relate the denote values.
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
    -- Fix Option.map and convert type index
    simp only [Option.map] at *
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
    -- Now both sides are at .bool. Need h_td_qty for the binder type.
    have h_td_qty : TyDenote tcInterp vt (LMonoTy.subst S qty) = TyDenote tcInterp vt' qty :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S qty)
    have h_td_bool : TyDenote tcInterp vt (LMonoTy.subst S .bool) = TyDenote tcInterp vt' .bool :=
      congrArg (SortDenote tcInterp) (hvt' ▸ substTyVars_subst vt S .bool)
    simp only [cast_cast]
    -- h_body_q_s needs context and type adjustment for IH
    have h_body_q_s' : LExpr.HasTypeA ((qty :: Δ).map (LMonoTy.subst S))
        (body.replaceUserProvidedType (LMonoTy.subst S)) (LMonoTy.subst S .bool) := by grind
    -- Both sides at .bool. Case split on quantifier kind.
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
    : cast h_td
        (LExpr.denote tcInterp opInterp fvarVal vt .nil (e.applySubst S) (LMonoTy.subst S τ) h_subst) =
      LExpr.denote tcInterp opInterp fvarVal vt' .nil e τ h_body :=
  denote_applySubst_gen tcInterp opInterp fvarVal hvt' h_body h_subst h_td
    (bvarVal := .nil) (bvarVal' := .nil)
    (fun i _ hb _ => absurd hb (by simp))

end Lambda

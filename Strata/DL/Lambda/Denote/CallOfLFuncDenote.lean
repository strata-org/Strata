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

/-- Every `.op` annotation in `e` is a valid instantiation of the corresponding
factory function's polymorphic type. -/
def OpsConsistent (F : @Factory T) : LExpr T.mono → Prop
  | .op _ name (some ty_op) =>
    match F.getFactoryLFunc name.name with
    | some fn => ∃ σ : Map TyIdentifier LMonoTy,
        ty_op = LMonoTy.substMap σ (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
    | none => True
  | .op _ _ none => True
  | .const _ _ => True
  | .bvar _ _ => True
  | .fvar _ _ _ => True
  | .app _ fn arg => OpsConsistent F fn ∧ OpsConsistent F arg
  | .abs _ _ _ body => OpsConsistent F body
  | .ite _ c t e => OpsConsistent F c ∧ OpsConsistent F t ∧ OpsConsistent F e
  | .eq _ e1 e2 => OpsConsistent F e1 ∧ OpsConsistent F e2
  | .quant _ _ _ _ tr body => OpsConsistent F tr ∧ OpsConsistent F body

/-! ## `substTyVars` commutation lemmas -/

theorem substTyVars_mkArrow' (vt : TyVarVal) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.mkArrow' ret ins) =
    LSort.mkArrow (LMonoTy.substTyVars vt ret) (ins.map (LMonoTy.substTyVars vt)) := by
  sorry

theorem substTyVars_substMap (vt : TyVarVal) (σ : Map TyIdentifier LMonoTy) (ty : LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.substMap σ ty) =
    LMonoTy.substTyVars
      (fun x => match Map.find? σ x with | some t => LMonoTy.substTyVars vt t | none => vt x)
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

/-! ## `substMap` / `mkArrow'` structural lemmas -/

/-- `substMap` distributes over `mkArrow'`. -/
theorem substMap_mkArrow' (σ : Map TyIdentifier LMonoTy) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.substMap σ (LMonoTy.mkArrow' ret ins) =
    LMonoTy.mkArrow' (LMonoTy.substMap σ ret) (ins.map (LMonoTy.substMap σ)) := by
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

/-- `OpsConsistent` propagates to the callee of a `callOfLFunc` decomposition. -/
theorem OpsConsistent_callOfLFunc_callee
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hOps : OpsConsistent F e)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : OpsConsistent F callee := by
  sorry

end Lambda

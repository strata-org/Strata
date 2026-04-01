/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote

namespace Lambda

/-! ## `LMonoTy.substMap` — clean type-variable substitution for proofs -/

/-- Apply a simple type-variable substitution (a `Map`) to a monomorphic type.
Unlike `LMonoTy.subst` (which uses multi-scope `Subst` with `hasEmptyScopes`
guard), this is clean for equational reasoning. -/
def LMonoTy.substMap (σ : Map TyIdentifier LMonoTy) : LMonoTy → LMonoTy
  | .ftvar x    => (σ.find? x).getD (.ftvar x)
  | .bitvec n   => .bitvec n
  | .tcons name args => .tcons name (args.map (substMap σ))

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

/-! ## `substMap` inversion through `mkArrow'` -/

/-- `OpsConsistent` propagates to the callee of a `callOfLFunc` decomposition. -/
theorem OpsConsistent_callOfLFunc_callee
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hOps : OpsConsistent F e)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : OpsConsistent F callee := by
  sorry

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst

/-!
## Factory Function Call Denotation

Properties of `callOfLFunc` (factory function applications). Defines
`OpsConsistent` (operation type annotations are valid) and proves that
denotation of a factory call equals `opInterp` applied to argument denotations.

- `OpsConsistent` — every call has a valid type substitution and consistent `.op` annotation
- `callOfLFunc_denote` — denotation of a factory call equals `opInterp` applied to args
-/

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
   | some (callee, _, fn) =>
       match LFunc.opTypeSubst fn callee with
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

/-- `OpsConsistent` is preserved by `substK` when substituting a free variable.
This could be generalized to arbitrary `s` with the assumption that `s` does not
produce `.app` or `.op` nodes (needed so `getLFuncCall` commutation holds). -/
theorem OpsConsistent_substK_fvar
    {F : @Factory T} {k : Nat}
    {x : Identifier T.IDMeta × Option T.mono.TypeType}
    {e : LExpr T.mono}
    (h : OpsConsistent F e)
    : OpsConsistent F (LExpr.substK k (fun m => .fvar m x.fst x.snd) e) := by
  induction e generalizing k with
  | const => simp only [LExpr.substK]; exact h
  | op => simp only [LExpr.substK]; exact h
  | fvar => simp only [LExpr.substK]; exact h
  | bvar m i =>
    simp only [LExpr.substK]
    split
    · unfold OpsConsistent; simp [callOfLFunc_fvar]
    · exact h
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.substK]
    have hcall := Factory.callOfLFunc_substK_fvar (F := F) (k := k) (x := x) (e := .app m e1 e2)
    simp only at hcall
    simp only [LExpr.substK] at hcall
    constructor
    · -- callOfLFunc conjunct
      cases heq : F.callOfLFunc (.app m e1 e2) with
      | none =>
        simp only [heq] at hcall
        rw [hcall]; trivial
      | some val =>
        obtain ⟨callee, args, fn⟩ := val
        simp only [heq] at hcall
        rw [hcall]
        have h1 := h.1
        simp only [heq] at h1
        simp only []
        exact h1
    · exact ⟨ih1 h.2.1, ih2 h.2.2⟩
  | abs m name ty body ih =>
    simp only [LExpr.substK]
    unfold OpsConsistent
    simp only [callOfLFunc_abs]
    exact ⟨trivial, ih h.2⟩
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substK]
    unfold OpsConsistent
    simp only [callOfLFunc_ite]
    exact ⟨trivial, ihc h.2.1, iht h.2.2.1, ihf h.2.2.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substK]
    unfold OpsConsistent
    simp only [callOfLFunc_eq_]
    exact ⟨trivial, ih1 h.2.1, ih2 h.2.2⟩
  | quant m qk name ty tr body ihtr ihbody =>
    simp only [LExpr.substK]
    unfold OpsConsistent
    simp only [callOfLFunc_quant]
    exact ⟨trivial, ihtr h.2.1, ihbody h.2.2⟩

/-- `OpsConsistent` is preserved by `varOpen`. -/
theorem OpsConsistent_varOpen
    {F : @Factory T} {k : Nat}
    {x : Identifier T.IDMeta × Option T.mono.TypeType}
    {e : LExpr T.mono}
    (h : OpsConsistent F e)
    : OpsConsistent F (LExpr.varOpen k x e) := by
  unfold LExpr.varOpen
  exact OpsConsistent_substK_fvar h

/-- Every element of the args list returned by `getLFuncCall.go` inherits `OpsConsistent`
from the input expression and accumulator. -/
private theorem getLFuncCall_go_OpsConsistent
    {F : @Factory T} {e : LExpr T.mono} {acc : List (LExpr T.mono)}
    (hOps : OpsConsistent F e)
    (hacc : ∀ a ∈ acc, OpsConsistent F a)
    : ∀ a ∈ (getLFuncCall.go e acc).2, OpsConsistent F a := by
  fun_induction getLFuncCall.go e acc with
  | case1 m m' e' arg1 arg2 acc ih =>
    -- e = .app m' (.app e' arg1 arg2) acc, accumulator is m
    have hOps_arg1 := hOps.2.1.2.1
    have hOps_arg2 := hOps.2.1.2.2
    have hOps_acc := hOps.2.2
    have hacc' : ∀ a ∈ [arg2, acc] ++ m, OpsConsistent F a := by
      simp only [List.cons_append, List.mem_cons, List.mem_append]
      intro a ha
      rcases ha with rfl | rfl | hmem
      · exact hOps_arg2
      · exact hOps_acc
      · exact hacc a (by grind)
    exact ih hOps_arg1 hacc'
  | case2 m m' fn fnty arg1 acc =>
    simp only [List.cons_append, List.mem_cons, List.mem_append]
    intro a ha
    cases ha with
    | inl heq => rw [heq]; exact hOps.2.2
    | inr hmem => exact hacc a (by grind)
  | case3 e acc => exact hacc

/-- Every argument of a `callOfLFunc` call inherits `OpsConsistent`. -/
theorem OpsConsistent_callOfLFunc_args
    {F : @Factory T} {e callee : LExpr T.mono}
    {args : List (LExpr T.mono)} {fn : LFunc T}
    (hOps : OpsConsistent F e)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∀ a ∈ args, OpsConsistent F a := by
  have hgl := callOfLFunc_getLFuncCall hcall
  have hargs : args = (getLFuncCall.go e []).2 := by
    simp only [getLFuncCall] at hgl; rw [hgl]
  rw [hargs]
  exact getLFuncCall_go_OpsConsistent hOps (by simp)

/-! ## `getLFuncCall` typing and denotation -/

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
  fun_induction getLFuncCall.go e acc generalizing τ accTys
  · -- case 1: .app _ (.app _ e' arg1) arg2 → go e' ([arg1, arg2] ++ acc)
    rename_i ih
    have ⟨aty2, h_inner, h_arg2⟩ := HasTypeA.app_inv h_e
    have ⟨aty1, h_e', h_arg1⟩ := HasTypeA.app_inv h_inner
    rw [← LMonoTy.mkArrow'_cons, ← LMonoTy.mkArrow'_cons] at h_e'
    exact ih h_e' (.cons h_arg1 (.cons h_arg2 h_acc))
  · -- case 2: .app _ (.op m fn fnty) arg1 → (.op m fn fnty, [arg1] ++ acc)
    have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h_e
    exact ⟨aty :: accTys, .cons h_arg h_acc, LMonoTy.mkArrow'_cons .. ▸ h_fn⟩
  · -- case 3: other → (e, acc)
    exact ⟨accTys, h_acc, h_e⟩

theorem getLFuncCall_spec
    {T : LExprParams}
    {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] e τ)
    : let (op, args) := getLFuncCall e
      ∃ argTys,
        List.Forall₂ (LExpr.HasTypeA []) args argTys ∧
        LExpr.HasTypeA [] op (LMonoTy.mkArrow' τ argTys) := by
  have h' : LExpr.HasTypeA [] e (LMonoTy.mkArrow' τ []) := by rw [LMonoTy.mkArrow'_nil]; exact h
  exact getLFuncCall_go_spec h' .nil

/-! ## `callOfLFunc` output type and denotation -/

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

private theorem applyArgs_cons {ret : LSort} {s : LSort} {ss : List LSort}
    (f : SortDenote tcInterp (LSort.mkArrow ret (s :: ss)))
    (x : SortDenote tcInterp s) (xs : HList (SortDenote tcInterp) ss)
    : SortDenote.applyArgs tcInterp f (.cons x xs) = SortDenote.applyArgs tcInterp (f x) xs := by
  rfl

private theorem denoteArgs_cons
    {Δ : List LMonoTy} (bv : BVarVal tcInterp vt Δ)
    {e : LExpr T.mono} {es : List (LExpr T.mono)}
    {ty : LMonoTy} {tys : List LMonoTy}
    (h : List.Forall₂ (LExpr.HasTypeA Δ) (e :: es) (ty :: tys))
    : denoteArgs tcInterp opInterp fvarVal vt bv (e :: es) (ty :: tys) h =
      .cons (LExpr.denote tcInterp opInterp fvarVal vt bv e ty h.head)
            (denoteArgs tcInterp opInterp fvarVal vt bv es tys h.tail) := by
  rfl

/-- Key cast-composition lemma for denote_app_chain_go case 1.
    Peeling two args off a cast-wrapped function: casting to arrow form, applying
    two args, then casting result to mkArrow form = casting directly to full
    mkArrow form and applying two args via applyArgs. -/
private theorem applyArgs_cast_peel_two
    {s : LSort} {s1 s2 r : LSort} {ss : List LSort}
    (f : SortDenote tcInterp s)
    (h_arrow : s = .tcons "arrow" [s1, .tcons "arrow" [s2, r]])
    (h_small : r = LSort.mkArrow ret ss)
    (h_full : s = LSort.mkArrow ret (s1 :: s2 :: ss))
    (x : SortDenote tcInterp s1)
    (y : SortDenote tcInterp s2)
    (rest : HList (SortDenote tcInterp) ss)
    : SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) h_small) ((cast (congrArg (SortDenote tcInterp) h_arrow) f) x y))
        rest =
      SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) h_full) f)
        (.cons x (.cons y rest)) := by
  subst h_arrow; subst h_small
  simp only [cast_eq] at *
  cases h_full
  rfl

/-- One-arg version of applyArgs_cast_peel_two, for case 2. -/
private theorem applyArgs_cast_peel_one
    {s : LSort} {s1 r : LSort} {ss : List LSort}
    (f : SortDenote tcInterp s)
    (h_arrow : s = .tcons "arrow" [s1, r])
    (h_small : r = LSort.mkArrow ret ss)
    (h_full : s = LSort.mkArrow ret (s1 :: ss))
    (x : SortDenote tcInterp s1)
    (rest : HList (SortDenote tcInterp) ss)
    : SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) h_small) ((cast (congrArg (SortDenote tcInterp) h_arrow) f) x))
        rest =
      SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) h_full) f)
        (.cons x rest) := by
  subst h_arrow; subst h_small
  simp only [cast_eq] at *
  cases h_full
  rfl

private theorem denote_app_chain_go
    {e : LExpr T.mono} {τ : LMonoTy}
    {acc : List (LExpr T.mono)} {accTys : List LMonoTy}
    (h_e : LExpr.HasTypeA [] e (LMonoTy.mkArrow' τ accTys))
    (h_acc : List.Forall₂ (LExpr.HasTypeA []) acc accTys)
    {op : LExpr T.mono} {allArgs : List (LExpr T.mono)}
    (h_go : getLFuncCall.go e acc = (op, allArgs))
    {opArgTys : List LMonoTy}
    (h_op : LExpr.HasTypeA [] op (LMonoTy.mkArrow' τ opArgTys))
    (h_allArgs : List.Forall₂ (LExpr.HasTypeA []) allArgs opArgTys)
    : SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) (substTyVars_mkArrow' vt τ accTys))
          (LExpr.denote tcInterp opInterp fvarVal vt .nil e (LMonoTy.mkArrow' τ accTys) h_e))
        (denoteArgs tcInterp opInterp fvarVal vt .nil acc accTys h_acc) =
      SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) (substTyVars_mkArrow' vt τ opArgTys))
          (LExpr.denote tcInterp opInterp fvarVal vt .nil op (LMonoTy.mkArrow' τ opArgTys) h_op))
        (denoteArgs tcInterp opInterp fvarVal vt .nil allArgs opArgTys h_allArgs) := by
  fun_induction getLFuncCall.go e acc generalizing τ accTys opArgTys
  · -- case 1: .app _ (.app _ e' arg1) arg2 → go e' ([arg1, arg2] ++ acc)
    rename_i acc0 m1 m2 e' arg1 arg2 ih
    -- Step 1: app_inv twice
    have ⟨aty2, h_inner, h_arg2⟩ := HasTypeA.app_inv h_e
    have ⟨aty1, h_e'_orig, h_arg1⟩ := HasTypeA.app_inv h_inner
    -- Step 2: mkArrow'_cons twice
    have h_e' := h_e'_orig
    rw [← LMonoTy.mkArrow'_cons, ← LMonoTy.mkArrow'_cons] at h_e'
    -- Step 3: build extended Forall₂
    have h_acc' : List.Forall₂ (LExpr.HasTypeA []) ([arg1, arg2] ++ acc0) (aty1 :: aty2 :: accTys) :=
      .cons h_arg1 (.cons h_arg2 h_acc)
    -- Step 4: apply IH, reduce to showing LHS = LHS-of-IH
    rw [← ih h_e' h_acc' h_go h_op h_allArgs]
    -- Step 5: denote_app twice
    rw [denote_app .nil h_inner h_arg2, denote_app .nil h_e'_orig h_arg1]
    -- Step 6: denote_cast_ty to relate denote e' at arrow type vs mkArrow' type
    have h_ty_eq : LMonoTy.mkArrow' τ (aty1 :: aty2 :: accTys) =
        LMonoTy.arrow aty1 (LMonoTy.arrow aty2 (LMonoTy.mkArrow' τ accTys)) := by
      rw [LMonoTy.mkArrow'_cons, LMonoTy.mkArrow'_cons]
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_ty_eq.symm h_e'_orig h_e' .nil]
    -- Step 7: simplify [arg1, arg2] ++ acc0 to arg1 :: arg2 :: acc0, then denoteArgs_cons twice
    simp only [List.cons_append, List.nil_append] at h_acc' ⊢
    rw [denoteArgs_cons (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt) .nil h_acc']
    rw [denoteArgs_cons (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt) .nil h_acc'.tail]
    -- Step 10: applyArgs_cast_peel_two
    have h_arrow : LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ (aty1 :: aty2 :: accTys)) =
        .tcons "arrow" [LMonoTy.substTyVars vt aty1,
          .tcons "arrow" [LMonoTy.substTyVars vt aty2, LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ accTys)]] := by
      rw [LMonoTy.mkArrow'_cons, LMonoTy.mkArrow'_cons]; rfl
    exact applyArgs_cast_peel_two tcInterp _
      h_arrow (substTyVars_mkArrow' vt τ accTys) (substTyVars_mkArrow' vt τ (aty1 :: aty2 :: accTys)) _ _ _
  · -- case 2: .app _ (.op m fn fnty) arg1 → (.op m fn fnty, [arg1] ++ acc)
    rename_i acc0 m1 m2 fn fnty arg1
    cases h_go
    -- app_inv
    have ⟨aty1, h_op_orig, h_arg1⟩ := HasTypeA.app_inv h_e
    -- mkArrow'_cons to get h_op at mkArrow' form
    have h_op' := h_op_orig
    rw [← LMonoTy.mkArrow'_cons] at h_op'
    -- Unify opArgTys with aty1 :: accTys
    have h_unique := HasTypeA_unique h_op' h_op
    have hlen : (aty1 :: accTys).length = opArgTys.length := by
      simp only [List.cons_append, List.nil_append] at h_allArgs
      have := (List.Forall₂.cons h_arg1 h_acc).length_eq; have := h_allArgs.length_eq; omega
    have ⟨_, h_tys⟩ := LMonoTy.mkArrow'_injective hlen h_unique
    subst h_tys
    -- denote_app
    rw [denote_app .nil h_op_orig h_arg1]
    -- denote_cast_ty
    have h_ty_eq : LMonoTy.mkArrow' τ (aty1 :: accTys) =
        LMonoTy.arrow aty1 (LMonoTy.mkArrow' τ accTys) := by
      rw [LMonoTy.mkArrow'_cons]
    rw [denote_cast_ty (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt)
        h_ty_eq.symm h_op_orig h_op' .nil]
    -- denoteArgs_cons on RHS
    simp only [List.cons_append, List.nil_append] at h_allArgs ⊢
    rw [denoteArgs_cons (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt) .nil h_allArgs]
    -- applyArgs_cast_peel_one
    have h_arrow : LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ (aty1 :: accTys)) =
        .tcons "arrow" [LMonoTy.substTyVars vt aty1, LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ accTys)] := by
      rw [LMonoTy.mkArrow'_cons]; rfl
    exact applyArgs_cast_peel_one tcInterp _
      h_arrow (substTyVars_mkArrow' vt τ accTys) (substTyVars_mkArrow' vt τ (aty1 :: accTys)) _ _
  · -- case 3: other → (e, acc)
    cases h_go
    have h_eq := HasTypeA_unique h_e h_op
    have hlen : accTys.length = opArgTys.length := by
      have := h_acc.length_eq; have := h_allArgs.length_eq; omega
    have ⟨_, h_tys⟩ := LMonoTy.mkArrow'_injective hlen h_eq
    subst h_tys; rfl

private theorem denote_app_chain
    {e : LExpr T.mono} {τ : LMonoTy}
    {op : LExpr T.mono} {args : List (LExpr T.mono)}
    {argTys : List LMonoTy}
    (h_e : LExpr.HasTypeA [] e τ)
    (h_chain : getLFuncCall e = (op, args))
    (h_op : LExpr.HasTypeA [] op (LMonoTy.mkArrow' τ argTys))
    (h_args : List.Forall₂ (LExpr.HasTypeA []) args argTys)
    : let h_eq := substTyVars_mkArrow' vt τ argTys
      LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h_e =
      SortDenote.applyArgs tcInterp
        (h_eq ▸ LExpr.denote tcInterp opInterp fvarVal vt .nil op (LMonoTy.mkArrow' τ argTys) h_op)
        (denoteArgs tcInterp opInterp fvarVal vt .nil args argTys h_args) := by
  have h_e' : LExpr.HasTypeA [] e (LMonoTy.mkArrow' τ []) := by
    rw [LMonoTy.mkArrow'_nil]; exact h_e
  have h_go := denote_app_chain_go tcInterp opInterp fvarVal vt h_e' .nil h_chain h_op h_args
  simp only [SortDenote.applyArgs, denoteArgs] at h_go
  -- Connect denote e τ h_e to denote e (mkArrow' τ []) h_e'
  have h_nil := LMonoTy.mkArrow'_nil τ  -- mkArrow' τ [] = τ
  have h_eq_e : LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h_e =
      cast (congrArg (TyDenote tcInterp vt) h_nil)
        (LExpr.denote tcInterp opInterp fvarVal vt .nil e (LMonoTy.mkArrow' τ []) h_e') := by grind
  rw [h_eq_e, h_go]
  grind

/-! ## `subst` / `mkArrow'` structural lemmas -/

/-- Extract the top-level `callOfLFunc` consistency from `OpsConsistent`. -/
theorem OpsConsistent_callOfLFunc
    {F : @Factory T} {e callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hOps : OpsConsistent F e)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∃ tySubst,
        LFunc.opTypeSubst fn callee = some tySubst ∧
        ∀ m name ty_op, callee = .op m name (some ty_op) →
          ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst := by
  unfold OpsConsistent at hOps
  have ⟨h1, _⟩ := hOps
  simp [hcall] at h1
  split at h1
  · next h_tySubst =>
    split at h1
    · next m name ty_op =>
      exact ⟨_, h_tySubst, fun _ _ _ h => by cases h; exact h1⟩
    · exact absurd h1 id
  · exact absurd h1 id

/-! ## `callOfLFunc` output type and denotation -/

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
  obtain ⟨m, name, ty, h_callee, h_get⟩ := Factory.callOfLFunc_getElem? hcall
  have h_chain := Factory.callOfLFunc_getLFuncCall hcall
  have h_spec := getLFuncCall_spec h
  rw [h_chain] at h_spec
  obtain ⟨argTys, h_args, h_op⟩ := h_spec
  subst h_callee
  -- ty must be `some ty_op` since HasTypeA for .op requires it
  cases ty with
  | none => exact absurd h_op (by intro h; cases h)
  | some ty_op =>
    have h_inv := HasTypeA.op_inv h_op
    exact ⟨argTys, ty_op, m, name, rfl, h_args, h_inv.symm, Factory.callOfLFunc_arity hcall⟩

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
  -- Step 1: get typing info
  obtain ⟨argTys, ty_op, m, name, h_callee, h_args, hty_op, _⟩ := callOfLFunc_output_type hcall h
  -- Step 2: get the chain equation
  have h_chain := Factory.callOfLFunc_getLFuncCall hcall
  -- Step 3: get typing of op from getLFuncCall_spec
  have h_spec := getLFuncCall_spec h
  rw [h_chain] at h_spec
  obtain ⟨argTys', h_args', h_op⟩ := h_spec
  -- argTys' = argTys (both come from the same getLFuncCall)
  -- h_op : HasTypeA [] callee (mkArrow' τ argTys')
  -- We know callee = .op m name (some ty_op) and ty_op = mkArrow' τ argTys
  subst h_callee
  have h_inv := HasTypeA.op_inv h_op  -- mkArrow' τ argTys' = ty_op
  rw [hty_op] at h_inv
  have hlen: argTys'.length = argTys.length := by
    have := h_args'.length_eq; have := h_args.length_eq; omega
  have ⟨_, h_argTys_eq⟩ := LMonoTy.mkArrow'_injective hlen h_inv
  subst h_argTys_eq
  -- Step 4: apply denote_app_chain
  have h_denote := denote_app_chain tcInterp opInterp fvarVal vt h h_chain h_op h_args'
  -- Step 5: rewrite denote of .op using denote_op
  have h_dop := denote_op tcInterp opInterp fvarVal vt .nil h_op
  refine ⟨argTys', ty_op, m, name, h_args, hty_op, rfl, ?_⟩
  rw [h_denote, h_dop]
  grind

end Lambda

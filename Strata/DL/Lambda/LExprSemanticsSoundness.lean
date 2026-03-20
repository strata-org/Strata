/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprAnnotated
import all Strata.DL.Lambda.LExprDenote
import all Strata.DL.Lambda.Semantics

namespace Lambda

variable {T : LExprParams} [DecidableEq T.Metadata] [DecidableEq T.Identifier]
    [DecidableEq T.IDMeta]
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp T tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### HList cast infrastructure -/

/-- Cast an `HList` along a proof that the index lists are equal. -/
def HList.cast {α : Type} {f : α → Type} {xs ys : List α}
    (h : xs = ys) (hlist : HList f xs) : HList f ys :=
  h ▸ hlist

@[simp] theorem HList.cast_rfl {α : Type} {f : α → Type} {xs : List α}
    (hlist : HList f xs) : HList.cast rfl hlist = hlist := rfl

@[simp] theorem HList.cast_cast {α : Type} {f : α → Type} {xs ys zs : List α}
    (h₁ : xs = ys) (h₂ : ys = zs) (hlist : HList f xs)
    : HList.cast h₂ (HList.cast h₁ hlist) = HList.cast (h₁.trans h₂) hlist := by
  subst h₁; subst h₂; rfl

/-- Casting the argument list of `applyArgs` can be absorbed by casting the
sort in the applied function. In particular, for `opInterp`-style functions
that take the sort as a parameter, this lets us move between equivalent
index representations. -/
theorem SortDenote.applyArgs_cast_eq {xs ys : List LSort} {ret : LSort}
    (h : xs = ys)
    (g : (s : LSort) → SortDenote tcInterp s)
    (args : HList (SortDenote tcInterp) xs)
    : SortDenote.applyArgs tcInterp (g (LSort.mkArrow ret xs)) args =
      SortDenote.applyArgs tcInterp (g (LSort.mkArrow ret ys)) (HList.cast h args) := by
  subst h; rfl

/-! ### Helper lemmas -/

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] in
/-- `callOfLFunc` only returns functions that are members of the factory. -/
theorem Factory.callOfLFunc_mem {F : @Factory T} {e : LExpr T.mono} {callee args fn} :
    F.callOfLFunc e = some (callee, args, fn) → fn ∈ F := by
  simp [Factory.callOfLFunc]
  cases getLFuncCall e with | mk op args' =>
  simp; cases op <;> simp
  rename_i m name ty
  cases h : F.getFactoryLFunc name.name <;> simp
  rename_i func
  cases args'.length == func.inputs.length <;> simp
  intro _ _ h_fn; subst h_fn
  exact Array.mem_of_find?_eq_some h

/-- Bound-variable substitution commutes with denotation: the denotation of
`subst (fun _ => v) body` in context `Δ` equals the denotation of `body` in
context `aty :: Δ` with bvar 0 mapped to `denote v`. -/
theorem subst_denote
    {body : LExpr T.mono} {v : LExpr T.mono}
    {aty τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (aty :: Δ) body τ)
    (h_v : LExpr.HasTypeA Δ v aty)
    (h_subst : LExpr.HasTypeA Δ (LExpr.subst (fun _ => v) body) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (LExpr.subst (fun _ => v) body)  τ h_subst =
      LExpr.denote tcInterp opInterp fvarVal vt
        (.cons (LExpr.denote tcInterp opInterp fvarVal vt bvarVal v aty h_v) bvarVal) body τ h_body := by
  sorry

/-- Free-variable substitution commutes with denotation: the denotation of
`substFvars body bindings` equals the denotation of `body` with `fvarVal`
updated to map each substituted name to the denotation of its replacement. -/
theorem substFvars_denote
    {body : LExpr T.mono} {τ : LMonoTy}
    {bindings : List (T.Identifier × LExpr T.mono)}
    {sortBindings : List (Identifier T.IDMeta × LSort)}
    (h_body : LExpr.HasTypeA [] body τ)
    (h_subst : LExpr.HasTypeA [] (LExpr.substFvars body bindings) τ)
    (h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd))
    (h_keys : bindings.map Prod.fst = sortBindings.map Prod.fst)
    (h_len : bindings.length = sortBindings.length)
    : LExpr.denote tcInterp opInterp
        (fvarVal.withArgs sortBindings h_args)
        vt .nil body τ h_body =
      LExpr.denote tcInterp opInterp fvarVal vt .nil
        (LExpr.substFvars body bindings) τ h_subst := by
  sorry

/-- For canonical values, syntactic equality (`eql`) agrees with semantic
equality under denotation. -/
theorem eql_iff_denote_eq
    {F : @Factory T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hv₁ : LExpr.isCanonicalValue F e₁)
    (hv₂ : LExpr.isCanonicalValue F e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    : LExpr.eql F e₁ e₂ hv₁ hv₂ = true ↔
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  sorry

/-- If `callOfLFunc F e = some (callee, args, fn)` and `e : τ` and `F` is
well-typed, then `τ = fn.output`. -/
theorem callOfLFunc_output_type
    {F : @Factory T}
    {e : LExpr T.mono} {τ : LMonoTy}
    {callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hFwt : Factory.WellTyped F)
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    (h : LExpr.HasTypeA [] e τ)
    : τ = fn.output := by
  sorry

/-- If `callOfLFunc F e = some (callee, args, fn)` and `e` is well-typed, then
the denotation of `e` equals `opInterp fn.name` applied to the denotations of
`args`. -/
theorem callOfLFunc_denote
    {F : @Factory T}
    {e : LExpr T.mono} {τ : LMonoTy}
    {callee : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    (h : LExpr.HasTypeA [] e τ)
    : ∃ (h_args : List.Forall₂ (LExpr.HasTypeA []) args (List.map Prod.snd fn.inputs)),
      let inputSorts := (List.map Prod.snd fn.inputs).map (LMonoTy.substTyVars vt)
      let fullSort := LSort.mkArrow (LMonoTy.substTyVars vt τ) inputSorts
      LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h =
        SortDenote.applyArgs tcInterp (opInterp fn.name fullSort)
          (denoteArgs tcInterp opInterp fvarVal vt h_args) := by
  sorry

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] in
/-- Unfolding lemma for `denote` of an application:
`denote (app m fn arg) τ h = (denote fn (arrow aty τ) h_fn) (denote arg aty h_arg)`.
Proved via `Denotes` to avoid dependent-type casts from `app_inv`. -/
theorem denote_app
    {fn arg : LExpr T.mono} {aty τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_fn : LExpr.HasTypeA Δ fn (.arrow aty τ))
    (h_arg : LExpr.HasTypeA Δ arg aty)
    (h_app : LExpr.HasTypeA Δ (.app m fn arg) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.app m fn arg) τ h_app =
      (LExpr.denote tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn)
        (LExpr.denote tcInterp opInterp fvarVal vt bvarVal arg aty h_arg) := by
  have hd_fn := denote_Denotes tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn
  have hd_arg := denote_Denotes tcInterp opInterp fvarVal vt bvarVal arg aty h_arg
  have hd_app := Denotes.app bvarVal (h := h_app) hd_fn hd_arg
  exact (Denotes_denote hd_app).symm

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] in
/-- Unfolding lemma for `denote` of an abstraction:
`denote (abs m name (some aty) body) (arrow aty rty) h = fun x => denote body rty h_body`
with `x` consed onto the bound-variable valuation.
Proved via `Denotes` to avoid dependent-type casts from `abs_inv`. -/
theorem denote_abs
    {body : LExpr T.mono} {aty rty : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (aty :: Δ) body rty)
    (h_abs : LExpr.HasTypeA Δ (.abs m name (some aty) body) (.arrow aty rty))
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.abs m name (some aty) body) (.arrow aty rty) h_abs =
      fun x => LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body := by
  have hd_body : ∀ x, Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body
      (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body) :=
    fun x => denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body
  have hd_abs := Denotes.abs bvarVal (h := h_abs) hd_body
  exact (Denotes_denote hd_abs).symm

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] in
/-- Unfolding lemma for `denote` of `eq` when operands are equal. -/
theorem denote_eq_true
    {e1 e2 : LExpr T.mono} {ty' : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_1 : LExpr.HasTypeA Δ e1 ty')
    (h_2 : LExpr.HasTypeA Δ e2 ty')
    (h_eq : LExpr.HasTypeA Δ (.eq m e1 e2) .bool)
    (heq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1 =
           LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h_eq = true := by
  have hd1 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1
  have hd2 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2
  rw [heq] at hd1
  exact (Denotes_denote (Denotes.eq_true bvarVal (h := h_eq) hd1 hd2)).symm

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] in
/-- Unfolding lemma for `denote` of `eq` when operands are not equal. -/
theorem denote_eq_false
    {e1 e2 : LExpr T.mono} {ty' : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_1 : LExpr.HasTypeA Δ e1 ty')
    (h_2 : LExpr.HasTypeA Δ e2 ty')
    (h_eq : LExpr.HasTypeA Δ (.eq m e1 e2) .bool)
    (hne : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1 ≠
           LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h_eq = false := by
  have hd1 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1
  have hd2 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2
  exact (Denotes_denote (Denotes.eq_false bvarVal (h := h_eq) hd1 hd2 hne)).symm

omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] [DecidableEq T.IDMeta] in
/-- Unfolding lemma for `denote` of an `ite`:
`denote (ite m c t e) τ h = if denote c .bool h_c then denote t τ h_t else denote e τ h_e`.
Proved via `Denotes` to avoid dependent-type casts from `ite_inv`. -/
theorem denote_ite
    {c t e : LExpr T.mono} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_c : LExpr.HasTypeA Δ c .bool)
    (h_t : LExpr.HasTypeA Δ t τ)
    (h_e : LExpr.HasTypeA Δ e τ)
    (h_ite : LExpr.HasTypeA Δ (.ite m c t e) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.ite m c t e) τ h_ite =
      bif LExpr.denote tcInterp opInterp fvarVal vt bvarVal c .bool h_c
      then LExpr.denote tcInterp opInterp fvarVal vt bvarVal t τ h_t
      else LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h_e := by
  cases hb : LExpr.denote tcInterp opInterp fvarVal vt bvarVal c .bool h_c with
  | true =>
    simp
    have hd_c := denote_Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c
    rw [hb] at hd_c
    have hd_t := denote_Denotes tcInterp opInterp fvarVal vt bvarVal t τ h_t
    have hd_ite := Denotes.ite_true bvarVal (h := h_ite) hd_c hd_t
    exact (Denotes_denote hd_ite).symm
  | false =>
    simp
    have hd_c := denote_Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c
    rw [hb] at hd_c
    have hd_e := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e τ h_e
    have hd_ite := Denotes.ite_false bvarVal (h := h_ite) hd_c hd_e
    exact (Denotes_denote hd_ite).symm

/-! ### Main theorem -/

/-- If `e₁` steps to `e₂` under a factory `F` and environment `env`, and both
are well-typed at the same type `τ`, then (given consistency of the factory and
environment with the semantic interpretations) they have the same denotation. -/
theorem Step.denote_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hFwt : Factory.WellTyped F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  induction hstep generalizing τ with
  | expand_fvar x e henv =>
    cases h₁ with
    | fvar => simp [LExpr.denote]; exact (hEnv vt x _ _ henv h₂).symm
  | beta e1 v2 eres hval heq =>
    subst heq
    cases h₁
    rename_i aty htyv2 htyabs
    cases htyabs with
    | abs =>
      rename_i h_body
      rw [denote_app tcInterp opInterp fvarVal vt .nil (.abs h_body) htyv2,
          denote_abs tcInterp opInterp fvarVal vt .nil h_body]
      exact (subst_denote tcInterp opInterp fvarVal vt .nil h_body htyv2 h₂).symm
  | reduce_2 v1 e2 e2' hval hstep' ih =>
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        have haty := HasTypeA_unique h_fn h_fn'
        cases haty
        rw [denote_app tcInterp opInterp fvarVal vt .nil h_fn h_arg,
            denote_app tcInterp opInterp fvarVal vt .nil h_fn' h_arg']
        congr 1
        rw[ih h_arg h_arg']
  | reduce_1 e1 e1' e2 hstep' ih =>
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        have haty := HasTypeA_unique h_arg h_arg'
        subst haty
        rw [denote_app tcInterp opInterp fvarVal vt .nil h_fn h_arg,
            denote_app tcInterp opInterp fvarVal vt .nil h_fn' h_arg']
        congr 1
        rw[ih h_fn h_fn']
  | ite_reduce_then ethen eelse =>
    cases h₁ with
    | ite h_c h_t h_e =>
      rw [denote_ite tcInterp opInterp fvarVal vt .nil h_c h_t h_e]
      have hc: LExpr.denote tcInterp opInterp fvarVal vt .nil
          (.const _ (.boolConst true)) .bool h_c = true := by rfl
      rw [hc]; rfl
  | ite_reduce_else ethen eelse =>
    cases h₁ with
    | ite h_c h_t h_e =>
      rw [denote_ite tcInterp opInterp fvarVal vt .nil h_c h_t h_e]
      have hc : LExpr.denote tcInterp opInterp fvarVal vt .nil
          (.const _ (.boolConst false)) .bool h_c = false := by rfl
      rw [hc]; rfl
  | ite_reduce_cond econd econd' ethen eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite tcInterp opInterp fvarVal vt .nil h_c h_t h_e,
            denote_ite tcInterp opInterp fvarVal vt .nil h_c' h_t' h_e']
        rw [ih h_c h_c']
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite tcInterp opInterp fvarVal vt .nil h_c h_t h_e,
            denote_ite tcInterp opInterp fvarVal vt .nil h_c' h_t' h_e']
        rw [ih h_t h_t']
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite tcInterp opInterp fvarVal vt .nil h_c h_t h_e,
            denote_ite tcInterp opInterp fvarVal vt .nil h_c' h_t' h_e']
        rw [ih h_e h_e']
  | eq_reduce e1 e2 eres hv1 hv2 heq =>
    subst heq
    cases h₁ with
    | eq h_1 h_2 =>
      revert h₂
      cases hb : LExpr.eql F e1 e2 hv1 hv2 with
      | true =>
        intros h₂
        rw [denote_eq_true tcInterp opInterp fvarVal vt .nil h_1 h_2 _
            ((eql_iff_denote_eq tcInterp opInterp fvarVal vt hv1 hv2 h_1 h_2).mp hb)]
        rfl
      | false =>
        intros h₂
        rw [denote_eq_false tcInterp opInterp fvarVal vt .nil h_1 h_2 _
            (mt (eql_iff_denote_eq tcInterp opInterp fvarVal vt hv1 hv2 h_1 h_2).mpr
              (by simp [hb]))]
        rfl
  | eq_reduce_lhs e1 e1' e2 hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_2 h_2'; subst hty
        have ih_eq := ih h_1 h_1'
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil e1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true tcInterp opInterp fvarVal vt .nil h_1 h_2 _ heq,
              denote_eq_true tcInterp opInterp fvarVal vt .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false tcInterp opInterp fvarVal vt .nil h_1 h_2 _ heq,
              denote_eq_false tcInterp opInterp fvarVal vt .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | eq_reduce_rhs v1 e2 e2' hv1 hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_1 h_1'; subst hty
        have ih_eq := ih h_2 h_2'
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true tcInterp opInterp fvarVal vt .nil h_1 h_2 _ heq,
              denote_eq_true tcInterp opInterp fvarVal vt .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false tcInterp opInterp fvarVal vt .nil h_1 h_2 _ heq,
              denote_eq_false tcInterp opInterp fvarVal vt .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | expand_fn e callee fnbody new_body args fn hcall hbody heq =>
    subst heq
    obtain ⟨h_args, h_denote_e⟩ := callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    have h_tau : τ = fn.output := callOfLFunc_output_type hFwt hcall h₁
    subst h_tau
    have hfn_in : fn ∈ F := Factory.callOfLFunc_mem hcall
    have h_body_ty : LExpr.HasTypeA [] fnbody fn.output := hFwt fn hfn_in fnbody hbody
    have h_map_eq : (List.map Prod.snd fn.inputs).map (LMonoTy.substTyVars vt) =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).map Prod.snd := by
      simp [List.map_map, Function.comp]
    -- Transport denoteArgs to the InterpConsistentBody index
    let args' : HList (SortDenote tcInterp)
        ((fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).map Prod.snd) :=
      HList.cast h_map_eq (denoteArgs tcInterp opInterp fvarVal vt h_args)
    have h_consistent := hF.1 fn hfn_in fnbody hbody vt fvarVal h_body_ty args'
    have h_arity : args.length = fn.inputs.length := by
      have := h_args.length_eq; simp at this; exact this
    have h_keys : (fn.inputs.keys.zip args).map Prod.fst =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).map Prod.fst := by
      rw [ListMap.keys_eq_map_fst,
          List.map_fst_zip (l₁ := fn.inputs.map Prod.fst) (l₂ := args) (by simp; omega),
          List.map_map]; rfl
    have h_len : (fn.inputs.keys.zip args).length =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))).length := by
      simp [ListMap.keys_eq_map_fst, List.length_zip, h_arity]
    have h_subst := substFvars_denote tcInterp opInterp fvarVal vt
        (sortBindings := fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty)))
        h_body_ty h₂ args' h_keys h_len
    rw [h_denote_e, ← h_subst]
    -- Goal: applyArgs (opInterp fn.name (mkArrow ret xs)) (denoteArgs h_args)
    --     = denote (withArgs ...) fnbody
    -- h_consistent: applyArgs (opInterp fn.name (mkArrow ret ys)) args' = same RHS
    -- Use applyArgs_cast_eq to rewrite LHS, replacing (denoteArgs h_args) with args'
    rw [SortDenote.applyArgs_cast_eq tcInterp h_map_eq (opInterp fn.name)
        (denoteArgs tcInterp opInterp fvarVal vt h_args)]
    exact h_consistent
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    have h_tau := callOfLFunc_output_type hFwt hcall h₁; subst h_tau
    obtain ⟨h_args, h_denote_e⟩ := callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    have hfn_in : fn ∈ F := Factory.callOfLFunc_mem hcall
    rename_i m
    have h_consistent := hF.2 fn hfn_in denotefn heval vt fvarVal m args e'
        hresult.symm h_args h₂
    rw [h_denote_e, ← h_consistent]

/-- A single step preserves well-typedness. -/
theorem Step.type_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    : LExpr.HasTypeA [] e₂ τ := by
  sorry

/-- Multi-step version: if `e₁` reduces to `e₂` in zero or more steps, and
both are well-typed at `τ`, they have the same denotation. -/
theorem StepStar.denote_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hsteps : StepStar F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  sorry

end Lambda

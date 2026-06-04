/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Init.Data.List.Basic
import Init.Data.List.Lemmas
public import Strata.DL.Lambda.Lambda
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.Languages.Core.StatementSemantics
public import Strata.Transform.CoreTransform
public import Strata.Transform.CoreTransformSemanticsProps
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Util.ListUtils

/-! # Substitution-Correctness Stack

  Reusable substitution-correctness lemmas for `LExpr.substFvar` /
  `substFvars` against `substStores` / `invStores`. Used by `CallElimCorrect`;
  applicable to any transform that introduces fresh variables and
  substitutes them (procedure-inlining, loop-elimination, etc.).
-/

namespace Core.Transform
open Imperative

public section

/-! ### Substitution-correctness lemmas (small-step)

    These re-derive the legacy `Lambda.LExpr.substFvarCorrect` and
    `Lambda.LExpr.substFvarsCorrect` proofs using only currently-live
    infrastructure. They are pure expression-level lemmas and are the
    workhorses behind `H_asserts` / `H_assumes`. -/

/-- Substitution of a single free variable preserves expression evaluation
    when the source/target stores agree on the substitution and on
    everything-else used in `e`. -/
theorem subst_fvar_correct
    {δ : CoreEval}
    {σ σ' : CoreStore}
    {fro to : Expression.Ident}
    {e : Expression.Expr}
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hsubst : Imperative.substStores σ σ' [(fro, to)])
    (Hinv : Imperative.invStores σ σ'
              ((Imperative.HasVarsPure.getVars (P:=Expression) e).removeAll [fro])) :
    δ σ e = δ σ' (e.substFvar fro (Core.Transform.createFvar to)) := by
  induction e <;> simp [Lambda.LExpr.substFvar, Core.Transform.createFvar] at *
  case const c | op o ty | bvar x =>
    rw [Hwfvl.2]
    rw [Hwfvl.2]
    constructor
    constructor
  case fvar name ty =>
    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
    split <;> try simp_all
    . simp [Imperative.substStores] at Hsubst
      rw [Hwfvr]
      rw [Hwfvr]
      exact Hsubst
      simp [Imperative.HasFvar.getFvar]
      simp [Imperative.HasFvar.getFvar]
    . next Hne =>
      simp [Imperative.invStores, Imperative.substStores,
            Imperative.HasVarsPure.getVars,
            Lambda.LExpr.LExpr.getVars, List.removeAll, Hne] at Hinv
      rw [Hwfvr]
      rw [Hwfvr]
      exact Hinv
      simp [Imperative.HasFvar.getFvar]
      simp [Imperative.HasFvar.getFvar]
  case abs m ty e ih =>
    specialize ih Hinv
    have Hwfca := Hwfc.1 σ σ' e ((e.substFvar fro (Lambda.LExpr.fvar () to none)))
    grind
  case quant m k ty tr e trih eih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize eih ?_
    · intros k1 k2 Hin
      rw [Hinv]
      right;
      assumption
    specialize trih ?_
    · intros k1 k2 Hin
      rw [Hinv]
      left;
      assumption
    apply Hwfc.quantcongr <;> grind
  case app m c fn fih eih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize fih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    apply Hwfc.appcongr <;> grind
  case ite m c t e cih tih eih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize cih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize tih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; right; assumption
    apply Hwfc.itecongr <;> grind
  case eq m e1 e2 e1ih e2ih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize e1ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize e2ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    apply Hwfc.eqcongr <;> grind

/-- Zero-substitution case: when the source/target stores agree on every
    free variable of `e`, evaluation is unchanged. Re-derived from the
    legacy `Lambda.LExpr.substFvarsCorrectZero`. -/
theorem subst_fvarsZero_correct
    {δ : CoreEval}
    {σ σ' : CoreStore}
    {e : Expression.Expr}
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hinv : Imperative.invStores σ σ'
              (Imperative.HasVarsPure.getVars (P:=Expression) e)) :
    δ σ e = δ σ' e := by
  induction e <;> simp at *
  case const c | op o ty | bvar x =>
    rw [Hwfvl.2]
    rw [Hwfvl.2]
    constructor
    constructor
  case fvar m name ty =>
    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
    specialize Hwfvr (Lambda.LExpr.fvar m name ty) name
    rw [Hwfvr]
    rw [Hwfvr]
    rw [Hinv]
    simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars]
    simp [Imperative.HasFvar.getFvar]
    simp [Imperative.HasFvar.getFvar]
  case abs m ty e ih =>
    specialize ih Hinv
    have Hwfca := Hwfc.abscongr σ σ' e e ih
    apply Hwfca
  case quant m k ty tr e trih eih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize trih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    apply Hwfc.quantcongr <;> grind
  case app m fn e fih eih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize fih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    apply Hwfc.appcongr <;> grind
  case ite m c t e cih tih eih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize cih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize tih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; right; assumption
    apply Hwfc.itecongr <;> grind
  case eq m e1 e2 e1ih e2ih =>
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize e1ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize e2ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    apply Hwfc.eqcongr <;> grind

/-! ### Substitution-list helpers

    Re-derived from the legacy code (currently in the comment block) so the
    new small-step proofs of `H_asserts`/`H_assumes` can stand on their own.
    These are pure list-level / store-level lemmas about
    `substDefined`, `substNodup`, `substStores`, and `invStores`. -/

theorem updatedStateIsDefinedMono'
    {σ : CoreStore} {k : Expression.Ident} {v : Expression.Expr}
    {x : Expression.Ident} :
    (σ x).isSome = true → ((updatedState σ k v) x).isSome = true := by
  intros Hsome
  simp [updatedState]
  split <;> simp_all

theorem subst_defined_updatedState
    {σ σ' : CoreStore} {k : Expression.Ident} {v : Expression.Expr}
    {ls : List (Expression.Ident × Expression.Ident)} :
    Imperative.substDefined σ σ' ls →
    Imperative.substDefined (updatedState σ k v) σ' ls := by
  intros Hsubst k1 k2 Hin
  refine ⟨?_, (Hsubst k1 k2 Hin).2⟩
  exact updatedStateIsDefinedMono' (Hsubst k1 k2 Hin).1

/-- Build `substDefined σ σ' ((a₁ ++ b₁).zip (a₂ ++ b₂))` from per-half
    `isDefined` facts. -/
theorem substDefined_of_app
    {σ σ' : CoreStore} {a₁ b₁ a₂ b₂ : List Expression.Ident}
    (Hσ_a : Imperative.isDefined σ a₁) (Hσ_b : Imperative.isDefined σ b₁)
    (Hσ'_a : Imperative.isDefined σ' a₂) (Hσ'_b : Imperative.isDefined σ' b₂) :
    Imperative.substDefined σ σ' ((a₁ ++ b₁).zip (a₂ ++ b₂)) := by
  intro k1 k2 Hkin
  have Hmem := List.of_mem_zip Hkin
  exact ⟨(List.mem_append.mp Hmem.1).elim (Hσ_a _) (Hσ_b _),
         (List.mem_append.mp Hmem.2).elim (Hσ'_a _) (Hσ'_b _)⟩

theorem subst_nodup_ht
    {h h' : Expression.Ident}
    {t t' : List Expression.Ident} :
    t.length = t'.length →
    Imperative.substNodup ((h, h') :: List.zip t t') →
    ¬ h ∈ t ∧ ¬ h' ∈ t' := by
  intros Hlen Hsubst
  simp [Imperative.substNodup] at Hsubst
  refine ⟨?_, ?_⟩
  · exact List.zip_notin_fst_pair Hlen Hsubst.1.1
  · have Hnd := nodup_middle Hsubst.2
    simp at Hnd
    have Hnd' := Hnd.1.2
    exact List.zip_notin_snd_pair Hlen Hnd'

theorem getVars_substFvar_or
    {e : Expression.Expr} {h h' v : Expression.Ident} :
    v ∈ (Imperative.HasVarsPure.getVars (P:=Expression)
          (Lambda.LExpr.substFvar e h (Core.Transform.createFvar h'))) →
    v ∈ (Imperative.HasVarsPure.getVars (P:=Expression) e) ∨ v = h' := by
  intros Hin
  induction e <;>
    simp [Lambda.LExpr.substFvar,
          Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars,
          Core.Transform.createFvar
         ] at * <;> try simp_all
  case fvar name ty =>
    split at Hin <;> simp [Lambda.LExpr.LExpr.getVars] at * <;> simp_all
  case app m fn e fn_ih e_ih =>
    cases Hin <;> simp_all
    · cases fn_ih <;> simp_all
    · cases e_ih <;> simp_all
  case quant m qk name ty tr e tr_ih e_ih =>
    cases Hin <;> simp_all
    · cases tr_ih <;> simp_all
    · cases e_ih <;> simp_all
  case ite m c t e c_ih t_ih e_ih =>
    cases Hin with
    | inl Hin => cases (c_ih Hin) <;> simp_all
    | inr Hin =>
      cases Hin with
      | inl Hin => cases (t_ih Hin) <;> simp_all
      | inr Hin => cases (e_ih Hin) <;> simp_all
  case eq m e1 e2 e1_ih e2_ih =>
    cases Hin <;> simp_all
    · cases e1_ih <;> simp_all
    · cases e2_ih <;> simp_all

theorem getVars_substFvar_replace
    {e : Expression.Expr} {h h' : Expression.Ident} :
    (Imperative.HasVarsPure.getVars
        (Lambda.LExpr.substFvar e h (Core.Transform.createFvar h'))) =
    (Imperative.HasVarsPure.getVars (P:=Expression) e).replaceAll h h' := by
  induction e <;>
    simp [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars,
          Lambda.LExpr.substFvar,
          Core.Transform.createFvar,
          List.replaceAll] at * <;> try assumption
  case fvar name ty =>
    by_cases h_eq : name = h
    · subst h_eq
      simp [Lambda.LExpr.LExpr.getVars]
    · simp [h_eq, Lambda.LExpr.LExpr.getVars]
      have hbeq : (h == name) = false := by
        simp; intro heq; exact h_eq heq.symm
      rw [hbeq]
  case app fn e fn_ih e_ih =>
    rw [fn_ih, e_ih, List.replaceAll_app]
  case quant qk ty tr_ih e_ih =>
    rw [tr_ih, e_ih, List.replaceAll_app]
  case ite c t e c_ih t_ih e_ih =>
    rw [c_ih, t_ih, e_ih, List.replaceAll_app, List.replaceAll_app]
  case eq e1 e2 e1_ih e2_ih =>
    rw [e1_ih, e2_ih, List.replaceAll_app]

theorem updatedStores_invStores
    {σ : CoreStore} {k : Expression.Ident} {v : Expression.Expr}
    {ks : List Expression.Ident} :
    ¬ k ∈ ks →
    Imperative.invStores σ (updatedState σ k v) ks := by
  intros Hnin k1 k2 Hin
  have Heq : k1 = k2 := zip_self_eq Hin
  simp_all
  have Hin := (List.of_mem_zip Hin).1
  have Hne : k2 ≠ k := ne_of_mem_of_not_mem Hin Hnin
  simp [updatedState]
  simp_all

theorem invStores_subst_head
    {σ : CoreStore} {h h' : Expression.Ident} {v₁ : Expression.Expr}
    {vs : List Expression.Ident} :
    Imperative.substStores (P := Expression) σ (updatedState σ h' v₁) [(h, h')] →
    ¬ h' ∈ vs →
    Imperative.invStores σ (updatedState σ h' v₁) (List.removeAll vs [h]) := by
  intros _ Hnin
  apply updatedStores_invStores
  simp [List.removeAll]
  simp_all

theorem invStores_subst_tail
    {σ σ' : CoreStore} {h h' : Expression.Ident} {v₁ : Expression.Expr}
    {t t' vs : List Expression.Ident} :
    Imperative.substStores (P := Expression) σ σ' ((h, h') :: t.zip t') →
    Imperative.substStores (P := Expression) (updatedState σ h' v₁) σ' (t.zip t') →
    σ h = some v₁ →
    h ≠ h' →
    Imperative.invStores σ σ' (List.removeAll vs ((h :: t) ++ (h' :: t'))) →
    Imperative.invStores (updatedState σ h' v₁) σ'
                            (List.removeAll (vs.replaceAll h h') (t ++ t')) := by
  intros Hsubst1 _ Hsome Hne Hinv k1 k2 Hin
  have Heq := zip_self_eq Hin
  simp_all
  simp [Imperative.invStores, Imperative.substStores] at *
  simp [updatedState]
  split
  · rw [← Hsubst1 h] <;> simp_all
  · next neq =>
    apply Hinv
    apply zip_self_eq'
    have Hin := (List.of_mem_zip Hin).1
    have Hsub := removeAll_sublist (vs.replaceAll h h') (t ++ t')
    have Hin' : k2 ∈ (vs.replaceAll h h') := List.Sublist.mem Hin Hsub
    have Hor := in_replaceAll_removeAll Hin
    cases Hor <;> simp_all
    apply removeAll_cons
    · intros Heq
      simp_all
      have Hnmem : ¬ h ∈ vs.replaceAll h h' := replaceAll_not_mem Hne
      exact Hnmem Hin'
    · simp [List.removeAll] at *
      simp_all

/-- Helper: `Map.find? rest h' = none` when `h'` is not a key in `rest`. -/
theorem map_find_none_of_not_key
    {h' : Expression.Ident}
    {rest : List (Expression.Ident × Expression.Expr)} :
    (∀ a b, (a, b) ∈ rest → a ≠ h') →
    Map.find? rest h' = none := by
  intro Hnk
  induction rest with
  | nil => rfl
  | cons p rs ih =>
    obtain ⟨a, b⟩ := p
    have hane : a ≠ h' := Hnk a b List.mem_cons_self
    have ih' : Map.find? rs h' = none := by
      apply ih
      intros a' b' hin
      exact Hnk a' b' (List.mem_cons_of_mem _ hin)
    show (if a = h' then some b else Map.find? rs h') = none
    rw [if_neg hane, ih']

/-- Helper: `Map.find? ((h, v) :: rest) name = Map.find? rest name` when `name ≠ h`. -/
theorem map_find_cons_ne
    {h name : Expression.Ident} {v : Expression.Expr}
    {rest : List (Expression.Ident × Expression.Expr)} :
    name ≠ h →
    Map.find? ((h, v) :: rest) name = Map.find? rest name := by
  intro Hne
  show (if h = name then some v else Map.find? rest name) = Map.find? rest name
  rw [if_neg (fun heq => Hne heq.symm)]

/-- For a cons-substitution `(h, fv) :: rest`, when `h` and `h'` (the source of
    `fv = createFvar h'`) are not keys, `substFvars` decomposes as a leading
    single-var substitution. -/
theorem substFvars_cons_eq
    {e : Expression.Expr} {h h' : Expression.Ident}
    {rest : List (Expression.Ident × Expression.Expr)}
    (Hh_notin_keys : ∀ a b, (a, b) ∈ rest → a ≠ h)
    (Hh'_notin_keys : ∀ a b, (a, b) ∈ rest → a ≠ h') :
    Lambda.LExpr.substFvars e ((h, Core.Transform.createFvar h') :: rest) =
    Lambda.LExpr.substFvars
      (Lambda.LExpr.substFvar e h (Core.Transform.createFvar h')) rest := by
  induction e with
  | const m c =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_const']
  | op m n t =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_op']
  | bvar m i =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_bvar]
  | fvar m name ty =>
    by_cases heq : name = h
    · subst heq
      -- LHS: substFvars (fvar name) ((name, fv) :: rest) = fv
      have hfind_lhs : Map.find?
            ((name, Core.Transform.createFvar h') :: rest) name =
            some (Core.Transform.createFvar h') := by
        show (if name = name then some (Core.Transform.createFvar h')
              else Map.find? rest name) = _
        rw [if_pos rfl]
      have hLHS := Lambda.LExpr.substFvars_fvar_find m name ty
                      ((name, Core.Transform.createFvar h') :: rest)
                      (Core.Transform.createFvar h') hfind_lhs
      -- RHS: substFvar (fvar name) name fv  =  fv = createFvar h'
      have hsubst : Lambda.LExpr.substFvar
                      (Lambda.LExpr.fvar m name ty)
                      name (Core.Transform.createFvar h') =
                    Core.Transform.createFvar h' := by
        show (if (name == name) = true then _ else _) = _
        simp
      rw [hsubst]
      -- Now goal: substFvars (fvar name ...) (...) = substFvars (createFvar h') rest
      -- LHS rewrites via hLHS to createFvar h'
      rw [hLHS]
      -- RHS: substFvars (createFvar h' = fvar h') rest
      have hfind_rhs : Map.find? rest h' = none :=
        map_find_none_of_not_key Hh'_notin_keys
      -- Use substFvars_fvar_none, with implicits inferred from rest's type
      have hRHS : Lambda.LExpr.substFvars
                    (Core.Transform.createFvar h' :
                      Expression.Expr) rest =
                  Core.Transform.createFvar h' := by
        unfold Core.Transform.createFvar
        exact Lambda.LExpr.substFvars_fvar_none _ _ _ _ hfind_rhs
      show Core.Transform.createFvar h' =
            Lambda.LExpr.substFvars (Core.Transform.createFvar h' : Expression.Expr) rest
      rw [hRHS]
    · -- name ≠ h
      have hsubst : Lambda.LExpr.substFvar
                      (Lambda.LExpr.fvar m name ty)
                      h (Core.Transform.createFvar h') =
                    Lambda.LExpr.fvar m name ty := by
        show (if (name == h) = true then _ else _) = _
        rw [if_neg]
        intro hbeq
        exact heq (beq_iff_eq.mp hbeq)
      rw [hsubst]
      have hcons := map_find_cons_ne (h := h) (v := Core.Transform.createFvar h')
                      (name := name) (rest := rest) heq
      cases hf : Map.find? rest name with
      | none =>
        have hf' : Map.find? ((h, Core.Transform.createFvar h') :: rest) name = none := by
          rw [hcons]; exact hf
        rw [Lambda.LExpr.substFvars_fvar_none m name ty _ hf']
        rw [Lambda.LExpr.substFvars_fvar_none m name ty rest hf]
      | some v =>
        have hf' : Map.find? ((h, Core.Transform.createFvar h') :: rest) name = some v := by
          rw [hcons]; exact hf
        rw [Lambda.LExpr.substFvars_fvar_find m name ty _ v hf']
        rw [Lambda.LExpr.substFvars_fvar_find m name ty rest v hf]
  | abs m pn ty body ih =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_abs, ih]
  | quant m qk pn ty tr body trih bih =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_quant, trih, bih]
  | app m fn arg fih aih =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_app, fih, aih]
  | ite m c t f cih tih fih =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_ite, cih, tih, fih]
  | eq m e1 e2 ih1 ih2 =>
    simp only [Lambda.LExpr.substFvar, Lambda.LExpr.substFvars_eq, ih1, ih2]

/-- Helper: if `h' ∉ ts`, then `h'` is not a key in `(t.zip (createFvars ts)).fst`. -/
theorem zip_createFvars_keys_notin
    {h : Expression.Ident}
    {t : List Expression.Ident} {ts : List Expression.Ident} :
    ¬ h ∈ t →
    ∀ a b, (a, b) ∈ t.zip (Core.Transform.createFvars ts) → a ≠ h := by
  intros Hnin a b Hin Heq
  subst Heq
  exact Hnin (List.of_mem_zip Hin).1

/-- Multi-variable substitution preserves expression evaluation. Re-derived
    from the legacy `Lambda.LExpr.substFvarsCorrect`. -/
theorem subst_fvars_correct
    {δ : CoreEval}
    {σ σ' : CoreStore}
    {fro to : List Expression.Ident}
    {e : Expression.Expr}
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hlen : fro.length = to.length)
    (Hdef : Imperative.substDefined σ σ' (fro.zip to))
    (Hnd : Imperative.substNodup (fro.zip to))
    (Hsubst : Imperative.substStores σ σ' (fro.zip to))
    (Hnin : to.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) e))
    (Hinv : Imperative.invStores σ σ'
              ((Imperative.HasVarsPure.getVars (P:=Expression) e).removeAll (fro ++ to))) :
    δ σ e = δ σ' (e.substFvars (fro.zip (Core.Transform.createFvars to))) := by
  induction fro generalizing to σ σ' e
  case nil =>
    have Hemp : to = [] := List.eq_nil_of_length_eq_zero (Eq.symm Hlen)
    subst Hemp
    simp only [Core.Transform.createFvars, List.map_nil, List.zip_nil_right]
    -- substFvars on empty map is identity
    have hsubstEmp :
        Lambda.LExpr.substFvars e ([] : Map Expression.Ident Expression.Expr) = e := by
      simp [Lambda.LExpr.substFvars, Map.isEmpty]
    rw [hsubstEmp]
    -- Hinv came in with `removeAll ([] ++ [])`, simplify
    have HinvSimp :
        Imperative.invStores σ σ'
          (Imperative.HasVarsPure.getVars (P:=Expression) e) := by
      have := Hinv
      simp at this
      exact this
    exact subst_fvarsZero_correct Hwfc Hwfvr Hwfvl HinvSimp
  case cons h t ih =>
    cases to with
    | nil => simp at Hlen
    | cons h' t' =>
      have Hlen_t : t.length = t'.length := by
        simp at Hlen; exact Hlen
      have Hnd_t : Imperative.substNodup (t.zip t') := subst_nodup_tail Hnd
      have Hht := subst_nodup_ht Hlen_t Hnd
      have Hne : h ≠ h' := by
        intro heq
        subst heq
        simp [Imperative.substNodup] at Hnd
      have Hsubst1 := substStoresCons' Hnd Hdef Hsubst
      obtain ⟨σ₁, v₁, Hsome, Hstore, Hsubst', Hsubst1⟩ := Hsubst1
      subst Hstore
      -- Step 1: rewrite δ σ e using subst_fvar_correct.
      have Hinv_head : Imperative.invStores σ (updatedState σ h' v₁)
                          ((Imperative.HasVarsPure.getVars (P:=Expression) e).removeAll [h]) := by
        apply invStores_subst_head Hsubst'
        intro Hin
        exact Hnin (List.mem_cons_self) Hin
      have Hhead : δ σ e =
                   δ (updatedState σ h' v₁)
                     (Lambda.LExpr.substFvar e h (Core.Transform.createFvar h')) :=
        subst_fvar_correct Hwfc Hwfvr Hwfvl Hsubst' Hinv_head
      rw [Hhead]
      -- Step 2: rewrite using IH. We apply IH at e' = substFvar e h (createFvar h').
      have Hdef_σ₁ : Imperative.substDefined (updatedState σ h' v₁) σ' (t.zip t') :=
        subst_defined_updatedState (subst_defined_tail Hdef)
      have Hnin_t : t'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression)
                      (Lambda.LExpr.substFvar e h (Core.Transform.createFvar h'))) := by
        intros a' Hin Hin2
        have Hor := getVars_substFvar_or Hin2
        cases Hor with
        | inl Hin3 =>
          exact Hnin (List.mem_cons_of_mem h' Hin) Hin3
        | inr Heq =>
          subst Heq
          exact Hht.2 Hin
      have Hinv_t : Imperative.invStores (updatedState σ h' v₁) σ'
          ((Imperative.HasVarsPure.getVars
              (Lambda.LExpr.substFvar e h (Core.Transform.createFvar h'))).removeAll
            (t ++ t')) := by
        rw [getVars_substFvar_replace]
        have HinvE : Imperative.invStores σ σ'
            ((Imperative.HasVarsPure.getVars (P:=Expression) e).removeAll
              ((h :: t) ++ (h' :: t'))) := by
          have heq : (h :: t) ++ (h' :: t') = h :: t ++ h' :: t' := by simp
          rw [heq]; exact Hinv
        exact invStores_subst_tail Hsubst Hsubst1 Hsome Hne HinvE
      have Hres := ih Hlen_t Hdef_σ₁ Hnd_t Hsubst1 Hnin_t Hinv_t
      rw [Hres]
      -- Step 3: align substFvars-cons with substFvars after substFvar.
      have Hh_notin : ∀ a b, (a, b) ∈ t.zip (Core.Transform.createFvars t') → a ≠ h :=
        zip_createFvars_keys_notin Hht.1
      -- substNodup: nodup of fst++snd = h::t ++ h'::t'. h' ∉ t (and h' ∉ t').
      have Hh'_notin_t : ¬ h' ∈ t := by
        intro hh
        have HzipUnzip : (t.zip t').unzip = (t, t') := by
          rw [List.unzip_zip]; exact Hlen_t
        have HndStart : List.Nodup
            (((h, h') :: t.zip t').unzip.fst ++
              ((h, h') :: t.zip t').unzip.snd) := Hnd
        -- Manually unfold: ((h,h')::t.zip t').unzip = (h :: t, h' :: t')
        have Hcons_fst :
            ((h, h') :: t.zip t').unzip.fst = h :: t := by
          simp [HzipUnzip]
        have Hcons_snd :
            ((h, h') :: t.zip t').unzip.snd = h' :: t' := by
          simp [HzipUnzip]
        rw [Hcons_fst, Hcons_snd] at HndStart
        -- HndStart : Nodup (h :: t ++ h' :: t')
        have HtailNd : List.Nodup (t ++ h' :: t') := by
          have : List.Nodup ((h :: t) ++ h' :: t') := HndStart
          rw [List.cons_append] at this
          exact (List.nodup_cons.mp this).2
        have HmidNd := nodup_middle HtailNd
        have Hnotin : h' ∉ t ++ t' := (List.nodup_cons.mp HmidNd).1
        exact Hnotin (List.mem_append_left _ hh)
      have Hh'_notin : ∀ a b, (a, b) ∈ t.zip (Core.Transform.createFvars t') → a ≠ h' := by
        intros a b Hin Heq
        subst Heq
        exact Hh'_notin_t ((List.of_mem_zip Hin).1)
      have Hcons := substFvars_cons_eq (e := e) (h := h) (h' := h')
                      (rest := t.zip (Core.Transform.createFvars t'))
                      Hh_notin Hh'_notin
      rw [← Hcons]
      simp [Core.Transform.createFvars]

/-! ### Structural decomposition for `getVars (substFvars e sm)`.

    For the L6 (assumes) site of `callElimStatementCorrect`, we need to
    reason about the free variables of the post-`oldSubst` postcondition
    expressions.  The decomposition lemma below shows that any variable
    in `getVars (substFvars e sm)` either survives from `e` (when it is
    not a key of `sm`) or comes from the codomain expression of some
    key-substitution that `e` references.  This is the multi-step
    analogue of the existing `getVars_substFvar_or` lemma. -/

/-- Multi-step substitution decomposition: every free variable of
    `substFvars e sm` either (a) was free in `e` and not a key of `sm`,
    or (b) was contributed by the codomain expression `w` of some
    `(k, w) ∈ sm` where `k` was a free variable of `e`. -/
theorem getVars_substFvars_mem
    {e : Expression.Expr} {v : Expression.Ident}
    {sm : Map Expression.Ident Expression.Expr}
    (Hin : v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
              (Lambda.LExpr.substFvars e sm)) :
    (v ∈ Imperative.HasVarsPure.getVars (P:=Expression) e ∧
      Map.find? sm v = none) ∨
    (∃ k w,
        k ∈ Imperative.HasVarsPure.getVars (P:=Expression) e ∧
        Map.find? sm k = some w ∧
        v ∈ Imperative.HasVarsPure.getVars (P:=Expression) w) := by
  induction e with
  | const m c =>
    simp only [Lambda.LExpr.substFvars_const',
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.not_mem_nil] at Hin
  | op m n t =>
    simp only [Lambda.LExpr.substFvars_op',
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.not_mem_nil] at Hin
  | bvar m i =>
    simp only [Lambda.LExpr.substFvars_bvar,
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.not_mem_nil] at Hin
  | fvar m name ty =>
    -- substFvars (fvar name) sm = match sm.find? name with | some w => w | none => fvar name
    by_cases hfind : Map.find? sm name = none
    · rw [Lambda.LExpr.substFvars_fvar_none m name ty sm hfind] at Hin
      -- Hin : v ∈ getVars (fvar name) = [name]
      simp only [Imperative.HasVarsPure.getVars,
                 Lambda.LExpr.LExpr.getVars,
                 List.mem_singleton] at Hin
      subst Hin
      refine Or.inl ⟨?_, hfind⟩
      simp [Imperative.HasVarsPure.getVars,
            Lambda.LExpr.LExpr.getVars]
    · -- find? returns some w
      rcases Option.ne_none_iff_exists.mp hfind with ⟨w, hf⟩
      rw [Lambda.LExpr.substFvars_fvar_find m name ty sm w hf.symm] at Hin
      -- Hin : v ∈ getVars w
      refine Or.inr ⟨name, w, ?_, hf.symm, Hin⟩
      simp [Imperative.HasVarsPure.getVars,
            Lambda.LExpr.LExpr.getVars]
  | abs m name ty body ih =>
    simp only [Lambda.LExpr.substFvars_abs,
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars] at Hin
    have Hbody := ih Hin
    simp only [Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars]
    exact Hbody
  | quant m qk name ty tr body trih bih =>
    simp only [Lambda.LExpr.substFvars_quant,
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append] at Hin
    simp only [Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append]
    cases Hin with
    | inl Hin =>
      cases trih Hin with
      | inl h => exact Or.inl ⟨Or.inl h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inl Hk, Hf, Hv⟩
    | inr Hin =>
      cases bih Hin with
      | inl h => exact Or.inl ⟨Or.inr h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inr Hk, Hf, Hv⟩
  | app m fn arg fih aih =>
    simp only [Lambda.LExpr.substFvars_app,
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append] at Hin
    simp only [Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append]
    cases Hin with
    | inl Hin =>
      cases fih Hin with
      | inl h => exact Or.inl ⟨Or.inl h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inl Hk, Hf, Hv⟩
    | inr Hin =>
      cases aih Hin with
      | inl h => exact Or.inl ⟨Or.inr h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inr Hk, Hf, Hv⟩
  | ite m c t f cih tih fih =>
    simp only [Lambda.LExpr.substFvars_ite,
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append] at Hin
    simp only [Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append]
    cases Hin with
    | inl Hin =>
      cases Hin with
      | inl Hin =>
        cases cih Hin with
        | inl h => exact Or.inl ⟨Or.inl (Or.inl h.1), h.2⟩
        | inr h =>
          obtain ⟨k, w, Hk, Hf, Hv⟩ := h
          exact Or.inr ⟨k, w, Or.inl (Or.inl Hk), Hf, Hv⟩
      | inr Hin =>
        cases tih Hin with
        | inl h => exact Or.inl ⟨Or.inl (Or.inr h.1), h.2⟩
        | inr h =>
          obtain ⟨k, w, Hk, Hf, Hv⟩ := h
          exact Or.inr ⟨k, w, Or.inl (Or.inr Hk), Hf, Hv⟩
    | inr Hin =>
      cases fih Hin with
      | inl h => exact Or.inl ⟨Or.inr h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inr Hk, Hf, Hv⟩
  | eq m e1 e2 e1ih e2ih =>
    simp only [Lambda.LExpr.substFvars_eq,
               Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append] at Hin
    simp only [Imperative.HasVarsPure.getVars,
               Lambda.LExpr.LExpr.getVars,
               List.mem_append]
    cases Hin with
    | inl Hin =>
      cases e1ih Hin with
      | inl h => exact Or.inl ⟨Or.inl h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inl Hk, Hf, Hv⟩
    | inr Hin =>
      cases e2ih Hin with
      | inl h => exact Or.inl ⟨Or.inr h.1, h.2⟩
      | inr h =>
        obtain ⟨k, w, Hk, Hf, Hv⟩ := h
        exact Or.inr ⟨k, w, Or.inr Hk, Hf, Hv⟩

/-- Pointwise δ-eval bridge for an arbitrary substitution `sm`.  Given two
    pointwise hypotheses — (a) δ σ' agrees with δ σ on every "surviving"
    free variable of `e` (those with `find? sm = none`), and (b) for every
    `(k, w) ∈ sm` with `k ∈ getVars e`, δ σ' w equals δ σ (fvar k) — we
    obtain `δ σ' (substFvars e sm) = δ σ e`.

    This generalizes `subst_fvars_correct` (which only handles
    `createFvars to`-style codomain) to arbitrary expression codomains.
    Used at the call site to bridge `δ σ_R1 (substFvars c.expr oldSubst_L6)`
    to `δ σO c.expr` for the L6 post-substitution eval. -/
theorem subst_fvars_eval_bridge
    {δ : CoreEval}
    {σ σ' : CoreStore}
    {e : Expression.Expr}
    {sm : Map Expression.Ident Expression.Expr}
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hsurv : ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) e,
              Map.find? sm v = none →
              δ σ' (Lambda.LExpr.fvar () v none) =
                δ σ (Lambda.LExpr.fvar () v none))
    (Hsub : ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) e →
              Map.find? sm k = some w →
              δ σ' w = δ σ (Lambda.LExpr.fvar () k none)) :
    δ σ' (Lambda.LExpr.substFvars e sm) = δ σ e := by
  induction e with
  | const m c =>
    simp only [Lambda.LExpr.substFvars_const']
    rw [Hwfvl.2, Hwfvl.2]
    constructor; constructor
  | op m n t =>
    simp only [Lambda.LExpr.substFvars_op']
    rw [Hwfvl.2, Hwfvl.2]
    constructor; constructor
  | bvar m i =>
    simp only [Lambda.LExpr.substFvars_bvar]
    rw [Hwfvl.2, Hwfvl.2]
    constructor; constructor
  | fvar m name ty =>
    by_cases hfind : Map.find? sm name = none
    · rw [Lambda.LExpr.substFvars_fvar_none m name ty sm hfind]
      simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
      have HwfL : δ σ' (Lambda.LExpr.fvar m name ty) = σ' name := by
        rw [Hwfvr (Lambda.LExpr.fvar m name ty) name]
        simp [Imperative.HasFvar.getFvar]
      have HwfR : δ σ (Lambda.LExpr.fvar m name ty) = σ name := by
        rw [Hwfvr (Lambda.LExpr.fvar m name ty) name]
        simp [Imperative.HasFvar.getFvar]
      have HwfL' : δ σ' (Lambda.LExpr.fvar () name none) = σ' name := by
        rw [Hwfvr (Lambda.LExpr.fvar () name none) name]
        simp [Imperative.HasFvar.getFvar]
      have HwfR' : δ σ (Lambda.LExpr.fvar () name none) = σ name := by
        rw [Hwfvr (Lambda.LExpr.fvar () name none) name]
        simp [Imperative.HasFvar.getFvar]
      have HsurvAt :=
        Hsurv name
          (by simp [Imperative.HasVarsPure.getVars,
                    Lambda.LExpr.LExpr.getVars])
          hfind
      rw [HwfL', HwfR'] at HsurvAt
      rw [HwfL, HwfR]
      exact HsurvAt
    · rcases Option.ne_none_iff_exists.mp hfind with ⟨w, hf⟩
      rw [Lambda.LExpr.substFvars_fvar_find m name ty sm w hf.symm]
      have Hself :
          name ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                  (Lambda.LExpr.fvar m name ty) := by
        simp [Imperative.HasVarsPure.getVars,
              Lambda.LExpr.LExpr.getVars]
      have HsubAt := Hsub name w Hself hf.symm
      simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
      have HwfR : δ σ (Lambda.LExpr.fvar m name ty) = σ name := by
        rw [Hwfvr (Lambda.LExpr.fvar m name ty) name]
        simp [Imperative.HasFvar.getFvar]
      have HwfR' : δ σ (Lambda.LExpr.fvar () name none) = σ name := by
        rw [Hwfvr (Lambda.LExpr.fvar () name none) name]
        simp [Imperative.HasFvar.getFvar]
      rw [HwfR]
      rw [HwfR'] at HsubAt
      exact HsubAt
  | abs m name ty body ih =>
    simp only [Lambda.LExpr.substFvars_abs]
    have Hsurv_body :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) body,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.abs m name ty body)
      simp [Lambda.LExpr.LExpr.getVars]
      show v ∈ Lambda.LExpr.LExpr.getVars body
      exact Hv
    have Hsub_body :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) body →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.abs m name ty body)
      simp [Lambda.LExpr.LExpr.getVars]
      show k ∈ Lambda.LExpr.LExpr.getVars body
      exact Hk
    have Hbody := ih Hsurv_body Hsub_body
    exact Hwfc.abscongr σ' σ _ _ Hbody m name ty
  | quant m qk name ty tr body trih bih =>
    simp only [Lambda.LExpr.substFvars_quant]
    have Hsurv_tr :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) tr,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.quant m qk name ty tr body)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inl Hv
    have Hsurv_body :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) body,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.quant m qk name ty tr body)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inr Hv
    have Hsub_tr :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) tr →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.quant m qk name ty tr body)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inl Hk
    have Hsub_body :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) body →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.quant m qk name ty tr body)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inr Hk
    have Htr := trih Hsurv_tr Hsub_tr
    have Hbody := bih Hsurv_body Hsub_body
    exact Hwfc.quantcongr σ' σ m qk name ty _ _ _ _ Htr Hbody
  | app m fn arg fih aih =>
    simp only [Lambda.LExpr.substFvars_app]
    have Hsurv_fn :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) fn,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.app m fn arg)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inl Hv
    have Hsurv_arg :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) arg,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.app m fn arg)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inr Hv
    have Hsub_fn :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) fn →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.app m fn arg)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inl Hk
    have Hsub_arg :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) arg →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.app m fn arg)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inr Hk
    have Hfn := fih Hsurv_fn Hsub_fn
    have Harg := aih Hsurv_arg Hsub_arg
    exact Hwfc.appcongr σ' σ m _ _ _ _ Hfn Harg
  | ite m c t f cih tih fih =>
    simp only [Lambda.LExpr.substFvars_ite]
    have HmkLeft : ∀ {x : Expression.Ident},
        x ∈ Imperative.HasVarsPure.getVars (P:=Expression) c →
        x ∈ Imperative.HasVarsPure.getVars (P:=Expression)
              (Lambda.LExpr.ite m c t f) := by
      intro x Hx
      show x ∈ Lambda.LExpr.LExpr.getVars c ++ Lambda.LExpr.LExpr.getVars t
                  ++ Lambda.LExpr.LExpr.getVars f
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl Hx)))
    have HmkMid : ∀ {x : Expression.Ident},
        x ∈ Imperative.HasVarsPure.getVars (P:=Expression) t →
        x ∈ Imperative.HasVarsPure.getVars (P:=Expression)
              (Lambda.LExpr.ite m c t f) := by
      intro x Hx
      show x ∈ Lambda.LExpr.LExpr.getVars c ++ Lambda.LExpr.LExpr.getVars t
                  ++ Lambda.LExpr.LExpr.getVars f
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr Hx)))
    have HmkRight : ∀ {x : Expression.Ident},
        x ∈ Imperative.HasVarsPure.getVars (P:=Expression) f →
        x ∈ Imperative.HasVarsPure.getVars (P:=Expression)
              (Lambda.LExpr.ite m c t f) := by
      intro x Hx
      show x ∈ Lambda.LExpr.LExpr.getVars c ++ Lambda.LExpr.LExpr.getVars t
                  ++ Lambda.LExpr.LExpr.getVars f
      exact List.mem_append.mpr (Or.inr Hx)
    have Hc := cih (fun v Hv Hnone => Hsurv v (HmkLeft Hv) Hnone)
                   (fun k w Hk Hf => Hsub k w (HmkLeft Hk) Hf)
    have Ht := tih (fun v Hv Hnone => Hsurv v (HmkMid Hv) Hnone)
                   (fun k w Hk Hf => Hsub k w (HmkMid Hk) Hf)
    have Hf' := fih (fun v Hv Hnone => Hsurv v (HmkRight Hv) Hnone)
                    (fun k w Hk Hf => Hsub k w (HmkRight Hk) Hf)
    exact Hwfc.itecongr σ' σ m _ _ _ _ _ _ Ht Hf' Hc
  | eq m e1 e2 e1ih e2ih =>
    simp only [Lambda.LExpr.substFvars_eq]
    have Hsurv_l :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) e1,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.eq m e1 e2)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inl Hv
    have Hsurv_r :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) e2,
          Map.find? sm v = none →
          δ σ' (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv Hnone
      apply Hsurv v ?_ Hnone
      show v ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.eq m e1 e2)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inr Hv
    have Hsub_l :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) e1 →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.eq m e1 e2)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inl Hk
    have Hsub_r :
        ∀ k w, k ∈ Imperative.HasVarsPure.getVars (P:=Expression) e2 →
          Map.find? sm k = some w →
          δ σ' w = δ σ (Lambda.LExpr.fvar () k none) := by
      intro k w Hk Hf
      apply Hsub k w ?_ Hf
      show k ∈ Lambda.LExpr.LExpr.getVars (Lambda.LExpr.eq m e1 e2)
      simp [Lambda.LExpr.LExpr.getVars, List.mem_append]
      exact Or.inr Hk
    have Hl := e1ih Hsurv_l Hsub_l
    have Hr := e2ih Hsurv_r Hsub_r
    exact Hwfc.eqcongr σ' σ m _ _ _ _ Hl Hr

/-! ### Small-step block helpers for assert/assume sequences -/

/-- Generic block-evaluator helper for assert/assume statement lists with
    substituted predicates. Parameterized by `mkStmt` (the `Statement.assert`
    or `Statement.assume` constructor) and `mkSingletonEval` (a function that
    builds a singleton `EvalStatementsContract` from the eval-true witness).
    Used to derive both `H_asserts` and `H_assumes`. -/
theorem H_check_block
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {entries : List (CoreLabel × Procedure.Check)}
    {md : Imperative.MetaData Expression}
    {labelPrefix : String}
    (mkStmt : String → Expression.Expr → Imperative.MetaData Expression → Statement)
    (mkSingletonEval :
      ∀ (lbl : String) (e : Expression.Expr) (m : Imperative.MetaData Expression),
        δ σ' e = some Imperative.HasBool.tt →
        EvalStatementsContract π φ ⟨σ', δ, false⟩ [mkStmt lbl e m] ⟨σ', δ, false⟩)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σA σ' (ks.zip ks'))
    (Hentries : ∀ entry, entry ∈ entries →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      (entries.mapIdx (fun i (lbl, check) =>
        mkStmt s!"{labelPrefix}{i}_{lbl}"
          (Lambda.LExpr.substFvars check.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (check.md.setCallSiteFileRange md)))
      ⟨σ', δ, false⟩ := by
  -- Generalize over the starting index of mapIdx so we can induct on the list.
  suffices Hgen :
      ∀ (i : Nat) (l : List (CoreLabel × Procedure.Check)),
        (∀ entry, entry ∈ l →
           Imperative.invStores σA σ'
             ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
                (ks ++ ks')) ∧
           ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
           δ σA entry.snd.expr = some Imperative.HasBool.tt) →
        EvalStatementsContract π φ ⟨σ', δ, false⟩
          (l.mapIdx (fun j (lbl, check) =>
            mkStmt s!"{labelPrefix}{i + j}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)))
          ⟨σ', δ, false⟩ by
    have := Hgen 0 entries Hentries
    simpa using this
  intros i l Hl
  induction l generalizing i with
  | nil =>
    simp [List.mapIdx]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons head tail ih =>
    obtain ⟨lbl, check⟩ := head
    have HtailHyp :
        ∀ entry, entry ∈ tail →
          Imperative.invStores σA σ'
            ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
              (ks ++ ks')) ∧
          ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
          δ σA entry.snd.expr = some Imperative.HasBool.tt := by
      intros entry hin; exact Hl entry (List.mem_cons_of_mem _ hin)
    have Htail := ih (i + 1) HtailHyp
    have HlHead := Hl (lbl, check) List.mem_cons_self
    obtain ⟨HinvHead, HnininHead, HevHead⟩ := HlHead
    have Heq : δ σA check.expr =
                δ σ' (Lambda.LExpr.substFvars check.expr
                        (ks.zip (Core.Transform.createFvars ks'))) :=
      subst_fvars_correct Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst HnininHead HinvHead
    have HevSubst : δ σ' (Lambda.LExpr.substFvars check.expr
                          (ks.zip (Core.Transform.createFvars ks'))) =
                    some Imperative.HasBool.tt := by
      rw [← Heq]; exact HevHead
    have HheadStmts := mkSingletonEval s!"{labelPrefix}{i}_{lbl}"
      (Lambda.LExpr.substFvars check.expr (ks.zip (Core.Transform.createFvars ks')))
      (check.md.setCallSiteFileRange md) HevSubst
    have Hcombined :
        EvalStatementsContract π φ ⟨σ', δ, false⟩
          ([mkStmt s!"{labelPrefix}{i}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)] ++
           tail.mapIdx (fun j p =>
              mkStmt s!"{labelPrefix}{i + 1 + j}_{p.fst}"
                (Lambda.LExpr.substFvars p.snd.expr
                  (ks.zip (Core.Transform.createFvars ks')))
                (p.snd.md.setCallSiteFileRange md)))
          ⟨σ', δ, false⟩ := EvalStatementsContractApp HheadStmts Htail
    have Hgoal_eq :
        ((lbl, check) :: tail).mapIdx (fun j p =>
            mkStmt s!"{labelPrefix}{i + j}_{p.fst}"
              (Lambda.LExpr.substFvars p.snd.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (p.snd.md.setCallSiteFileRange md)) =
        [mkStmt s!"{labelPrefix}{i}_{lbl}"
            (Lambda.LExpr.substFvars check.expr
              (ks.zip (Core.Transform.createFvars ks')))
            (check.md.setCallSiteFileRange md)] ++
        tail.mapIdx (fun j p =>
            mkStmt s!"{labelPrefix}{i + 1 + j}_{p.fst}"
              (Lambda.LExpr.substFvars p.snd.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (p.snd.md.setCallSiteFileRange md)) := by
      rw [List.mapIdx_cons]
      simp only [List.singleton_append, List.cons.injEq, Nat.add_zero, true_and]
      apply List.mapIdx_eq_iff.mpr
      intros k
      simp [List.getElem?_mapIdx]
      cases hh : tail[k]? with
      | none => rfl
      | some p =>
        have : i + 1 + k = i + (k + 1) := by omega
        rw [this]
    show EvalStatementsContract π φ ⟨σ', δ, false⟩
      (((lbl, check) :: tail).mapIdx (fun j p =>
        mkStmt s!"{labelPrefix}{i + j}_{p.fst}"
          (Lambda.LExpr.substFvars p.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (p.snd.md.setCallSiteFileRange md))) ⟨σ', δ, false⟩
    rw [Hgoal_eq]
    exact Hcombined

/-- Generic block-evaluator helper for the labels-aware (`zip`) variant of
    assert/assume statement lists.  Used to derive both `H_asserts_zip` and
    `H_assumes_zip`. -/
theorem H_check_block_zip
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {entries : List (CoreLabel × Procedure.Check)}
    {labels : List String}
    {md : Imperative.MetaData Expression}
    (mkStmt : String → Expression.Expr → Imperative.MetaData Expression → Statement)
    (mkSingletonEval :
      ∀ (lbl : String) (e : Expression.Expr) (m : Imperative.MetaData Expression),
        δ σ' e = some Imperative.HasBool.tt →
        EvalStatementsContract π φ ⟨σ', δ, false⟩ [mkStmt lbl e m] ⟨σ', δ, false⟩)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σA σ' (ks.zip ks'))
    (Hentries : ∀ entry, entry ∈ entries →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      ((entries.zip labels).map (fun (entry, lbl) =>
        mkStmt lbl
          (Lambda.LExpr.substFvars entry.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (entry.snd.md.setCallSiteFileRange md)))
      ⟨σ', δ, false⟩ := by
  induction entries generalizing labels with
  | nil =>
    simp [List.zip_nil_left, List.map_nil]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons head tail ih =>
    cases labels with
    | nil =>
      simp [List.zip_nil_right, List.map_nil]
      exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
    | cons lbl labels' =>
      obtain ⟨_, check⟩ := head
      have HtailHyp :
          ∀ entry, entry ∈ tail →
            Imperative.invStores σA σ'
              ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
                (ks ++ ks')) ∧
            ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
            δ σA entry.snd.expr = some Imperative.HasBool.tt := by
        intros entry hin; exact Hentries entry (List.mem_cons_of_mem _ hin)
      have Htail := ih (labels := labels') HtailHyp
      have HlHead := Hentries _ List.mem_cons_self
      obtain ⟨HinvHead, HnininHead, HevHead⟩ := HlHead
      have Heq : δ σA check.expr =
                  δ σ' (Lambda.LExpr.substFvars check.expr
                          (ks.zip (Core.Transform.createFvars ks'))) :=
        subst_fvars_correct Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst HnininHead HinvHead
      have HevSubst : δ σ' (Lambda.LExpr.substFvars check.expr
                            (ks.zip (Core.Transform.createFvars ks'))) =
                      some Imperative.HasBool.tt := by
        rw [← Heq]; exact HevHead
      have HheadStmts := mkSingletonEval lbl
        (Lambda.LExpr.substFvars check.expr (ks.zip (Core.Transform.createFvars ks')))
        (check.md.setCallSiteFileRange md) HevSubst
      simp only [List.zip_cons_cons, List.map_cons]
      exact EvalStatementsContractApp HheadStmts Htail

/-! ### Pure list-shape analogues of `createAsserts` / `createAssumes`.

    The monadic `Core.Transform.createAsserts` / `createAssumes` use a fresh
    label generator. For the small-step proof we need a pure-list version that
    we can induct over directly. -/

/-- Pure-list analogue of `Core.Transform.createAsserts` (without the
    monadic label generator). Produces `Statement.assert` statements,
    one per entry, with substituted predicates. -/
def createAsserts_list
    (entries : List (CoreLabel × Procedure.Check))
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String) :
    List Statement :=
  entries.mapIdx (fun i (l, check) =>
    Statement.assert s!"{labelPrefix}{i}_{l}"
                     (Lambda.LExpr.substFvars check.expr subst)
                     (check.md.setCallSiteFileRange md))

/-- Pure-list analogue of `Core.Transform.createAssumes`. -/
def createAssumes_list
    (entries : List (CoreLabel × Procedure.Check))
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String) :
    List Statement :=
  entries.mapIdx (fun i (l, check) =>
    Statement.assume s!"{labelPrefix}{i}_{l}"
                     (Lambda.LExpr.substFvars check.expr subst)
                     (check.md.setCallSiteFileRange md))

/-- A list of `Statement.assert` with substituted predicates evaluates from
    σ' to σ' (store unchanged) under contract semantics, given that each
    substituted predicate evaluates to `tt` in σ' and the substitution
    well-formedness assumptions hold. -/
theorem H_asserts
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {pres : List (CoreLabel × Procedure.Check)}
    {md : Imperative.MetaData Expression}
    {labelPrefix : String}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σ' σA (ks'.zip ks))
    (Hpres : ∀ entry, entry ∈ pres →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      (createAsserts_list pres (ks.zip (Core.Transform.createFvars ks')) md labelPrefix)
      ⟨σ', δ, false⟩ := by
  have Hsubst' : Imperative.substStores σA σ' (ks.zip ks') := by
    apply Imperative.substStoresFlip'
    simp [Imperative.substSwap, zip_swap]
    exact Hsubst
  have := H_check_block (π := π) (φ := φ) (md := md) (labelPrefix := labelPrefix)
    (entries := pres) Statement.assert
    (mkSingletonEval := singletonAssertEval Hwfb)
    Hwfvr Hwfvl Hwfc Hlen Hnd Hdef Hsubst' Hpres
  simpa [createAsserts_list] using this

/-- Symmetric to `H_asserts`: a list of `Statement.assume` with substituted
    predicates evaluates from σ' to σ'. -/
theorem H_assumes
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {posts : List (CoreLabel × Procedure.Check)}
    {md : Imperative.MetaData Expression}
    {labelPrefix : String}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σA σ' (ks.zip ks'))
    (Hposts : ∀ entry, entry ∈ posts →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      (createAssumes_list posts (ks.zip (Core.Transform.createFvars ks')) md labelPrefix)
      ⟨σ', δ, false⟩ := by
  have := H_check_block (π := π) (φ := φ) (md := md) (labelPrefix := labelPrefix)
    (entries := posts) Statement.assume
    (mkSingletonEval := singletonAssumeEval Hwfb)
    Hwfvr Hwfvl Hwfc Hlen Hnd Hdef Hsubst Hposts
  simpa [createAssumes_list] using this

/-- Labels-aware variant of `H_asserts`: takes a separate `labels`
    list (paired positionally with `pres` via `zip`) rather than a
    `labelOf` projection.  This matches the shape exposed by the
    `HassertsShape` clause of `callElimCmd_call_eq` (B3 layer), which
    forms the asserts list as `(pres.zip labels).map (fun (entry, lbl) => …)`. -/
theorem H_asserts_zip
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {pres : List (CoreLabel × Procedure.Check)}
    {labels : List String}
    {md : Imperative.MetaData Expression}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σ' σA (ks'.zip ks))
    (Hpres : ∀ entry, entry ∈ pres →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      ((pres.zip labels).map (fun (entry, lbl) =>
        Statement.assert lbl
          (Lambda.LExpr.substFvars entry.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (entry.snd.md.setCallSiteFileRange md)))
      ⟨σ', δ, false⟩ := by
  have Hsubst' : Imperative.substStores σA σ' (ks.zip ks') := by
    apply Imperative.substStoresFlip'
    simp [Imperative.substSwap, zip_swap]
    exact Hsubst
  exact H_check_block_zip (entries := pres) (labels := labels) Statement.assert
    (mkSingletonEval := singletonAssertEval Hwfb)
    Hwfvr Hwfvl Hwfc Hlen Hnd Hdef Hsubst' Hpres

/-- Labels-aware variant of `H_assumes`: takes a separate `labels`
    list (paired positionally with `posts` via `zip`) rather than a
    `labelOf` projection.  This matches the shape exposed by the
    `HassumesShape` clause of `callElimCmd_call_eq` (B3 layer), which
    forms the assumes list as `(posts.zip labels).map (fun (entry, lbl) => …)`. -/
theorem H_assumes_zip
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {posts : List (CoreLabel × Procedure.Check)}
    {labels : List String}
    {md : Imperative.MetaData Expression}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σA σ' (ks.zip ks'))
    (Hposts : ∀ entry, entry ∈ posts →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      ((posts.zip labels).map (fun (entry, lbl) =>
        Statement.assume lbl
          (Lambda.LExpr.substFvars entry.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (entry.snd.md.setCallSiteFileRange md)))
      ⟨σ', δ, false⟩ :=
  H_check_block_zip (entries := posts) (labels := labels) Statement.assume
    (mkSingletonEval := singletonAssumeEval Hwfb)
    Hwfvr Hwfvl Hwfc Hlen Hnd Hdef Hsubst Hposts

/-- Helper: lifting `ReadValues σ ks vs` across an `updatedStates` extension
    by names disjoint from `ks`. Live-code analogue of the legacy
    `ReadValuesUpdatedStates`. -/
theorem readValues_updatedStates
    {σ : CoreStore} {ks ks' : List Expression.Ident}
    {vs : List Expression.Expr} {vs' : List Expression.Expr}
    (Hlen : ks'.length = vs'.length)
    (Hdisj : ks.Disjoint ks')
    (Hrd : ReadValues σ ks vs) :
    ReadValues (updatedStates σ ks' vs') ks vs := by
  induction ks' generalizing σ vs' with
  | nil =>
    cases vs' <;> simp_all [updatedStates, updatedStates']
  | cons k' ks'' ih =>
    cases vs' with
    | nil => simp at Hlen
    | cons v' vs'' =>
      simp only [updatedStates, List.zip_cons_cons, updatedStates']
      have Hdisj' : ks.Disjoint ks'' := by
        intro x Hin1 Hin2
        exact Hdisj Hin1 (List.mem_cons_of_mem _ Hin2)
      -- Prove ReadValues (updatedState σ k' v') ks vs using readValues_updatedState.
      have Hk'_notin : ¬ k' ∈ ks := by
        intro Hin
        exact Hdisj Hin List.mem_cons_self
      have Hrd_step : ReadValues (updatedState σ k' v') ks vs :=
        readValues_updatedState (k:=k') (v:=v') Hk'_notin Hrd
      have Hlen' : ks''.length = vs''.length := by
        simp at Hlen
        exact Hlen
      -- Apply ih on the remaining list.
      exact ih (σ:=updatedState σ k' v') Hlen' Hdisj' Hrd_step

/-- Lift `ReadValues σ ks vs` across three nested `updatedStates` extensions
    given `ks` is disjoint from each layer.  Used to bridge a base read in
    `σ` to the σ_old / σ_havoc 3-layer initialization in CallElim. -/
theorem readValues_3layer_lift
    {σ : CoreStore} {ks : List Expression.Ident} {vs : List Expression.Expr}
    {ts1 ts2 ts3 : List Expression.Ident}
    {vs1 vs2 vs3 : List Expression.Expr}
    (Hlen1 : ts1.length = vs1.length) (Hdisj1 : ks.Disjoint ts1)
    (Hlen2 : ts2.length = vs2.length) (Hdisj2 : ks.Disjoint ts2)
    (Hlen3 : ts3.length = vs3.length) (Hdisj3 : ks.Disjoint ts3)
    (Hrd : ReadValues σ ks vs) :
    ReadValues
      (updatedStates
        (updatedStates (updatedStates σ ts1 vs1) ts2 vs2) ts3 vs3) ks vs :=
  readValues_updatedStates Hlen3 Hdisj3
    (readValues_updatedStates Hlen2 Hdisj2
      (readValues_updatedStates Hlen1 Hdisj1 Hrd))

/-- Lift `Imperative.isDefined σ lhs` across three nested `updatedStates`
    extensions given `lhs` is disjoint from each layer. -/
theorem isDefined_3layer_lift
    {σ : CoreStore} {lhs : List Expression.Ident}
    {ts1 ts2 ts3 : List Expression.Ident}
    {vs1 vs2 vs3 : List Expression.Expr}
    (Hdisj1 : lhs.Disjoint ts1) (Hdisj2 : lhs.Disjoint ts2)
    (Hdisj3 : lhs.Disjoint ts3)
    (Hdef : Imperative.isDefined σ lhs) :
    Imperative.isDefined
      (updatedStates
        (updatedStates (updatedStates σ ts1 vs1) ts2 vs2) ts3 vs3) lhs :=
  fun v Hv => by
    rw [updatedStates_get_notin (fun Hin => Hdisj3 Hv Hin),
        updatedStates_get_notin (fun Hin => Hdisj2 Hv Hin),
        updatedStates_get_notin (fun Hin => Hdisj1 Hv Hin)]
    exact Hdef v Hv

/-! ### Temp-extension lift helpers

`updateState_updatedStates_lift` / `havocVars_updatedStates_lift` lift a
single `UpdateState` / `HavocVars` derivation across an `updatedStates` temp
extension, given suitable disjointness. -/

/-- A single `UpdateState` lifts across an `updatedStates` temp extension as
    long as the updated variable `x` is disjoint from the temp variables. -/
theorem updateState_updatedStates_lift
    {σ σ' : CoreStore} {x : Expression.Ident} {v : Expression.Expr}
    {tempVars : List Expression.Ident} {tempVals : List Expression.Expr}
    (Hnotin : ¬ x ∈ tempVars)
    (Hup : Imperative.UpdateState (P:=Expression) σ x v σ') :
    Imperative.UpdateState (P:=Expression)
      (updatedStates σ tempVars tempVals) x v
      (updatedStates σ' tempVars tempVals) := by
  cases Hup with
  | update Hsome Hsome' Hother =>
    rename_i v'
    -- Lookup x in extended σ.
    have HlookupL :
        (updatedStates σ tempVars tempVals) x = some v' := by
      simp [updatedStates]
      have : ∀ (ts : List Expression.Ident) (vs : List Expression.Expr) (s : CoreStore),
          ¬ x ∈ ts → s x = some v' →
          (updatedStates' s (ts.zip vs)) x = some v' := by
        intro ts
        induction ts with
        | nil => intros vs s _ Hs; simp [updatedStates']; exact Hs
        | cons t ts ih =>
          intro vs s Hxn Hs
          cases vs with
          | nil => simp [updatedStates', List.zip]; exact Hs
          | cons w ws =>
            simp [updatedStates', List.zip, List.zipWith]
            have Hxt : x ≠ t := fun h => Hxn (h ▸ List.mem_cons_self)
            have Hxts : ¬ x ∈ ts := fun h => Hxn (List.mem_cons_of_mem _ h)
            have HsTail : (updatedState s t w) x = some v' := by
              simp [updatedState, Hxt]; exact Hs
            exact ih ws (updatedState s t w) Hxts HsTail
      exact this tempVars tempVals σ Hnotin Hsome
    have HlookupR :
        (updatedStates σ' tempVars tempVals) x = some v := by
      simp [updatedStates]
      have : ∀ (ts : List Expression.Ident) (vs : List Expression.Expr) (s : CoreStore),
          ¬ x ∈ ts → s x = some v →
          (updatedStates' s (ts.zip vs)) x = some v := by
        intro ts
        induction ts with
        | nil => intros vs s _ Hs; simp [updatedStates']; exact Hs
        | cons t ts ih =>
          intro vs s Hxn Hs
          cases vs with
          | nil => simp [updatedStates', List.zip]; exact Hs
          | cons w ws =>
            simp [updatedStates', List.zip, List.zipWith]
            have Hxt : x ≠ t := fun h => Hxn (h ▸ List.mem_cons_self)
            have Hxts : ¬ x ∈ ts := fun h => Hxn (List.mem_cons_of_mem _ h)
            have HsTail : (updatedState s t w) x = some v := by
              simp [updatedState, Hxt]; exact Hs
            exact ih ws (updatedState s t w) Hxts HsTail
      exact this tempVars tempVals σ' Hnotin Hsome'
    have Hframe : ∀ y, x ≠ y →
        (updatedStates σ' tempVars tempVals) y =
        (updatedStates σ tempVars tempVals) y := by
      intro y Hne
      simp [updatedStates]
      -- Induct over tempVars, tempVals together.
      have : ∀ (ts : List Expression.Ident) (vs : List Expression.Expr)
              (s s2 : CoreStore),
          (∀ z, x ≠ z → s2 z = s z) →
          (updatedStates' s2 (ts.zip vs)) y =
          (updatedStates' s (ts.zip vs)) y := by
        intro ts
        induction ts with
        | nil => intros vs s s2 Hs2; simp [updatedStates']; exact Hs2 y Hne
        | cons t ts ih =>
          intro vs s s2 Hs2
          cases vs with
          | nil => simp [updatedStates', List.zip]; exact Hs2 y Hne
          | cons w ws =>
            simp [updatedStates', List.zip, List.zipWith]
            apply ih ws (updatedState s t w) (updatedState s2 t w)
            intro z Hxz
            simp [updatedState]
            split
            · rfl
            · exact Hs2 z Hxz
      exact this tempVars tempVals σ σ' Hother
    exact Imperative.UpdateState.update HlookupL HlookupR Hframe

/-- Lift a `HavocVars` derivation across a temp-extension, given the havoc'd
    variables are disjoint from the temp variables. -/
theorem havocVars_updatedStates_lift
    {σ σ' : CoreStore} {ks tempVars : List Expression.Ident}
    {tempVals : List Expression.Expr}
    (Hdisj : ks.Disjoint tempVars)
    (Hhav : HavocVars σ ks σ') :
    HavocVars (updatedStates σ tempVars tempVals) ks
              (updatedStates σ' tempVars tempVals) := by
  induction Hhav with
  | update_none => exact HavocVars.update_none
  | @update_some σ_a x v σ_b ks_t σ_c hUp hTail ih =>
    have Hxnotin : ¬ x ∈ tempVars :=
      fun hin => Hdisj (List.mem_cons_self) hin
    have Hdisj_t : ks_t.Disjoint tempVars := by
      intro y Hy_in_t Hy_in_temp
      exact Hdisj (List.mem_cons_of_mem _ Hy_in_t) Hy_in_temp
    have hUp' : Imperative.UpdateState (P:=Expression)
                  (updatedStates σ_a tempVars tempVals) x v
                  (updatedStates σ_b tempVars tempVals) :=
      updateState_updatedStates_lift Hxnotin hUp
    have hTail' : HavocVars (updatedStates σ_b tempVars tempVals) ks_t
                            (updatedStates σ_c tempVars tempVals) :=
      ih Hdisj_t
    exact HavocVars.update_some hUp' hTail'

/-- Glue lemma: chain L1–L6 via `EvalStatementsContractApp` to produce the
    full call-elim block evaluation from σ to σ_havoc. -/
theorem EvalCallElim_glue
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ σ_arg σ_out σ_old σ_havoc : CoreStore}
    {argInit outInit oldInit asserts havocs assumes : List Statement}
    (HL1 : EvalStatementsContract π φ ⟨σ, δ, false⟩ argInit ⟨σ_arg, δ, false⟩)
    (HL2 : EvalStatementsContract π φ ⟨σ_arg, δ, false⟩ outInit ⟨σ_out, δ, false⟩)
    (HL3 : EvalStatementsContract π φ ⟨σ_out, δ, false⟩ oldInit ⟨σ_old, δ, false⟩)
    (HL4 : EvalStatementsContract π φ ⟨σ_old, δ, false⟩ asserts ⟨σ_old, δ, false⟩)
    (HL5 : EvalStatementsContract π φ ⟨σ_old, δ, false⟩ havocs ⟨σ_havoc, δ, false⟩)
    (HL6 : EvalStatementsContract π φ ⟨σ_havoc, δ, false⟩ assumes ⟨σ_havoc, δ, false⟩) :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      (argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes)
      ⟨σ_havoc, δ, false⟩ := by
  have H12 := EvalStatementsContractApp HL1 HL2
  have H123 := EvalStatementsContractApp H12 HL3
  have H1234 := EvalStatementsContractApp H123 HL4
  have H12345 := EvalStatementsContractApp H1234 HL5
  exact EvalStatementsContractApp H12345 HL6

end

end Core.Transform

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Util.List
import all Strata.DL.Util.Maps
import all Strata.DL.Util.Map
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
## Theorems for Type Substitution and Unification

Properties of substitution and the soundness of `Constraints.unify`.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

public section

theorem SubstWF.not_mem_freeVars_of_find (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    a ∉ LMonoTy.freeVars t := by
  simp [SubstWF] at h_wf
  have h_key := Maps.find?_mem_keys S h_find
  have h_fv_subset := Subst.freeVars_of_find_subset S h_find
  grind

/-- Absorption for type lists: the single substitution is absorbed element-wise. -/
theorem LMonoTys.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mtys : LMonoTys)
    (hS : Subst.hasEmptyScopes S = false)
    (hSingle : Subst.hasEmptyScopes [[(a, t)]] = false)
    (ih : ∀ m, m ∈ mtys → LMonoTy.subst S (LMonoTy.subst [[(a, t)]] m) = LMonoTy.subst S m) :
    LMonoTys.subst S (LMonoTys.subst [[(a, t)]] mtys) = LMonoTys.subst S mtys := by
  rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
  induction mtys with
  | nil => simp [LMonoTys.substLogic, hS, hSingle]
  | cons m rest ih_rest =>
    simp only [LMonoTys.substLogic, hS, hSingle, Bool.false_eq_true, ↓reduceIte]
    grind

/--
#### Absorption: relating substitutions produced by successive resolveAux calls

Absorption: `subst S (subst [(a,t)] mty) = subst S mty` when `Maps.find? S a = some t`
and `SubstWF S`. The single-variable substitution `[(a,t)]` is "absorbed" by `S`
because `S` already maps `a` to `t`.
-/
theorem LMonoTy.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mty : LMonoTy) (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S (LMonoTy.subst [[(a, t)]] mty) = LMonoTy.subst S mty := by
  have hS : Subst.hasEmptyScopes S = false :=
    Subst.hasEmptyScopes_false_of_find S a t h_find
  have hSingle : Subst.hasEmptyScopes [[(a, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  induction mty with
  | ftvar x =>
    by_cases h_eq : a = x
    · -- x = a: inner subst gives t, then subst S t = t = subst S (ftvar a)
      subst h_eq
      have h_inner : LMonoTy.subst [[(a, t)]] (.ftvar a) = t := by
        simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?]
      rw [h_inner]
      simp [LMonoTy.subst, hS, h_find]
      exact LMonoTy.subst_idempotent_value S a t h_find h_wf
    · -- x ≠ a: inner subst is identity
      have h_inner : LMonoTy.subst [[(a, t)]] (.ftvar x) = .ftvar x := by
        simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?, h_eq]
      rw [h_inner]
  | bitvec n =>
    simp [LMonoTy.subst]
  | tcons name args ih =>
    simp only [LMonoTy.subst, hSingle, hS, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact LMonoTys.subst_absorbs_single S a t args hS hSingle ih

/-!
When `resolveAux` processes subexpressions, each call extends the substitution.
The key property is that later substitutions "absorb" earlier ones: applying the
outer substitution after the inner one is the same as applying the outer alone.

This lets us upgrade typing judgments from an inner substitution to the final one.
-/

/--
`S_outer` absorbs `S_inner` means: for every binding `a ↦ t` in `S_inner`,
`subst S_outer t = subst S_outer (ftvar a)`. In other words, `S_outer` already
"knows about" every binding in `S_inner`.
-/
def Subst.absorbs (S_outer S_inner : Subst) : Prop :=
  ∀ a t, Maps.find? S_inner a = some t →
    LMonoTy.subst S_outer t = LMonoTy.subst S_outer (.ftvar a)

/--
Absorption implies substitution composition collapses:
`subst S_outer (subst S_inner mty) = subst S_outer mty`.
-/
theorem LMonoTy.subst_absorbs (S_outer S_inner : Subst) (mty : LMonoTy)
    (h : Subst.absorbs S_outer S_inner) :
    LMonoTy.subst S_outer (LMonoTy.subst S_inner mty) = LMonoTy.subst S_outer mty := by
  by_cases h_emptyI : Subst.hasEmptyScopes S_inner
  · rw [LMonoTy.subst_emptyS h_emptyI]
  · have hInner : Subst.hasEmptyScopes S_inner = false := by
      revert h_emptyI; cases Subst.hasEmptyScopes S_inner <;> simp
    induction mty with
    | ftvar x =>
      cases h_find : Maps.find? S_inner x with
      | none =>
        have : LMonoTy.subst S_inner (.ftvar x) = .ftvar x := by
          simp [LMonoTy.subst, hInner, h_find]
        rw [this]
      | some t =>
        have : LMonoTy.subst S_inner (.ftvar x) = t := by
          simp [LMonoTy.subst, hInner, h_find]
        rw [this]; exact h x t h_find
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      have h_inner : LMonoTy.subst S_inner (.tcons name args) =
          .tcons name (LMonoTys.subst S_inner args) := by
        unfold LMonoTy.subst; simp only [hInner, Bool.false_eq_true, ↓reduceIte]
      rw [h_inner]
      by_cases h_emptyO : Subst.hasEmptyScopes S_outer
      · rw [LMonoTy.subst_emptyS h_emptyO, LMonoTy.subst_emptyS h_emptyO]
        congr 1
        rw [LMonoTys.subst_eq_substLogic]
        suffices ∀ xs, (∀ m, m ∈ xs → LMonoTy.subst S_inner m = m) →
            LMonoTys.substLogic S_inner xs = xs by
          exact this args (fun m hm => by
            have := ih m hm
            simp only [LMonoTy.subst_emptyS h_emptyO] at this; exact this)
        intro xs; induction xs with
        | nil => intro _; simp [LMonoTys.substLogic, hInner]
        | cons a rest ih_rest =>
          intro ih_cons
          simp only [LMonoTys.substLogic, hInner, Bool.false_eq_true, ↓reduceIte]
          rw [ih_cons a List.mem_cons_self,
              ih_rest (fun m hm => ih_cons m (List.mem_cons_of_mem a hm))]
      · have hOuter : Subst.hasEmptyScopes S_outer = false := by
          revert h_emptyO; cases Subst.hasEmptyScopes S_outer <;> simp
        have h_l : LMonoTy.subst S_outer (.tcons name (LMonoTys.subst S_inner args)) =
            .tcons name (LMonoTys.subst S_outer (LMonoTys.subst S_inner args)) := by
          unfold LMonoTy.subst; simp only [hOuter, Bool.false_eq_true, ↓reduceIte]
        have h_r : LMonoTy.subst S_outer (.tcons name args) =
            .tcons name (LMonoTys.subst S_outer args) := by
          unfold LMonoTy.subst; simp only [hOuter, Bool.false_eq_true, ↓reduceIte]
        rw [h_l, h_r]; congr 1
        rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic,
            LMonoTys.subst_eq_substLogic]
        suffices ∀ xs,
            (∀ m, m ∈ xs → LMonoTy.subst S_outer (LMonoTy.subst S_inner m) =
              LMonoTy.subst S_outer m) →
            LMonoTys.substLogic S_outer (LMonoTys.substLogic S_inner xs) =
              LMonoTys.substLogic S_outer xs by
          exact this args (fun m hm => ih m hm)
        intro xs; induction xs with
        | nil => intro _; simp [LMonoTys.substLogic, hOuter, hInner]
        | cons a rest ih_rest =>
          intro ih_cons
          simp only [LMonoTys.substLogic, hOuter, hInner, Bool.false_eq_true, ↓reduceIte]
          rw [ih_cons a List.mem_cons_self,
              ih_rest (fun m hm => ih_cons m (List.mem_cons_of_mem a hm))]

theorem LMonoTy.subst_eq_of_absorbs (S S_inner : Subst) (ty1 ty2 : LMonoTy)
    (h_abs : Subst.absorbs S S_inner)
    (h_eq : LMonoTy.subst S_inner ty1 = LMonoTy.subst S_inner ty2) :
    LMonoTy.subst S ty1 = LMonoTy.subst S ty2 := by
  have h1 := (LMonoTy.subst_absorbs S S_inner ty1 h_abs).symm
  have h2 := LMonoTy.subst_absorbs S S_inner ty2 h_abs
  rw [h1, h_eq, h2]

/-- Every well-formed substitution absorbs itself. -/
theorem Subst.absorbs_refl (S : Subst) (h_wf : SubstWF S) :
    Subst.absorbs S S := by
  intro a t h_find
  have h_not_empty := Subst.hasEmptyScopes_false_of_find S a t h_find
  have : LMonoTy.subst S (.ftvar a) = t := by
    simp [LMonoTy.subst, h_not_empty, h_find]
  rw [this]
  exact LMonoTy.subst_idempotent_value S a t h_find h_wf

/-- Absorption is transitive: if `S2` absorbs `S1` and `S3` absorbs `S2`,
    then `S3` absorbs `S1`. -/
theorem Subst.absorbs_trans (S1 S2 S3 : Subst)
    (h12 : Subst.absorbs S2 S1) (h23 : Subst.absorbs S3 S2) :
    Subst.absorbs S3 S1 := by
  intro a t h_find
  have h1 := h12 a t h_find
  rw [← LMonoTy.subst_absorbs S3 S2 t h23, h1,
      LMonoTy.subst_absorbs S3 S2 (.ftvar a) h23]

/--
Composition lemma: applying a singleton substitution `[[(v, t)]]` followed by
`[ys]` equals applying the merged substitution `[(v, t) :: ys]`, provided
`subst [ys] t = t` (i.e., `t` is stable under `ys`).

This is a key lemma for proving that sequential `tinst` applications
(each substituting one bound variable) produce the same result as a
single parallel substitution with all bindings.
-/

theorem LMonoTy.subst_cons_single
    (v : TyIdentifier) (t : LMonoTy) (ys : SubstOne) (mty : LMonoTy)
    (h_t : LMonoTy.subst [ys] t = t) :
    LMonoTy.subst [ys] (LMonoTy.subst [[(v, t)]] mty) =
    LMonoTy.subst [((v, t) :: ys)] mty := by
  have hSingle : Subst.hasEmptyScopes [[(v, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  have hCons : Subst.hasEmptyScopes [((v, t) :: ys)] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  by_cases hYs : Subst.hasEmptyScopes [ys]
  · -- ys is empty, so subst [ys] is identity
    have h_ys_empty : ys = [] := by
      simp [Subst.hasEmptyScopes, Map.isEmpty] at hYs
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hYs
    subst h_ys_empty
    simp only [LMonoTy.subst_emptyS hYs]
  · have hYs_ne : Subst.hasEmptyScopes [ys] = false := by
      revert hYs; cases Subst.hasEmptyScopes [ys] <;> simp
    induction mty with
    | ftvar x =>
      by_cases h_eq : v = x
      · -- v = x: inner subst gives t, then subst [ys] t = t by h_t
        subst h_eq
        have h_inner : LMonoTy.subst [[(v, t)]] (.ftvar v) = t := by
          simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?]
        rw [h_inner, h_t]
        -- RHS: subst [(v,t)::ys] (ftvar v) = t (first match in (v,t)::ys)
        simp [LMonoTy.subst, hCons, Maps.find?, Map.find?]
      · -- v ≠ x: inner subst is identity, lookup x in ys
        have h_inner : LMonoTy.subst [[(v, t)]] (.ftvar x) = .ftvar x := by
          simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?, h_eq]
        rw [h_inner]
        -- Both sides look up x in ys (since v ≠ x, (v,t)::ys skips (v,t))
        simp [LMonoTy.subst, hYs_ne, hCons, Maps.find?, Map.find?, h_eq]
    | bitvec n =>
      simp [LMonoTy.subst]
    | tcons name args ih =>
      simp only [LMonoTy.subst, hSingle, hYs_ne, hCons, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic,
          LMonoTys.subst_eq_substLogic]
      suffices ∀ xs,
          (∀ m, m ∈ xs → LMonoTy.subst [ys] (LMonoTy.subst [[(v, t)]] m) =
            LMonoTy.subst [((v, t) :: ys)] m) →
          LMonoTys.substLogic [ys] (LMonoTys.substLogic [[(v, t)]] xs) =
            LMonoTys.substLogic [((v, t) :: ys)] xs by
        exact this args ih
      intro xs; induction xs with
      | nil => intro _; simp [LMonoTys.substLogic, hSingle, hYs_ne, hCons]
      | cons a rest ih_rest =>
        intro ih_xs
        simp only [LMonoTys.substLogic, hSingle, hYs_ne, hCons, Bool.false_eq_true, ↓reduceIte]
        rw [ih_xs a List.mem_cons_self,
            ih_rest (fun m hm => ih_xs m (List.mem_cons_of_mem a hm))]

-- Helper: applyLogic preserves some bindings.
private theorem Map.find?_applyLogic_some_h' {new old : SubstOne} {a : TyIdentifier} {t : LMonoTy}
    (h : Map.find? old a = some t) :
    Map.find? (SubstOne.applyLogic new old) a = some (LMonoTy.subst [new] t) := by
  induction old with
  | nil => simp [Map.find?] at h
  | cons hd rest ih =>
    simp only [SubstOne.applyLogic, Map.find?]
    simp only [Map.find?] at h
    grind

-- Helper: applyLogic preserves none bindings.
private theorem Map.find?_applyLogic_none_h' {new old : SubstOne} {a : TyIdentifier}
    (h : Map.find? old a = none) :
    Map.find? (SubstOne.applyLogic new old) a = none := by
  induction old with
  | nil => simp [SubstOne.applyLogic, Map.find?]
  | cons hd rest ih =>
    simp [SubstOne.applyLogic, Map.find?]
    simp [Map.find?] at h
    grind

-- Helper: Subst.apply preserves some bindings.
private theorem Maps.find?_apply_some_h' {new : SubstOne} {old : Subst} {a : TyIdentifier} {t : LMonoTy}
    (h : Maps.find? old a = some t) :
    Maps.find? (Subst.apply new old) a = some (LMonoTy.subst [new] t) := by
  induction old with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Subst.apply, Maps.find?]
    simp only [Maps.find?] at h
    rw [SubstOne.apply_eq_applyLogic]
    cases h_ma : Map.find? m a with
    | none =>
      rw [h_ma] at h
      rw [Map.find?_applyLogic_none_h' h_ma]
      exact ih h
    | some val =>
      rw [h_ma] at h; simp only [Option.some.injEq] at h; subst h
      rw [Map.find?_applyLogic_some_h' h_ma]

-- Helper: Except.mapError preserves ok values.
private theorem Except.mapError_ok_h' {α β γ : Type} {f : α → β} {e : Except α γ} {v : γ}
    (h : Except.mapError f e = .ok v) : e = .ok v := by
  cases e with
  | error a => simp [Except.mapError] at h
  | ok val => simp [Except.mapError] at h; exact congrArg Except.ok h

-- Helper: insert+apply produces an absorbing substitution.
private theorem absorbs_of_insert_apply_h' (S : SubstInfo) (id : TyIdentifier) (lty : LMonoTy)
    (h_none : Maps.find? S.subst id = none)
    (h_wf : SubstWF ((Subst.apply [(id, lty)] S.subst).insert id lty)) :
    Subst.absorbs ((Subst.apply [(id, lty)] S.subst).insert id lty) S.subst := by
  intro a t h_find
  have h_a_ne_id : a ≠ id := by
    intro h_eq; subst h_eq; rw [h_find] at h_none; simp at h_none
  let S_new := (Subst.apply [(id, lty)] S.subst).insert id lty
  have h_apply_a := Maps.find?_apply_some_h' (new := [(id, lty)]) h_find
  have h_find_new : Maps.find? S_new a = some (LMonoTy.subst [[(id, lty)]] t) := by
    show Maps.find? (Maps.insert _ id lty) a = _
    rw [Maps.find?_insert_ne _ _ _ _ h_a_ne_id]
    exact h_apply_a
  have h_find_id : Maps.find? S_new id = some lty := Maps.find?_insert_self _ id lty
  have h_not_empty := Subst.hasEmptyScopes_false_of_find S_new a _ h_find_new
  have h_subst_ftvar : LMonoTy.subst S_new (.ftvar a) = LMonoTy.subst [[(id, lty)]] t := by
    simp [LMonoTy.subst, h_not_empty, h_find_new]
  have h_idem := LMonoTy.subst_idempotent_value S_new a _ h_find_new h_wf
  have h_abs := LMonoTy.subst_absorbs_single S_new id lty t h_find_id h_wf
  rw [h_subst_ftvar, ← h_abs, h_idem]

/-- After inserting `(id, lty)` into the applied substitution, `subst _ (ftvar id) = lty`. -/
private theorem subst_ftvar_new_binding
    (S : Subst) (id : TyIdentifier) (lty : LMonoTy)
    (_h_none : Maps.find? S id = none) :
    LMonoTy.subst (Maps.insert (Subst.apply [(id, lty)] S) id lty) (LMonoTy.ftvar id) = lty := by
  have h_find := Maps.find?_insert_self (Subst.apply [(id, lty)] S) id lty
  have h_not_empty : ¬Subst.hasEmptyScopes (Maps.insert (Subst.apply [(id, lty)] S) id lty) := by
    intro h_empty
    exact absurd ((Subst.isEmpty_implies_keys_empty h_empty) ▸ Maps.find?_mem_keys _ h_find) (by simp)
  unfold LMonoTy.subst; simp [h_not_empty, h_find]

/-- When `S.find? id = none`, the new substitution absorbs `S` and maps `orig_lty` to `lty`. -/
private theorem subst_orig_new_binding
    (S : Subst) (id : TyIdentifier) (lty orig_lty : LMonoTy)
    (h_none : Maps.find? S id = none)
    (h_lty : lty = LMonoTy.subst S orig_lty)
    (h_occurs : ¬(id ∈ lty.freeVars)) :
    LMonoTy.subst (Maps.insert (Subst.apply [(id, lty)] S) id lty) orig_lty = lty := by
  subst h_lty
  have h_find_S'_id : Maps.find? (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
      id (LMonoTy.subst S orig_lty)) id = some (LMonoTy.subst S orig_lty) :=
    Maps.find?_insert_self _ _ _
  have hS' : Subst.hasEmptyScopes (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
      id (LMonoTy.subst S orig_lty)) = false :=
    Subst.hasEmptyScopes_false_of_find _ id _ h_find_S'_id
  have h_find_ne : ∀ x, x ≠ id →
      Maps.find? (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
        id (LMonoTy.subst S orig_lty)) x =
      (Maps.find? S x).map (LMonoTy.subst [[(id, LMonoTy.subst S orig_lty)]]) := fun x hx =>
    (Maps.find?_insert_ne _ _ _ _ hx).trans (Subst.find?_apply _ _ _)
  have h_single_noop : ∀ t : LMonoTy, ¬(id ∈ t.freeVars) →
      LMonoTy.subst [[(id, LMonoTy.subst S orig_lty)]] t = t := fun t ht =>
    LMonoTy.subst_no_relevant_keys _ _ (fun x hx => by
      simp [Maps.keys, Map.keys]; intro heq; subst heq; exact ht hx)
  by_cases hS : Subst.hasEmptyScopes S
  · simp only [LMonoTy.subst_emptyS hS] at h_occurs h_find_ne ⊢
    apply LMonoTy.subst_no_relevant_keys
    intro x hx
    have h_ne : x ≠ id := fun h => h_occurs (h ▸ hx)
    exact Maps.find?_of_not_mem_values _ (by
      rw [h_find_ne x h_ne, Maps.not_mem_keys_find?_none' S x
        ((Subst.isEmpty_implies_keys_empty hS) ▸ (by simp))]; simp)
  · have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    suffices ∀ mty, ¬(id ∈ (LMonoTy.subst S mty).freeVars) →
        LMonoTy.subst (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
          id (LMonoTy.subst S orig_lty)) mty = LMonoTy.subst S mty from
      this orig_lty h_occurs
    intro mty h_nf
    induction mty with
    | ftvar x =>
      by_cases h_id : x = id
      · subst h_id; exfalso; apply h_nf
        simp [LMonoTy.subst, hS_ne, h_none, LMonoTy.freeVars]
      · unfold LMonoTy.subst
        simp only [hS', hS_ne, Bool.false_eq_true, ↓reduceIte, h_find_ne x h_id]
        cases h_fx : Maps.find? S x with
        | none => simp
        | some t =>
          simp only [Option.map]
          exact h_single_noop t (by
            have : LMonoTy.subst S (.ftvar x) = t := by
              simp [LMonoTy.subst, hS_ne, h_fx]
            rwa [this] at h_nf)
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      unfold LMonoTy.subst
      simp only [hS', hS_ne, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
      have h_nf' : ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S args)) := by
        have h_eq : LMonoTy.subst S (.tcons name args) =
            .tcons name (LMonoTys.subst S args) := by
          unfold LMonoTy.subst; simp [hS_ne]
        simp only [h_eq, LMonoTy.freeVars, LMonoTys.subst_eq_substLogic] at h_nf
        exact h_nf
      suffices ∀ xs,
          (∀ m, m ∈ xs → ¬(id ∈ (LMonoTy.subst S m).freeVars) →
            LMonoTy.subst (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
              id (LMonoTy.subst S orig_lty)) m = LMonoTy.subst S m) →
          ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S xs)) →
          LMonoTys.substLogic (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
            id (LMonoTy.subst S orig_lty)) xs = LMonoTys.substLogic S xs by
        exact this args (fun m hm h_nfm => ih m hm h_nfm) h_nf'
      intro xs; induction xs with
      | nil => intros; simp [LMonoTys.substLogic, hS', hS_ne]
      | cons a rest ih_rest =>
        intro ih_xs h_nf_xs
        simp only [LMonoTys.substLogic, hS', hS_ne, Bool.false_eq_true, ↓reduceIte]
        have h_eq_cons : LMonoTys.substLogic S (a :: rest) =
            LMonoTy.subst S a :: LMonoTys.substLogic S rest := by
          simp [LMonoTys.substLogic, hS_ne]
        rw [h_eq_cons, LMonoTys.freeVars_of_cons] at h_nf_xs
        have h1 : ¬(id ∈ (LMonoTy.subst S a).freeVars) :=
          fun h => h_nf_xs (List.mem_append_left _ h)
        have h2 : ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S rest)) :=
          fun h => h_nf_xs (List.mem_append_right _ h)
        rw [ih_xs a (.head _) h1,
            ih_rest (fun m hm => ih_xs m (.tail _ hm)) h2]

/-- Bundled result for the three properties proved simultaneously about `unifyOne`:
    soundness (constraint is equalized), absorption (output absorbs input),
    and key inclusion (output keys come from input keys, constraint freeVars,
    or input value freeVars). -/
structure Constraint.UnifyOneProperties (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S) : Prop where
  sound : LMonoTy.subst relS.newS.subst c.1 = LMonoTy.subst relS.newS.subst c.2
  absorbs : Subst.absorbs relS.newS.subst S.subst
  keys_incl : ∀ k, k ∈ Maps.keys relS.newS.subst →
    k ∈ Maps.keys S.subst ∨ k ∈ Constraint.freeVars c ∨ k ∈ Subst.freeVars S.subst

/-- Bundled result for the three properties proved simultaneously about `unifyCore`. -/
structure Constraints.UnifyCoreProperties (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S) : Prop where
  sound : ∀ p, p ∈ cs → LMonoTy.subst relS.newS.subst p.1 = LMonoTy.subst relS.newS.subst p.2
  absorbs : Subst.absorbs relS.newS.subst S.subst
  keys_incl : ∀ k, k ∈ Maps.keys relS.newS.subst →
    k ∈ Maps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst

-- Combined soundness, absorption, and key-inclusion for `unifyOne`/`unifyCore`.
-- A single mutual induction on `Constraint.unifyOne.induct` proves all three
-- properties simultaneously, sharing the 17-case decomposition.
--
-- The theorem proves `motive1` (for `unifyOne`) directly; `motive2` (for
-- `unifyCore`) is proved as part of the same induction and is exposed
-- separately via `Constraints.unifyCore_sound`.
theorem Constraint.unifyOne_sound (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S)
    (h : Constraint.unifyOne c S = .ok relS) :
    Constraint.UnifyOneProperties c S relS := by
  suffices ∀ relS, Constraint.unifyOne c S = .ok relS →
      Constraint.UnifyOneProperties c S relS from this relS h
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS →
      Constraint.UnifyOneProperties c S relS)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS →
      Constraints.UnifyCoreProperties cs S relS)
  -- Case 1: t1 == t2
  · intro S t1 t2 h_eq _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h
      exact ⟨by grind, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨?_, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
      show LMonoTy.subst S.subst (.ftvar id) = LMonoTy.subst S.subst orig_lty
      have h_id_eq : LMonoTy.ftvar id = LMonoTy.subst S.subst orig_lty := eq_of_beq h_eq_lty
      rw [h_id_eq]; exact LMonoTy.subst_idempotent S.subst S.isWF orig_lty
  -- Case 3: ftvar id, orig_lty; occurs check — error
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 4: ftvar id, orig_lty; some sty — recursive
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]
          have ih := ih_rec relS' h_call
          -- Absorption (from IH)
          have h_abs := ih.absorbs
          -- Soundness: subst S' (ftvar id) = subst S' orig_lty
          have h_sound : LMonoTy.subst relS'.newS.subst (.ftvar id) =
              LMonoTy.subst relS'.newS.subst orig_lty := by
            have h_ftvar : LMonoTy.subst relS'.newS.subst (.ftvar id) =
                LMonoTy.subst relS'.newS.subst sty := by
              have := h_abs id sty h_some; simp only [this]
            have h_orig : LMonoTy.subst relS'.newS.subst (LMonoTy.subst S.subst orig_lty) =
                LMonoTy.subst relS'.newS.subst orig_lty :=
              LMonoTy.subst_absorbs relS'.newS.subst S.subst orig_lty h_abs
            rw [h_ftvar, ih.sound, h_orig]
          -- Key inclusion (from IH, lifting freeVars)
          have h_keys : ∀ k, k ∈ Maps.keys relS'.newS.subst →
              k ∈ Maps.keys S.subst ∨
              k ∈ Constraint.freeVars (LMonoTy.ftvar id, orig_lty) ∨
              k ∈ Subst.freeVars S.subst := by
            intro k hk
            rcases ih.keys_incl k hk with h1 | h2 | h3
            · left; exact h1
            · simp only [Constraint.freeVars, List.mem_append] at h2
              rcases h2 with h_sty | h_lty
              · right; right; exact Subst.freeVars_of_find_subset S.subst h_some h_sty
              · rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst orig_lty h_lty) with
                  h_orig | h_vals
                · right; left; simp [Constraint.freeVars]; right; exact h_orig
                · right; right; exact h_vals
            · right; right; exact h3
          exact ⟨h_sound, h_abs, h_keys⟩
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 5: ftvar id, orig_lty; none — insert+apply
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness
          exact Eq.trans
            (subst_ftvar_new_binding S.subst id (LMonoTy.subst S.subst orig_lty) h_none)
            (subst_orig_new_binding S.subst id (LMonoTy.subst S.subst orig_lty)
              orig_lty h_none rfl h_not_occurs).symm
        · -- Absorption
          exact absorbs_of_insert_apply_h' S id (LMonoTy.subst S.subst orig_lty) h_none
            (SubstWF.cons_of_subst_apply S id orig_lty _ rfl
              (SubstWF.single_subst id h_not_occurs) (SubstWF.apply_one_substituted_type S id orig_lty))
        · -- Key inclusion
          intro k hk
          have hk' := Maps.insert_keys_subset (ms := Subst.apply [(_,_)] S.subst) (key := _) (val := _) hk
          rw [Subst.keys_of_apply_eq] at hk'
          rcases List.mem_cons.mp hk' with rfl | h_old
          · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
          · left; exact h_old
  -- Case 6: orig_lty, ftvar id; ftvar id == lty
  · intro S orig_lty id h_neq _ _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨?_, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
      show LMonoTy.subst S.subst orig_lty = LMonoTy.subst S.subst (.ftvar id)
      have h_id_eq : LMonoTy.ftvar id = LMonoTy.subst S.subst orig_lty := eq_of_beq h_eq_lty
      rw [h_id_eq]; exact (LMonoTy.subst_idempotent S.subst S.isWF orig_lty).symm
  -- Case 7: orig_lty, ftvar id; occurs check — error
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 8: orig_lty, ftvar id; some sty — recursive (symmetric to case 4)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]
          have ih := ih_rec relS' h_call
          have h_abs := ih.absorbs
          -- Soundness: subst S' orig_lty = subst S' (ftvar id)
          have h_sound : LMonoTy.subst relS'.newS.subst orig_lty =
              LMonoTy.subst relS'.newS.subst (.ftvar id) := by
            have h_ftvar : LMonoTy.subst relS'.newS.subst (.ftvar id) =
                LMonoTy.subst relS'.newS.subst sty := by
              have := h_abs id sty h_some; simp only [this]
            have h_orig : LMonoTy.subst relS'.newS.subst (LMonoTy.subst S.subst orig_lty) =
                LMonoTy.subst relS'.newS.subst orig_lty :=
              LMonoTy.subst_absorbs relS'.newS.subst S.subst orig_lty h_abs
            rw [← h_orig, ← ih.sound, h_ftvar]
          -- Key inclusion (symmetric to case 4)
          have h_keys : ∀ k, k ∈ Maps.keys relS'.newS.subst →
              k ∈ Maps.keys S.subst ∨
              k ∈ Constraint.freeVars (orig_lty, LMonoTy.ftvar id) ∨
              k ∈ Subst.freeVars S.subst := by
            intro k hk
            rcases ih.keys_incl k hk with h1 | h2 | h3
            · left; exact h1
            · simp only [Constraint.freeVars, List.mem_append] at h2
              rcases h2 with h_sty | h_lty
              · right; right; exact Subst.freeVars_of_find_subset S.subst h_some h_sty
              · rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst orig_lty h_lty) with
                  h_orig | h_vals
                · right; left; simp [Constraint.freeVars]; left; exact h_orig
                · right; right; exact h_vals
            · right; right; exact h3
          exact ⟨h_sound, h_abs, h_keys⟩
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 9: orig_lty, ftvar id; none — insert+apply (symmetric to case 5)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness
          exact Eq.symm (Eq.trans
            (subst_ftvar_new_binding S.subst id (LMonoTy.subst S.subst orig_lty) h_none)
            (subst_orig_new_binding S.subst id (LMonoTy.subst S.subst orig_lty)
              orig_lty h_none rfl h_not_occurs).symm)
        · -- Absorption
          exact absorbs_of_insert_apply_h' S id (LMonoTy.subst S.subst orig_lty) h_none
            (SubstWF.cons_of_subst_apply S id orig_lty _ rfl
              (SubstWF.single_subst id h_not_occurs) (SubstWF.apply_one_substituted_type S id orig_lty))
        · -- Key inclusion
          intro k hk
          have hk' := Maps.insert_keys_subset (ms := Subst.apply [(_,_)] S.subst) (key := _) (val := _) hk
          rw [Subst.keys_of_apply_eq] at hk'
          rcases List.mem_cons.mp hk' with rfl | h_old
          · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
          · left; exact h_old
  -- Case 10: bitvec n1 == n2 contradiction
  · intro S n1 n2 h_neq h_eq_n relS h; grind
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 12: tcons match — recursive unifyCore
  · intro S name1 args1 name2 args2 h_neq h_match _nc ih_core relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]
        have ih := ih_core relS' h_call
        refine ⟨?_, ih.absorbs, ?_⟩
        · -- Soundness: subst S' (tcons name1 args1) = subst S' (tcons name2 args2)
          have h_name_eq : name1 = name2 := by
            have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).1; exact eq_of_beq this
          have h_len_eq : args1.length = args2.length := by
            have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).2; exact of_decide_eq_true this
          subst h_name_eq
          have ih_pw := ih.sound
          have h_args_eq : ∀ (l1 l2 : LMonoTys), l1.length = l2.length →
              (∀ p, p ∈ l1.zip l2 →
                LMonoTy.subst relS'.newS.subst p.1 = LMonoTy.subst relS'.newS.subst p.2) →
              LMonoTys.subst relS'.newS.subst l1 = LMonoTys.subst relS'.newS.subst l2 := by
            intro l1 l2 h_len h_pw
            rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
            by_cases hS : Subst.hasEmptyScopes relS'.newS.subst
            · have h_id : ∀ l, LMonoTys.substLogic relS'.newS.subst l = l := by
                intro l; induction l with
                | nil => simp [LMonoTys.substLogic, hS]
                | cons _ _ _ => simp [LMonoTys.substLogic, hS]
              rw [h_id, h_id]
              induction l1 generalizing l2 with
              | nil => cases l2 with | nil => rfl | cons _ _ => simp at h_len
              | cons a rest ih_l =>
                cases l2 with
                | nil => simp at h_len
                | cons b rest2 =>
                  simp at h_len
                  have h_ab := h_pw (a, b) List.mem_cons_self
                  simp [LMonoTy.subst_emptyS hS] at h_ab
                  rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
            · have hS_ne : Subst.hasEmptyScopes relS'.newS.subst = false := by
                revert hS; cases Subst.hasEmptyScopes relS'.newS.subst <;> simp
              induction l1 generalizing l2 with
              | nil => cases l2 with | nil => simp [LMonoTys.substLogic, hS_ne] | cons _ _ => simp at h_len
              | cons a rest ih_l =>
                cases l2 with
                | nil => simp at h_len
                | cons b rest2 =>
                  simp at h_len
                  simp only [LMonoTys.substLogic, hS_ne, Bool.false_eq_true, ↓reduceIte]
                  have h_ab : LMonoTy.subst relS'.newS.subst a = LMonoTy.subst relS'.newS.subst b :=
                    h_pw (a, b) List.mem_cons_self
                  rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
          have h_list := h_args_eq args1 args2 h_len_eq ih_pw
          by_cases hS_final : Subst.hasEmptyScopes relS'.newS.subst
          · simp [LMonoTy.subst_emptyS hS_final]
            simp [LMonoTys.subst, hS_final] at h_list; rw [h_list]
          · have hS_ne : Subst.hasEmptyScopes relS'.newS.subst = false := by
              revert hS_final; cases Subst.hasEmptyScopes relS'.newS.subst <;> simp
            simp [LMonoTy.subst, hS_ne]; exact h_list
        · -- Key inclusion
          intro k hk
          rcases ih.keys_incl k hk with h1 | h2 | h3
          · left; exact h1
          · right; left; simp only [Constraint.freeVars, LMonoTy.freeVars, List.mem_append]
            exact List.mem_append.mp (Constraints.freeVars_of_zip_subset h2)
          · right; right; exact h3
  -- Case 13: tcons name/length mismatch — error
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 16: unifyCore []
  · intro S relS h
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact ⟨fun p hp => by grind, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
  -- Case 17: unifyCore c :: rest
  · intro S c c_rest ih1 ih2 relS h
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h; subst h
        have ih_one := ih1 relS_one h_one
        have ih_rest := ih2 relS_one relS_rest h_rest
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness: all pairs in c :: c_rest are equalized
          intro p hp
          cases List.mem_cons.mp hp with
          | inl h_pc =>
            subst h_pc
            have h_sound_one := ih_one.sound
            have h_abs := ih_rest.absorbs
            calc LMonoTy.subst relS_rest.newS.subst p.1
                = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.1) :=
                  (LMonoTy.subst_absorbs _ _ _ h_abs).symm
              _ = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.2) := by
                  rw [h_sound_one]
              _ = LMonoTy.subst relS_rest.newS.subst p.2 :=
                  LMonoTy.subst_absorbs _ _ _ h_abs
          | inr h_rest_mem =>
            exact ih_rest.sound p h_rest_mem
        · -- Absorption: transitive
          exact Subst.absorbs_trans S.subst relS_one.newS.subst relS_rest.newS.subst
            ih_one.absorbs ih_rest.absorbs
        · -- Key inclusion
          intro k hk
          rcases ih_rest.keys_incl k hk with hk1 | hk2 | hk3
          · rcases ih_one.keys_incl k hk1 with h1a | h1b | h1c
            · left; exact h1a
            · right; left; simp [Constraints.freeVars]; left; exact h1b
            · right; right; exact h1c
          · right; left; simp [Constraints.freeVars]; right; exact hk2
          · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
            · right; left; simp [Constraints.freeVars]; left
              simp [Constraints.freeVars] at h_c; exact h_c
            · right; right; exact h_s

/-- Combined soundness, absorption, and key-inclusion for `unifyCore`.
    Proved by simple list induction, delegating to `Constraint.unifyOne_sound`
    for each head constraint. -/
theorem Constraints.unifyCore_sound (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S)
    (h : Constraints.unifyCore cs S = .ok relS) :
    Constraints.UnifyCoreProperties cs S relS := by
  induction cs generalizing S with
  | nil =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact ⟨fun p hp => by grind, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
  | cons c rest ih =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h; subst h
        have ih_one := Constraint.unifyOne_sound c S relS_one h_one
        have ih_rest := ih relS_one.newS relS_rest h_rest
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness
          intro p hp
          cases List.mem_cons.mp hp with
          | inl h_pc =>
            subst h_pc
            have h_abs := ih_rest.absorbs
            calc LMonoTy.subst relS_rest.newS.subst p.1
                = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.1) :=
                  (LMonoTy.subst_absorbs _ _ _ h_abs).symm
              _ = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.2) := by
                  rw [ih_one.sound]
              _ = LMonoTy.subst relS_rest.newS.subst p.2 :=
                  LMonoTy.subst_absorbs _ _ _ h_abs
          | inr h_rest_mem =>
            exact ih_rest.sound p h_rest_mem
        · -- Absorption
          exact Subst.absorbs_trans S.subst relS_one.newS.subst relS_rest.newS.subst
            ih_one.absorbs ih_rest.absorbs
        · -- Key inclusion
          intro k hk
          rcases ih_rest.keys_incl k hk with hk1 | hk2 | hk3
          · rcases ih_one.keys_incl k hk1 with h1a | h1b | h1c
            · left; exact h1a
            · right; left; simp [Constraints.freeVars]; left; exact h1b
            · right; right; exact h1c
          · right; left; simp [Constraints.freeVars]; right; exact hk2
          · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
            · right; left; simp [Constraints.freeVars]; left
              simp [Constraints.freeVars] at h_c; exact h_c
            · right; right; exact h_s

/-- Unification produces a substitution that absorbs the input substitution. -/
theorem Constraints.unify_absorbs (constraints : Constraints) (S_old S_new : SubstInfo)
    (h : Constraints.unify constraints S_old = .ok S_new) :
    Subst.absorbs S_new.subst S_old.subst := by
  simp only [Constraints.unify, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h; subst h
    exact (Constraints.unifyCore_sound constraints S_old relS h_core).absorbs

/-- Unification produces a substitution that makes every constraint pair equal. -/
theorem Constraints.unify_sound (constraints : Constraints) (S_old S_new : SubstInfo)
    (h : Constraints.unify constraints S_old = .ok S_new) :
    ∀ p, p ∈ constraints →
      LMonoTy.subst S_new.subst p.1 = LMonoTy.subst S_new.subst p.2 := by
  simp only [Constraints.unify, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h; subst h
    exact (Constraints.unifyCore_sound constraints S_old relS h_core).sound

end -- public section
end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyUnify
public import Strata.Util.ExceptProps
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Util.List
import all Strata.Util.HMaps
import all Strata.Util.HMap
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
## Theorems for Type Substitution and Unification

Properties of substitution, and the soundness, most-general-unifier, and matching
completeness of `Constraints.unify`. Key theorems: `Constraints.unify_sound`,
`Constraints.unify_mgu`, and `Constraints_unify_matching_complete`.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open Strata.Util (HMap HMaps)

public section

theorem SubstWF.not_mem_freeVars_of_find (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : HMaps.find? S a = some t) (h_wf : SubstWF S) :
    a ∉ LMonoTy.freeVars t := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_wf
  have h_key := HMaps.find?_mem_keys S h_find
  have h_fv_subset := Subst.freeVars_of_find_subset S h_find
  exact fun hmem => h_wf a h_key (h_fv_subset hmem)

/-- Absorption for type lists: the single substitution is absorbed element-wise. -/
theorem LMonoTys.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mtys : LMonoTys)
    (ih : ∀ m, m ∈ mtys → LMonoTy.subst S (LMonoTy.subst (Subst.singleton a t) m) = LMonoTy.subst S m) :
    LMonoTys.subst S (LMonoTys.subst (Subst.singleton a t) mtys) = LMonoTys.subst S mtys := by
  rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_map]
  exact List.map_congr_left (fun a ha => ih a ha)

/--
#### Absorption: relating substitutions produced by successive resolveAux calls

Absorption: `subst S (subst [(a,t)] mty) = subst S mty` when `HMaps.find? S a = some t`
and `SubstWF S`. The single-variable substitution `[(a,t)]` is "absorbed" by `S`
because `S` already maps `a` to `t`.
-/
theorem LMonoTy.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mty : LMonoTy) (h_find : HMaps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S (LMonoTy.subst (Subst.singleton a t) mty) = LMonoTy.subst S mty := by
  induction mty with
  | ftvar x =>
    by_cases h_eq : a = x
    · -- x = a: inner subst gives t, then subst S t = t = subst S (ftvar a)
      subst h_eq
      have h_inner : LMonoTy.subst (Subst.singleton a t) (.ftvar a) = t := by
        rw [LMonoTy.subst_unfold]; simp [Subst.find?_singleton_self]
      rw [h_inner]
      have h_a : LMonoTy.subst S (.ftvar a) = t := by
        rw [LMonoTy.subst_unfold]; simp [h_find]
      rw [h_a]
      exact LMonoTy.subst_idempotent_value S a t h_find h_wf
    · -- x ≠ a: inner subst is identity
      have h_inner : LMonoTy.subst (Subst.singleton a t) (.ftvar x) = .ftvar x := by
        have hfx : HMaps.find? (Subst.singleton a t) x = none := by
          simp only [Subst.singleton, HMaps.find?_single_scope,
            HMap.find?_single_ne a x t (by simp [bne, Ne.symm h_eq])]
        simp only [LMonoTy.subst_unfold, hfx]
      rw [h_inner]
  | bitvec n =>
    rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    exact LMonoTys.subst_absorbs_single S a t args ih

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
  ∀ a t, HMaps.find? S_inner a = some t →
    LMonoTy.subst S_outer t = LMonoTy.subst S_outer (.ftvar a)

/--
Absorption implies substitution composition collapses:
`subst S_outer (subst S_inner mty) = subst S_outer mty`.
-/
theorem LMonoTy.subst_absorbs (S_outer S_inner : Subst) (mty : LMonoTy)
    (h : Subst.absorbs S_outer S_inner) :
    LMonoTy.subst S_outer (LMonoTy.subst S_inner mty) = LMonoTy.subst S_outer mty := by
  induction mty with
  | ftvar x =>
    cases h_find : HMaps.find? S_inner x with
    | none =>
      have h_id : LMonoTy.subst S_inner (.ftvar x) = .ftvar x := by
        rw [LMonoTy.subst_unfold]; simp [h_find]
      rw [h_id]
    | some t =>
      have h_t : LMonoTy.subst S_inner (.ftvar x) = t := by
        rw [LMonoTy.subst_unfold]; simp [h_find]
      rw [h_t]; exact h x t h_find
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map,
        List.map_map]
    exact List.map_congr_left (fun a ha => ih a ha)

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
  have h1 : LMonoTy.subst S (.ftvar a) = t := by
    rw [LMonoTy.subst_unfold]; simp [h_find]
  rw [h1]
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
Composition lemma: applying a singleton substitution `[single v t]` followed by
`[ys]` equals applying the merged substitution `[ys.insert v t]`, provided
`subst [ys] t = t` (i.e., `t` is stable under `ys`).

This is a key lemma for proving that sequential `tinst` applications
(each substituting one bound variable) produce the same result as a
single parallel substitution with all bindings.
-/

theorem LMonoTy.subst_cons_single
    (v : TyIdentifier) (t : LMonoTy) (ys : SubstOne) (mty : LMonoTy)
    (h_t : LMonoTy.subst [ys] t = t) :
    LMonoTy.subst [ys] (LMonoTy.subst (Subst.singleton v t) mty) =
    LMonoTy.subst [ys.insert v t] mty := by
  induction mty with
  | ftvar x =>
    by_cases h_eq : v = x
    · subst h_eq
      have h_inner : LMonoTy.subst (Subst.singleton v t) (.ftvar v) = t := by
        simp only [LMonoTy.subst_unfold, Subst.find?_singleton_self]
      rw [h_inner, h_t]
      have h_rhs : HMaps.find? [ys.insert v t] v = some t := by
        rw [HMaps.find?_single_scope, HMap.find?_insert_self]
      simp only [LMonoTy.subst_unfold, h_rhs]
    · have h_inner : LMonoTy.subst (Subst.singleton v t) (.ftvar x) = .ftvar x := by
        have hfx : HMaps.find? (Subst.singleton v t) x = none := by
          simp only [Subst.singleton, HMaps.find?_single_scope,
            HMap.find?_single_ne v x t (by simp [bne, Ne.symm h_eq])]
        simp only [LMonoTy.subst_unfold, hfx]
      rw [h_inner]
      have h_rhs : HMaps.find? [ys.insert v t] x = HMaps.find? [ys] x := by
        rw [HMaps.find?_single_scope, HMaps.find?_single_scope,
          HMap.find?_insert_ne ys v x t (by simp [bne, Ne.symm h_eq])]
      simp only [LMonoTy.subst_unfold, h_rhs]
  | bitvec n =>
    simp only [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_map]
    exact List.map_congr_left (fun a ha => ih a ha)

-- Helper: insert+apply produces an absorbing substitution.
private theorem absorbs_of_insert_apply_h' (S : SubstInfo) (id : TyIdentifier) (lty : LMonoTy)
    (h_none : HMaps.find? S.subst id = none)
    (h_wf : SubstWF ((Subst.apply (HMap.single id lty) S.subst).insert id lty)) :
    Subst.absorbs ((Subst.apply (HMap.single id lty) S.subst).insert id lty) S.subst := by
  intro a t h_find
  have h_a_ne_id : a ≠ id := by
    intro h_eq; subst h_eq; rw [h_find] at h_none; simp at h_none
  let S_new := (Subst.apply (HMap.single id lty) S.subst).insert id lty
  have h_apply_a : HMaps.find? (Subst.apply (HMap.single id lty) S.subst) a
      = some (LMonoTy.subst [HMap.single id lty] t) := by
    rw [Subst.find?_apply, h_find]; rfl
  have h_find_new : HMaps.find? S_new a = some (LMonoTy.subst (Subst.singleton id lty) t) := by
    show HMaps.find? (HMaps.insert _ id lty) a = _
    rw [HMaps.find?_insert_ne _ a id lty h_a_ne_id]
    exact h_apply_a
  have h_find_id : HMaps.find? S_new id = some lty := HMaps.find?_insert_self _ id lty
  have h_subst_ftvar : LMonoTy.subst S_new (.ftvar a) = LMonoTy.subst (Subst.singleton id lty) t := by
    rw [LMonoTy.subst_unfold]; simp only [h_find_new]
  have h_idem := LMonoTy.subst_idempotent_value S_new a _ h_find_new h_wf
  have h_abs := LMonoTy.subst_absorbs_single S_new id lty t h_find_id h_wf
  rw [h_subst_ftvar, ← h_abs, h_idem]

/-- After inserting `(id, lty)` into the applied substitution, `subst _ (ftvar id) = lty`. -/
private theorem subst_ftvar_new_binding
    (S : Subst) (id : TyIdentifier) (lty : LMonoTy)
    (_h_none : HMaps.find? S id = none) :
    LMonoTy.subst (HMaps.insert (Subst.apply (HMap.single id lty) S) id lty) (LMonoTy.ftvar id) = lty := by
  have h_find := HMaps.find?_insert_self (Subst.apply (HMap.single id lty) S) id lty
  rw [LMonoTy.subst_unfold]; simp only [h_find]

/-- When `S.find? id = none`, the new substitution absorbs `S` and maps `orig_lty` to `lty`. -/
private theorem subst_orig_new_binding
    (S : Subst) (id : TyIdentifier) (lty orig_lty : LMonoTy)
    (h_none : HMaps.find? S id = none)
    (h_lty : lty = LMonoTy.subst S orig_lty)
    (h_occurs : ¬(id ∈ lty.freeVars)) :
    LMonoTy.subst (HMaps.insert (Subst.apply (HMap.single id lty) S) id lty) orig_lty = lty := by
  subst h_lty
  have h_find_ne : ∀ x, x ≠ id →
      HMaps.find? (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S)
        id (LMonoTy.subst S orig_lty)) x =
      (HMaps.find? S x).map (LMonoTy.subst (Subst.singleton id (LMonoTy.subst S orig_lty))) := fun x hx =>
    (HMaps.find?_insert_ne _ x id (LMonoTy.subst S orig_lty) hx).trans (Subst.find?_apply _ _ _)
  have h_single_noop : ∀ t : LMonoTy, ¬(id ∈ t.freeVars) →
      LMonoTy.subst (Subst.singleton id (LMonoTy.subst S orig_lty)) t = t := fun t ht =>
    LMonoTy.subst_no_relevant_keys _ _ (fun x hx => by
      simp only [Subst.singleton, HMaps.keys, HMap.mem_keys_single_iff, List.append_nil]
      intro heq; subst heq; exact ht hx)
  suffices ∀ mty, ¬(id ∈ (LMonoTy.subst S mty).freeVars) →
      LMonoTy.subst (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S)
        id (LMonoTy.subst S orig_lty)) mty = LMonoTy.subst S mty from
    this orig_lty h_occurs
  intro mty h_nf
  induction mty with
  | ftvar x =>
    by_cases h_id : x = id
    · subst h_id; exfalso; apply h_nf
      rw [LMonoTy.subst_unfold]; simp only [h_none, LMonoTy.freeVars, List.mem_singleton]
    · cases h_fx : HMaps.find? S x with
      | none =>
        have h_lhs : HMaps.find? (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S)
            id (LMonoTy.subst S orig_lty)) x = none := by
          rw [h_find_ne x h_id, h_fx]; rfl
        have e_lhs : LMonoTy.subst (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S)
            id (LMonoTy.subst S orig_lty)) (.ftvar x) = .ftvar x := by
          rw [LMonoTy.subst_unfold]; simp only [h_lhs]
        have e_rhs : LMonoTy.subst S (.ftvar x) = .ftvar x := by
          rw [LMonoTy.subst_unfold]; simp only [h_fx]
        rw [e_lhs, e_rhs]
      | some t =>
        have h_lhs : HMaps.find? (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S)
            id (LMonoTy.subst S orig_lty)) x
            = some (LMonoTy.subst (Subst.singleton id (LMonoTy.subst S orig_lty)) t) := by
          rw [h_find_ne x h_id, h_fx]; rfl
        have e_lhs : LMonoTy.subst (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S)
            id (LMonoTy.subst S orig_lty)) (.ftvar x)
            = LMonoTy.subst (Subst.singleton id (LMonoTy.subst S orig_lty)) t := by
          rw [LMonoTy.subst_unfold]; simp only [h_lhs]
        have e_rhs : LMonoTy.subst S (.ftvar x) = t := by
          rw [LMonoTy.subst_unfold]; simp only [h_fx]
        rw [e_lhs, e_rhs]
        exact h_single_noop t (by rwa [e_rhs] at h_nf)
  | bitvec n => simp only [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map]
    have h_nf' : ∀ m, m ∈ args → ¬(id ∈ (LMonoTy.subst S m).freeVars) := by
      intro m hm h_in
      apply h_nf
      rw [LMonoTy.subst_tcons, LMonoTy.freeVars, LMonoTys.subst_eq_map]
      exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem hm) h_in
    exact List.map_congr_left (fun a ha => ih a ha (h_nf' a ha))

/-- Bundled result for the three properties proved simultaneously about `unifyOne`:
    soundness (constraint is equalized), absorption (output absorbs input),
    and key inclusion (output keys come from input keys, constraint freeVars,
    or input value freeVars). -/
structure Constraint.UnifyOneProperties (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S) : Prop where
  sound : LMonoTy.subst relS.newS.subst c.1 = LMonoTy.subst relS.newS.subst c.2
  absorbs : Subst.absorbs relS.newS.subst S.subst
  keys_incl : ∀ k, k ∈ HMaps.keys relS.newS.subst →
    k ∈ HMaps.keys S.subst ∨ k ∈ Constraint.freeVars c ∨ k ∈ Subst.freeVars S.subst

/-- Bundled result for the three properties proved simultaneously about `unifyCore`. -/
structure Constraints.UnifyCoreProperties (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S) : Prop where
  sound : ∀ p, p ∈ cs → LMonoTy.subst relS.newS.subst p.1 = LMonoTy.subst relS.newS.subst p.2
  absorbs : Subst.absorbs relS.newS.subst S.subst
  keys_incl : ∀ k, k ∈ HMaps.keys relS.newS.subst →
    k ∈ HMaps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst

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
          have h_keys : ∀ k, k ∈ HMaps.keys relS'.newS.subst →
              k ∈ HMaps.keys S.subst ∨
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
            (SubstWF.cons_of_subst_apply S.subst S.isWF id orig_lty _ rfl h_not_occurs)
        · -- Key inclusion
          intro k hk
          have hk' := HMaps.insert_keys_subset (Subst.apply (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst) id (LMonoTy.subst S.subst orig_lty) k hk
          rcases List.mem_cons.mp hk' with rfl | h_old
          · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
          · left; exact (Subst.mem_keys_apply_iff _ S.subst k).mp h_old
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
          have h_keys : ∀ k, k ∈ HMaps.keys relS'.newS.subst →
              k ∈ HMaps.keys S.subst ∨
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
            (SubstWF.cons_of_subst_apply S.subst S.isWF id orig_lty _ rfl h_not_occurs)
        · -- Key inclusion
          intro k hk
          have hk' := HMaps.insert_keys_subset (Subst.apply (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst) id (LMonoTy.subst S.subst orig_lty) k hk
          rcases List.mem_cons.mp hk' with rfl | h_old
          · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
          · left; exact (Subst.mem_keys_apply_iff _ S.subst k).mp h_old
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
            rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map]
            induction l1 generalizing l2 with
            | nil => cases l2 with | nil => rfl | cons _ _ => simp at h_len
            | cons a rest ih_l =>
              cases l2 with
              | nil => simp at h_len
              | cons b rest2 =>
                simp at h_len
                simp only [List.map_cons]
                have h_ab : LMonoTy.subst relS'.newS.subst a = LMonoTy.subst relS'.newS.subst b :=
                  h_pw (a, b) List.mem_cons_self
                rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
          have h_list := h_args_eq args1 args2 h_len_eq ih_pw
          rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons]; exact congrArg _ h_list
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

/-! ## Most-general-unifier (MGU) helpers

An arbitrary unifier `R` "factors through" a substitution `S` exactly when
`Subst.absorbs R S` holds (`LMonoTy.subst_absorbs`: applying `S` first does not
change `R`'s result). The MGU theorems below show every unifier of the input
constraints that factors through the input substitution also factors through
the output substitution — i.e. the output is most general. -/

/-- A substitution `R` absorbs the singleton `[single id lty]` as soon as it
    identifies `id` with `lty`. -/
private theorem absorbs_single_of_subst_eq_h' (R : Subst) (id : TyIdentifier) (lty : LMonoTy)
    (h : LMonoTy.subst R lty = LMonoTy.subst R (.ftvar id)) :
    Subst.absorbs R (Subst.singleton id lty) := by
  intro a t h_find
  have h_at : id = a ∧ t = lty := by
    by_cases h_eq : a = id
    · subst h_eq
      rw [Subst.find?_singleton_self] at h_find
      simp only [Option.some.injEq] at h_find
      exact ⟨rfl, h_find.symm⟩
    · rw [Subst.singleton, HMaps.find?_single_scope,
        HMap.find?_single_ne id a lty (by simp [bne, h_eq])] at h_find
      simp at h_find
  obtain ⟨h1, h2⟩ := h_at
  subst h1; subst h2
  exact h

/-- **MGU core step**: if `R` absorbs `S` and identifies `id` with `lty`, then
    `R` absorbs the extension `(Subst.apply [single id lty] S).insert id lty` that
    `unifyOne` builds in its binding case. -/
private theorem absorbs_insert_apply_of_h' (R : Subst) (S : Subst)
    (id : TyIdentifier) (lty : LMonoTy)
    (hRS : Subst.absorbs R S)
    (h_id : LMonoTy.subst R lty = LMonoTy.subst R (.ftvar id)) :
    Subst.absorbs R ((Subst.apply (HMap.single id lty) S).insert id lty) := by
  have h_single := absorbs_single_of_subst_eq_h' R id lty h_id
  intro a t h_find
  by_cases h_a : a = id
  · subst h_a
    rw [HMaps.find?_insert_self] at h_find
    simp only [Option.some.injEq] at h_find; subst h_find
    exact h_id
  · rw [HMaps.find?_insert_ne _ a id lty h_a, Subst.find?_apply] at h_find
    obtain ⟨t₀, h_find₀, h_eq⟩ := Option.map_eq_some_iff.mp h_find
    subst h_eq
    calc LMonoTy.subst R (LMonoTy.subst (Subst.singleton id lty) t₀)
        = LMonoTy.subst R t₀ := LMonoTy.subst_absorbs R (Subst.singleton id lty) t₀ h_single
      _ = LMonoTy.subst R (.ftvar a) := hRS a t₀ h_find₀

/-- Pointwise unification of `tcons` arguments: if `R` unifies two equal-length
    `tcons` applications, it unifies every zipped argument pair. -/
private theorem subst_tcons_zip_h' (R : Subst) (name : String) (args1 args2 : LMonoTys)
    (h_len : args1.length = args2.length)
    (h : LMonoTy.subst R (.tcons name args1) = LMonoTy.subst R (.tcons name args2)) :
    ∀ p ∈ List.zip args1 args2, LMonoTy.subst R p.1 = LMonoTy.subst R p.2 := by
  rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons] at h
  simp only [LMonoTy.tcons.injEq, true_and] at h
  rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map] at h
  induction args1 generalizing args2 with
  | nil => intro p hp; simp at hp
  | cons a1 r1 ih =>
    match args2 with
    | [] => simp at h_len
    | a2 :: r2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      intro p hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with h_p | h_p
      · subst h_p; exact h.1
      · exact ih r2 (by simpa using h_len) h.2 p h_p

/-- **MGU (most general unifier), `unifyOne` level.** Any substitution `R`
    that unifies the constraint and factors through the input substitution
    (`Subst.absorbs R S.subst`) also factors through the output substitution.
    With `Constraint.unifyOne_sound` this says the computed substitution is a
    most general unifier: every solution is an instance of it. -/
theorem Constraint.unifyOne_mgu (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S)
    (h : Constraint.unifyOne c S = .ok relS)
    (R : Subst)
    (hR : LMonoTy.subst R c.1 = LMonoTy.subst R c.2)
    (hRS : Subst.absorbs R S.subst) :
    Subst.absorbs R relS.newS.subst := by
  suffices ∀ relS, Constraint.unifyOne c S = .ok relS → ∀ R,
      LMonoTy.subst R c.1 = LMonoTy.subst R c.2 → Subst.absorbs R S.subst →
      Subst.absorbs R relS.newS.subst from this relS h R hR hRS
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS → ∀ R,
      LMonoTy.subst R c.1 = LMonoTy.subst R c.2 → Subst.absorbs R S.subst →
      Subst.absorbs R relS.newS.subst)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS → ∀ R,
      (∀ p ∈ cs, LMonoTy.subst R p.1 = LMonoTy.subst R p.2) → Subst.absorbs R S.subst →
      Subst.absorbs R relS.newS.subst)
  -- Case 1: t1 == t2 — substitution unchanged
  · intro S t1 t2 h_eq _ relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h; exact hRS
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id, orig_lty; ftvar id == lty — substitution unchanged
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; exact hRS
  -- Case 3: occurs check — error
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 4: ftvar id with existing binding sty — recursive
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h R hR hRS
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
          -- R unifies (sty, subst S orig_lty): chain through the id binding.
          have h_unif : LMonoTy.subst R sty
              = LMonoTy.subst R (LMonoTy.subst S.subst orig_lty) := by
            calc LMonoTy.subst R sty
                = LMonoTy.subst R (.ftvar id) := hRS id sty h_some
              _ = LMonoTy.subst R orig_lty := hR
              _ = LMonoTy.subst R (LMonoTy.subst S.subst orig_lty) :=
                  (LMonoTy.subst_absorbs R S.subst orig_lty hRS).symm
          exact ih_rec relS' h_call R h_unif hRS
      · rename_i h_none'
        rw [h_some] at h_none'; simp at h_none'
  -- Case 5: ftvar id unbound — insert+apply extension
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        have h_id : LMonoTy.subst R (LMonoTy.subst S.subst orig_lty)
            = LMonoTy.subst R (.ftvar id) := by
          rw [LMonoTy.subst_absorbs R S.subst orig_lty hRS]; exact hR.symm
        exact absorbs_insert_apply_of_h' R S.subst id (LMonoTy.subst S.subst orig_lty) hRS h_id
  -- Case 6: orig_lty, ftvar id; ftvar id == lty — substitution unchanged
  · intro S orig_lty id h_neq _ _lty _ _ h_eq_lty relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; exact hRS
  -- Case 7: occurs check (symmetric) — error
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_occurs relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 8: existing binding sty (symmetric to case 4)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h R hR hRS
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
          have h_unif : LMonoTy.subst R sty
              = LMonoTy.subst R (LMonoTy.subst S.subst orig_lty) := by
            calc LMonoTy.subst R sty
                = LMonoTy.subst R (.ftvar id) := hRS id sty h_some
              _ = LMonoTy.subst R orig_lty := hR.symm
              _ = LMonoTy.subst R (LMonoTy.subst S.subst orig_lty) :=
                  (LMonoTy.subst_absorbs R S.subst orig_lty hRS).symm
          exact ih_rec relS' h_call R h_unif hRS
      · rename_i h_none'
        rw [h_some] at h_none'; simp at h_none'
  -- Case 9: unbound (symmetric to case 5)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        have h_id : LMonoTy.subst R (LMonoTy.subst S.subst orig_lty)
            = LMonoTy.subst R (.ftvar id) := by
          rw [LMonoTy.subst_absorbs R S.subst orig_lty hRS]; exact hR
        exact absorbs_insert_apply_of_h' R S.subst id (LMonoTy.subst S.subst orig_lty) hRS h_id
  -- Case 10: bitvec n1 == n2 — contradiction with t1 ≠ t2
  · intro S n1 n2 h_neq h_eq_n relS h R hR hRS; grind
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 12: tcons match — recursive unifyCore on zipped args
  · intro S name1 args1 name2 args2 h_neq h_match _nc ih_core relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]
        have h_name_eq : name1 = name2 := by
          have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).1; exact eq_of_beq this
        have h_len_eq : args1.length = args2.length := by
          have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).2; exact of_decide_eq_true this
        subst h_name_eq
        exact ih_core relS' h_call R (subst_tcons_zip_h' R name1 args1 args2 h_len_eq hR) hRS
  -- Case 13: tcons mismatch — error
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h R hR hRS
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 16: unifyCore [] — substitution unchanged
  · intro S relS h R hR hRS
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h; exact hRS
  -- Case 17: unifyCore c :: rest — compose
  · intro S c c_rest ih1 ih2 relS h R hR hRS
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
        have h_abs_one := ih1 relS_one h_one R (hR c (List.mem_cons_self ..)) hRS
        exact ih2 relS_one relS_rest h_rest R
          (fun p hp => hR p (List.mem_cons_of_mem c hp)) h_abs_one

/-- MGU at the `unifyCore` level: list induction delegating to
    `Constraint.unifyOne_mgu` per head constraint (mirrors
    `Constraints.unifyCore_sound`). -/
theorem Constraints.unifyCore_mgu (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S)
    (h : Constraints.unifyCore cs S = .ok relS) :
    ∀ R, (∀ p ∈ cs, LMonoTy.subst R p.1 = LMonoTy.subst R p.2) →
      Subst.absorbs R S.subst → Subst.absorbs R relS.newS.subst := by
  induction cs generalizing S with
  | nil =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact fun R _ hRS => hRS
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
        intro R hR hRS
        have h_abs_one := Constraint.unifyOne_mgu c S relS_one h_one R
          (hR c (List.mem_cons_self ..)) hRS
        exact ih relS_one.newS relS_rest h_rest R
          (fun p hp => hR p (List.mem_cons_of_mem c hp)) h_abs_one

/-- **MGU, `unify` level.** Any substitution `R` that unifies all constraints
    and factors through the input substitution also factors through the output
    substitution: with `Constraints.unify_sound`, the substitution `unify`
    computes is a most general unifier — every solution `R` is an instance of
    it (`LMonoTy.subst R (LMonoTy.subst S_new.subst ty) = LMonoTy.subst R ty`
    for all `ty`, by `LMonoTy.subst_absorbs`). -/
theorem Constraints.unify_mgu (constraints : Constraints) (S_old S_new : SubstInfo)
    (h : Constraints.unify constraints S_old = .ok S_new)
    (R : Subst)
    (hR : ∀ p ∈ constraints, LMonoTy.subst R p.1 = LMonoTy.subst R p.2)
    (hRS : Subst.absorbs R S_old.subst) :
    Subst.absorbs R S_new.subst := by
  simp only [Constraints.unify, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h; subst h
    exact Constraints.unifyCore_mgu constraints S_old relS h_core R hR hRS

/-! ## Completeness of unification for matching problems

Unlike the soundness/MGU results above, these lemmas show unification *succeeds* when a
matcher exists. `Constraint.unifyOne_matching_complete` carries the argument by functional
induction (`Constraint.unifyOne.induct`), tracking that the produced substitution only
binds pattern-side variables; `Constraints_unify_matching_complete` is the specialization
to a single constraint from the empty substitution. -/

/-- Occurs-check soundness: if `id` occurs in `t` and `t` is not `ftvar id`, then
    `subst M (ftvar id)` is a strict subterm of `subst M t`, so they differ. -/
private theorem subst_ftvar_ne_of_occurs (M : Subst) (id : TyIdentifier) (t : LMonoTy)
    (h_occurs : id ∈ t.freeVars) (h_ne : t ≠ .ftvar id) :
    LMonoTy.subst M (.ftvar id) ≠ LMonoTy.subst M t := by
  have hle : ∀ (u : LMonoTy), id ∈ u.freeVars →
      LMonoTy.size (LMonoTy.subst M (.ftvar id)) ≤ LMonoTy.size (LMonoTy.subst M u) := by
    intro u hu
    induction u with
    | ftvar x => simp only [LMonoTy.freeVars, List.mem_singleton] at hu; subst hu; exact Nat.le_refl _
    | bitvec n => simp [LMonoTy.freeVars] at hu
    | tcons name args ih =>
      simp only [LMonoTy.freeVars] at hu
      obtain ⟨a, ha, hva⟩ := LMonoTys.freeVars_exists hu
      rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
      calc LMonoTy.size (LMonoTy.subst M (.ftvar id))
          ≤ LMonoTy.size (LMonoTy.subst M a) := ih a ha hva
        _ ≤ LMonoTys.size (args.map (LMonoTy.subst M)) :=
            LMonoTy.size_lt_of_mem (List.mem_map_of_mem ha)
        _ ≤ LMonoTy.size (LMonoTy.tcons name (args.map (LMonoTy.subst M))) := by simp [LMonoTy.size]
  match t, h_occurs, h_ne with
  | .ftvar x, h, hne =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at h; subst h; exact absurd rfl hne
  | .bitvec n, h, _ => simp [LMonoTy.freeVars] at h
  | .tcons name args, h, _ =>
    simp only [LMonoTy.freeVars] at h
    obtain ⟨a, ha, hva⟩ := LMonoTys.freeVars_exists h
    intro h_eq
    have h1 := hle a hva
    have h2 : LMonoTy.size (LMonoTy.subst M a)
        < LMonoTy.size (LMonoTy.subst M (.tcons name args)) := by
      rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]; simp only [LMonoTy.size]
      have := LMonoTy.size_lt_of_mem (List.mem_map_of_mem (f := LMonoTy.subst M) ha)
      omega
    rw [h_eq] at h1; omega

/-- If every key of `S` lies in `L` and `L`, `F` are disjoint, then `S` fixes any
    type whose free variables lie in `F`. -/
private theorem subst_fix_of_keys_disjoint (S : Subst) (L F : List TyIdentifier)
    (hLF : ∀ v ∈ L, v ∉ F) (hSkeys : ∀ k ∈ HMaps.keys S, k ∈ L)
    (t : LMonoTy) (ht : LMonoTy.freeVars t ⊆ F) :
    LMonoTy.subst S t = t :=
  LMonoTy.subst_no_relevant_keys S t (fun x hx h_key => hLF x (hSkeys x h_key) (ht hx))

/-- A non-`ftvar` type cannot be mapped to an `ftvar` by any substitution. -/
private theorem subst_ne_ftvar_of_not_ftvar (M : Subst) (t : LMonoTy) (id : TyIdentifier)
    (h : ∀ x, t ≠ .ftvar x) : LMonoTy.subst M t ≠ LMonoTy.ftvar id := by
  match t with
  | .ftvar x => exact absurd rfl (h x)
  | .tcons nm ar => rw [LMonoTy.subst_tcons]; simp
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp

/-- **Combined completeness + key/value-tracking for `unifyOne`.** Under a matcher `M`
    with left variables in `L`, right variables in `F` (`L`/`F` disjoint), and `S`
    binding only `L`-keys to `F`-valued types, `unifyOne` succeeds and preserves those
    `S` invariants. -/
private theorem Constraint.unifyOne_matching_complete
    (c : Constraint) (S : SubstInfo) (L F : List TyIdentifier) (M : Subst)
    (hLF : ∀ v ∈ L, v ∉ F)
    (hMkeys : ∀ v ∈ HMaps.keys M, v ∈ L)
    (hb1 : LMonoTy.freeVars c.1 ⊆ L ++ F)
    (hb2 : LMonoTy.freeVars c.2 ⊆ F)
    (hmatch : LMonoTy.subst M c.1 = c.2)
    (hMabs : Subst.absorbs M S.subst)
    (hSkeys : ∀ k ∈ HMaps.keys S.subst, k ∈ L)
    (hSval : Subst.freeVars S.subst ⊆ F) :
    ∃ relS : ValidSubstRelation [c] S,
      Constraint.unifyOne c S = .ok relS ∧
      (∀ k ∈ HMaps.keys relS.newS.subst, k ∈ L) ∧
      Subst.freeVars relS.newS.subst ⊆ F := by
  revert hb1 hb2 hmatch hMabs hSkeys hSval
  apply Constraint.unifyOne.induct
    (motive1 := fun c S =>
      (LMonoTy.freeVars c.1 ⊆ L ++ F) → (LMonoTy.freeVars c.2 ⊆ F) →
      LMonoTy.subst M c.1 = c.2 → Subst.absorbs M S.subst →
      (∀ k ∈ HMaps.keys S.subst, k ∈ L) → Subst.freeVars S.subst ⊆ F →
      ∃ relS : ValidSubstRelation [c] S,
        Constraint.unifyOne c S = .ok relS ∧
        (∀ k ∈ HMaps.keys relS.newS.subst, k ∈ L) ∧
        Subst.freeVars relS.newS.subst ⊆ F)
    (motive2 := fun cs S =>
      (∀ p ∈ cs, LMonoTy.freeVars p.1 ⊆ L ++ F) → (∀ p ∈ cs, LMonoTy.freeVars p.2 ⊆ F) →
      (∀ p ∈ cs, LMonoTy.subst M p.1 = p.2) → Subst.absorbs M S.subst →
      (∀ k ∈ HMaps.keys S.subst, k ∈ L) → Subst.freeVars S.subst ⊆ F →
      ∃ relS : ValidSubstRelation cs S,
        Constraints.unifyCore cs S = .ok relS ∧
        (∀ k ∈ HMaps.keys relS.newS.subst, k ∈ L) ∧
        Subst.freeVars relS.newS.subst ⊆ F)
  -- Case 1: t1 == t2 — return S unchanged
  · intro S t1 t2 h_eq _ _ _ _ _ hSkeys hSval
    rw [Constraint.unifyOne.eq_def]; simp only; split
    · exact ⟨_, rfl, hSkeys, hSval⟩
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id == lty — return S unchanged
  · intro S id orig_lty h_neq _ _ _ _ _ _ _ _ hSkeys hSval
    rw [Constraint.unifyOne.eq_def]; simp only; split
    · exact absurd ‹_› h_neq
    · exact ⟨_, rfl, hSkeys, hSval⟩
  -- Case 3: ftvar id, orig_lty; occurs check — impossible under matching
  · intro S id orig_lty h_neq _ _ _ _ h_occurs _ hb2 hmatch _ hSkeys hSval
    exfalso
    have h_lty_eq : LMonoTy.subst S.subst orig_lty = orig_lty :=
      subst_fix_of_keys_disjoint S.subst L F hLF hSkeys orig_lty hb2
    change id ∈ (LMonoTy.subst S.subst orig_lty).freeVars at h_occurs
    rw [h_lty_eq] at h_occurs
    have h_ne : orig_lty ≠ .ftvar id := by
      rintro rfl; exact h_neq (by simp)
    have h_M_orig : LMonoTy.subst M orig_lty = orig_lty :=
      subst_fix_of_keys_disjoint M L F hLF hMkeys orig_lty hb2
    exact subst_ftvar_ne_of_occurs M id orig_lty h_occurs h_ne (hmatch.trans h_M_orig.symm)
  -- Case 4: ftvar id, orig_lty; existing binding sty — recursive on (sty, lty)
  · intro S id orig_lty h_neq _ _ _ _ _ sty h_some ih_rec
      _ hb2 hmatch hMabs hSkeys hSval
    -- lty = subst S orig_lty = orig_lty (S fixes F, since freeVars orig_lty ⊆ F).
    have h_lty_eq : LMonoTy.subst S.subst orig_lty = orig_lty :=
      subst_fix_of_keys_disjoint S.subst L F hLF hSkeys orig_lty hb2
    -- freeVars sty ⊆ F, so M and S both fix sty.
    have h_sty_fv : LMonoTy.freeVars sty ⊆ F := fun x hx =>
      hSval (Subst.freeVars_of_find_subset S.subst h_some hx)
    have h_M_sty : LMonoTy.subst M sty = sty :=
      subst_fix_of_keys_disjoint M L F hLF hMkeys sty h_sty_fv
    -- sty = orig_lty: subst M sty = subst M (ftvar id) = orig_lty.
    have h_sty_eq : sty = orig_lty := by
      have h1 : LMonoTy.subst M sty = LMonoTy.subst M (.ftvar id) := hMabs id sty h_some
      rw [h_M_sty] at h1; rw [h1]; exact hmatch
    -- Recursive call unifies (sty, lty) = (orig_lty, orig_lty): a trivial match.
    have ih := ih_rec
      (fun x hx => List.mem_append_right L (hb2 (h_sty_eq ▸ hx)))
      (by show LMonoTy.freeVars (LMonoTy.subst S.subst orig_lty) ⊆ F
          rw [h_lty_eq]; exact hb2)
      (by show LMonoTy.subst M sty = LMonoTy.subst S.subst orig_lty
          rw [h_lty_eq, h_M_sty]; exact h_sty_eq)
      hMabs hSkeys hSval
    obtain ⟨relS', h_call, h_keys', h_val'⟩ := ih
    rw [Constraint.unifyOne.eq_def]; simp only; split
    · exact absurd ‹_› h_neq
    · split
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind]
        rw [h_call]
        exact ⟨_, rfl, h_keys', h_val'⟩
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 5: ftvar id, orig_lty; none — insert+apply new binding [id ↦ lty]
  · intro S id orig_lty h_neq _ _ _ h_neq_lty _ h_none _ _ _ _ _ _ _
      hb1 hb2 hmatch _ hSkeys hSval
    simp only at hmatch hb1 hb2
    -- lty = subst S orig_lty = orig_lty (S fixes F).
    have h_lty_eq : LMonoTy.subst S.subst orig_lty = orig_lty :=
      subst_fix_of_keys_disjoint S.subst L F hLF hSkeys orig_lty hb2
    -- id ∉ F: else M fixes ftvar id, forcing orig_lty = ftvar id, contradicting h_neq_lty.
    have h_id_not_F : id ∉ F := by
      intro h_idF
      have h_M_id : LMonoTy.subst M (.ftvar id) = .ftvar id :=
        subst_fix_of_keys_disjoint M L F hLF hMkeys (.ftvar id) (by simpa [LMonoTy.freeVars])
      apply h_neq_lty
      show (LMonoTy.ftvar id == LMonoTy.subst S.subst orig_lty) = true
      rw [h_lty_eq, ← hmatch, h_M_id]; simp
    -- id ∈ L: it is in freeVars c.1 ⊆ L ++ F, and id ∉ F.
    have h_id_L : id ∈ L := by
      have : id ∈ L ++ F := hb1 (by simp [LMonoTy.freeVars])
      rcases List.mem_append.mp this with h | h
      · exact h
      · exact absurd h h_id_not_F
    rw [Constraint.unifyOne.eq_def]; simp only; split
    · exact absurd ‹_› h_neq
    · split
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · refine ⟨_, rfl, ?_, ?_⟩
        · -- Key inclusion: keys ⊆ L.
          intro k hk
          have hk' := HMaps.insert_keys_subset
            (Subst.apply (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst) id
            (LMonoTy.subst S.subst orig_lty) k hk
          rcases List.mem_cons.mp hk' with rfl | h_old
          · exact h_id_L
          · exact hSkeys k ((Subst.mem_keys_apply_iff _ S.subst k).mp h_old)
        · -- Value inclusion: freeVars ⊆ F.
          intro x hx
          have h_ins := Subst.freeVars_of_insert
            (Subst.apply (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst) id
            (LMonoTy.subst S.subst orig_lty) hx
          rcases List.mem_append.mp h_ins with h_apply | h_lty
          · rcases List.mem_append.mp (Subst.freeVars_of_apply_subset_alt _ S.subst h_apply) with h1 | h2
            · exact (h_lty_eq ▸ hb2) (Subst.freeVars_singleton_subset id _ h1)
            · exact hSval h2
          · exact (h_lty_eq ▸ hb2) h_lty
  -- Cases 6–9: in the (orig_lty, ftvar id) orientation orig_lty is not an ftvar, so a
  -- matcher cannot map it to ftvar id — vacuous under matching.
  · intro S orig_lty id h_ne_ftvar h_nf; intros
    refine absurd (by simp_all) (subst_ne_ftvar_of_not_ftvar M orig_lty id ?_)
    intro x hx; subst hx; exact h_nf x h_ne_ftvar rfl (HEq.refl _)
  · intro S orig_lty id h_ne_ftvar h_nf; intros
    refine absurd (by simp_all) (subst_ne_ftvar_of_not_ftvar M orig_lty id ?_)
    intro x hx; subst hx; exact h_nf x h_ne_ftvar rfl (HEq.refl _)
  · intro S orig_lty id h_ne_ftvar h_nf; intros
    refine absurd (by simp_all) (subst_ne_ftvar_of_not_ftvar M orig_lty id ?_)
    intro x hx; subst hx; exact h_nf x h_ne_ftvar rfl (HEq.refl _)
  · intro S orig_lty id h_ne_ftvar h_nf; intros
    refine absurd (by simp_all) (subst_ne_ftvar_of_not_ftvar M orig_lty id ?_)
    intro x hx; subst hx; exact h_nf x h_ne_ftvar rfl (HEq.refl _)
  -- Case 10: bitvec n1 == n2 while ¬(bitvec n1 == bitvec n2) — direct contradiction
  · intro S n1 n2 h_neq h_eq_n; intros; grind
  -- Case 11: bitvec n1 ≠ n2 — error; matcher forces n1 = n2
  · intro S n1 n2 h_neq h_neq_n; intro _ _ hmatch; intros
    exfalso; simp only at hmatch; rw [LMonoTy.subst_bitvec] at hmatch
    exact h_neq_n (by simp only [LMonoTy.bitvec.injEq] at hmatch; simp [hmatch])
  -- Case 12: tcons match — recurse on zipped args, same matcher M
  · intro S name1 args1 name2 args2 h_neq h_match _ ih_core hb1 hb2 hmatch hMabs hSkeys hSval
    simp only at hmatch hb1 hb2
    have h_name : name1 = name2 := by
      have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).1; exact eq_of_beq this
    have h_len : args1.length = args2.length := by
      have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).2; exact of_decide_eq_true this
    subst h_name
    -- Pointwise matching on the zipped args.
    have h_pw : ∀ p ∈ args1.zip args2, LMonoTy.subst M p.1 = p.2 := by
      rw [LMonoTy.subst_tcons] at hmatch
      simp only [LMonoTy.tcons.injEq, true_and] at hmatch
      rw [LMonoTys.subst_eq_map] at hmatch
      have h_map_eq := List.map_eq_iff.mp hmatch
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hi1 : i < args1.length := by
        have := List.length_zip (l₁ := args1) (l₂ := args2); omega
      rw [List.getElem_zip]
      have hmap := h_map_eq i
      rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem (by omega : i < args2.length),
        Option.map_some] at hmap
      simpa using hmap.symm
    -- freeVars bounds for zipped args from the tcons freeVars.
    have hb1' : ∀ p ∈ args1.zip args2, LMonoTy.freeVars p.1 ⊆ L ++ F := by
      intro p hp x hx
      apply hb1
      have hp1 : p.1 ∈ args1 := List.of_mem_zip hp |>.1
      show x ∈ LMonoTy.freeVars (LMonoTy.tcons name1 args1)
      rw [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset hp1 hx
    have hb2' : ∀ p ∈ args1.zip args2, LMonoTy.freeVars p.2 ⊆ F := by
      intro p hp x hx
      apply hb2
      have hp2 : p.2 ∈ args2 := List.of_mem_zip hp |>.2
      show x ∈ LMonoTy.freeVars (LMonoTy.tcons name1 args2)
      rw [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset hp2 hx
    obtain ⟨relS', h_call, h_keys', h_val'⟩ := ih_core hb1' hb2' h_pw hMabs hSkeys hSval
    rw [Constraint.unifyOne.eq_def]; simp only; split
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind]
      rw [h_call]
      exact ⟨_, rfl, h_keys', h_val'⟩
  -- Case 13: tcons name/length mismatch — error; matcher forces name & length equal
  · intro S name1 args1 name2 args2 h_neq h_mismatch; intro _ _ hmatch; intros
    exfalso; simp only at hmatch; rw [LMonoTy.subst_tcons] at hmatch
    simp only [LMonoTy.tcons.injEq] at hmatch
    apply h_mismatch
    obtain ⟨h_nm, h_args⟩ := hmatch
    subst h_nm
    rw [LMonoTys.subst_eq_map] at h_args
    simp only [beq_self_eq_true, Bool.true_and]
    have := congrArg List.length h_args; simpa using this
  -- Case 14: bitvec, tcons — error; matcher gives bitvec = tcons, impossible
  · intro S size name args h_neq; intro _ _ hmatch; intros
    exfalso; simp only at hmatch; rw [LMonoTy.subst_bitvec] at hmatch
    exact absurd hmatch (by simp)
  -- Case 15: tcons, bitvec — error; matcher gives tcons = bitvec, impossible
  · intro S name args size h_neq; intro _ _ hmatch; intros
    exfalso; simp only at hmatch; rw [LMonoTy.subst_tcons] at hmatch
    exact absurd hmatch (by simp)
  -- Case 16: unifyCore [] — return S unchanged
  · intro S _ _ _ _ hSkeys hSval
    rw [Constraints.unifyCore.eq_def]; simp only
    exact ⟨_, rfl, hSkeys, hSval⟩
  -- Case 17: unifyCore (c :: c_rest) — run head, thread matcher via MGU, recurse
  · intro S c c_rest ih1 ih2 hb1 hb2 hmatch hMabs hSkeys hSval
    -- Head constraint matching hypotheses.
    have hb1_c : LMonoTy.freeVars c.1 ⊆ L ++ F := hb1 c List.mem_cons_self
    have hb2_c : LMonoTy.freeVars c.2 ⊆ F := hb2 c List.mem_cons_self
    have hm_c : LMonoTy.subst M c.1 = c.2 := hmatch c List.mem_cons_self
    obtain ⟨relS_one, h_one, h_keys_one, h_val_one⟩ := ih1 hb1_c hb2_c hm_c hMabs hSkeys hSval
    -- M unifies c (M fixes c.2 since freeVars c.2 ⊆ F), so it absorbs relS_one via MGU.
    have h_M_fix_c2 : LMonoTy.subst M c.2 = c.2 :=
      subst_fix_of_keys_disjoint M L F hLF hMkeys c.2 hb2_c
    have hM_unif_c : LMonoTy.subst M c.1 = LMonoTy.subst M c.2 := by rw [hm_c, h_M_fix_c2]
    have hMabs_one : Subst.absorbs M relS_one.newS.subst :=
      Constraint.unifyOne_mgu c S relS_one h_one M hM_unif_c hMabs
    -- Recurse on the tail with the extended substitution.
    obtain ⟨relS_rest, h_rest, h_keys_rest, h_val_rest⟩ := ih2 relS_one
      (fun p hp => hb1 p (List.mem_cons_of_mem c hp))
      (fun p hp => hb2 p (List.mem_cons_of_mem c hp))
      (fun p hp => hmatch p (List.mem_cons_of_mem c hp))
      hMabs_one h_keys_one h_val_one
    rw [Constraints.unifyCore.eq_def]; simp only
    simp only [Bind.bind, Except.bind, Except.mapError]
    rw [h_one]; simp only; rw [h_rest]
    exact ⟨_, rfl, h_keys_rest, h_val_rest⟩

/-- **Combined completeness + key/value-tracking for `unifyCore`.** Under a matcher `M`
    for every constraint (left variables in `L`, right in `F`, `L`/`F` disjoint) and `S`
    binding only `L`-keys to `F`-valued types, `unifyCore` succeeds and preserves those
    `S` invariants. -/
private theorem Constraints.unifyCore_matching_complete
    (cs : Constraints) (S : SubstInfo) (L F : List TyIdentifier) (M : Subst)
    (hLF : ∀ v ∈ L, v ∉ F)
    (hpat : ∀ p ∈ cs, LMonoTy.freeVars p.1 ⊆ L)
    (htau : ∀ p ∈ cs, LMonoTy.freeVars p.2 ⊆ F)
    (hmatch : ∀ p ∈ cs, LMonoTy.subst M p.1 = p.2)
    (hMkeys : ∀ v ∈ HMaps.keys M, v ∈ L)
    (hMabs : Subst.absorbs M S.subst)
    (hSkeys : ∀ k ∈ HMaps.keys S.subst, k ∈ L)
    (hSval : Subst.freeVars S.subst ⊆ F) :
    ∃ relS : ValidSubstRelation cs S,
      Constraints.unifyCore cs S = .ok relS ∧
      (∀ k ∈ HMaps.keys relS.newS.subst, k ∈ L) ∧
      Subst.freeVars relS.newS.subst ⊆ F := by
  induction cs generalizing S with
  | nil =>
    rw [Constraints.unifyCore.eq_def]; simp only
    exact ⟨_, rfl, hSkeys, hSval⟩
  | cons c c_rest ih =>
    -- Head constraint.
    have hb1_c : LMonoTy.freeVars c.1 ⊆ L ++ F := fun x hx =>
      List.mem_append_left F (hpat c List.mem_cons_self hx)
    have hb2_c : LMonoTy.freeVars c.2 ⊆ F := htau c List.mem_cons_self
    have hm_c : LMonoTy.subst M c.1 = c.2 := hmatch c List.mem_cons_self
    obtain ⟨relS_one, h_one, h_keys_one, h_val_one⟩ :=
      Constraint.unifyOne_matching_complete c S L F M hLF hMkeys hb1_c hb2_c hm_c
        hMabs hSkeys hSval
    -- Thread the matcher via MGU.
    have h_M_fix_c2 : LMonoTy.subst M c.2 = c.2 :=
      subst_fix_of_keys_disjoint M L F hLF hMkeys c.2 hb2_c
    have hM_unif_c : LMonoTy.subst M c.1 = LMonoTy.subst M c.2 := by rw [hm_c, h_M_fix_c2]
    have hMabs_one : Subst.absorbs M relS_one.newS.subst :=
      Constraint.unifyOne_mgu c S relS_one h_one M hM_unif_c hMabs
    -- Recurse on the tail.
    obtain ⟨relS_rest, h_rest, h_keys_rest, h_val_rest⟩ := ih relS_one.newS
      (fun p hp => hpat p (List.mem_cons_of_mem c hp))
      (fun p hp => htau p (List.mem_cons_of_mem c hp))
      (fun p hp => hmatch p (List.mem_cons_of_mem c hp))
      hMabs_one h_keys_one h_val_one
    rw [Constraints.unifyCore.eq_def]; simp only
    simp only [Bind.bind, Except.bind, Except.mapError]
    rw [h_one]; simp only; rw [h_rest]
    exact ⟨_, rfl, h_keys_rest, h_val_rest⟩

/-- A matcher for `pat` against `τ` (`subst M pat = τ`) whose keys lie within
    `pat.freeVars`. -/
private theorem exists_restricted_matcher (pat τ : LMonoTy) (S : Subst)
    (hmatch : LMonoTy.subst S pat = τ) :
    ∃ M : Subst, (∀ v ∈ HMaps.keys M, v ∈ pat.freeVars) ∧ LMonoTy.subst M pat = τ := by
  refine ⟨[HMap.ofList (pat.freeVars.map (fun v => (v, LMonoTy.subst S (LMonoTy.ftvar v))))],
    ?_, ?_⟩
  · intro v hv
    simp only [HMaps.keys, List.append_nil] at hv
    simpa using HMap.mem_keys_ofList _ v hv
  · rw [← hmatch]
    apply agree_on_freeVars_implies_subst_eq
    intro v hv
    rw [LMonoTy.subst_unfold]
    show (match HMaps.find? [HMap.ofList (pat.freeVars.map (fun v => (v, LMonoTy.subst S (.ftvar v))))] v with
      | some sty => sty | none => LMonoTy.ftvar v) = LMonoTy.subst S (.ftvar v)
    rw [HMaps.find?_single_scope,
        HMap.find?_ofList_self_map pat.freeVars (fun v => LMonoTy.subst S (LMonoTy.ftvar v)) v hv]

/--
**Completeness of unification for matching problems.** If `τ` is a substitution
instance of `pat` (`subst S pat = τ`) and `pat` and `τ` share no free variables, then
unifying `[(pat, τ)]` from the empty substitution succeeds, and the resulting
substitution already maps `pat` to `τ`.
-/
theorem Constraints_unify_matching_complete
    (pat τ : LMonoTy) (S : Lambda.Subst)
    (hdisj  : ∀ v ∈ pat.freeVars, v ∉ τ.freeVars)
    (hmatch : LMonoTy.subst S pat = τ) :
    ∃ si : Lambda.SubstInfo,
      Lambda.Constraints.unify [(pat, τ)] Lambda.SubstInfo.empty = .ok si ∧
      LMonoTy.subst si.subst pat = τ := by
  -- Build a matcher whose keys lie inside `pat.freeVars`.
  obtain ⟨M, hMkeys, hMpat⟩ := exists_restricted_matcher pat τ S hmatch
  -- Completeness + key-tracking with L := pat.freeVars, F := τ.freeVars.
  obtain ⟨relS, h_core, h_keys, _⟩ :=
    Constraints.unifyCore_matching_complete [(pat, τ)] SubstInfo.empty
      pat.freeVars τ.freeVars M
      hdisj
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact fun _ h => h)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact fun _ h => h)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hMpat)
      hMkeys
      (by intro a t h; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at h)
      (by intro k hk; simp [SubstInfo.empty, Subst.empty, HMaps.keys] at hk)
      (by intro x hx; simp [SubstInfo.empty, Subst.empty, Subst.freeVars, HMaps.values] at hx)
  refine ⟨relS.newS, ?_, ?_⟩
  · simp only [Constraints.unify, bind, Except.bind, h_core]
  · -- subst relS pat = subst relS τ (soundness) = τ (relS avoids τ.freeVars).
    have h_unify : Constraints.unify [(pat, τ)] SubstInfo.empty = .ok relS.newS := by
      simp only [Constraints.unify, bind, Except.bind, h_core]
    have h_sound := Constraints.unify_sound [(pat, τ)] SubstInfo.empty relS.newS h_unify
      (pat, τ) List.mem_cons_self
    have h_fix : LMonoTy.subst relS.newS.subst τ = τ :=
      LMonoTy.subst_no_relevant_keys relS.newS.subst τ
        (fun x hx h_key => hdisj x (h_keys x h_key) hx)
    rw [h_sound, h_fix]

end -- public section
end Lambda

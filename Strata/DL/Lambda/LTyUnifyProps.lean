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

Properties of substitution and the soundness of `Constraints.unify`.
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

end -- public section
end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.Util.ExceptProps
public import Strata.Util.HMapsProps
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
import all Strata.Util.HMaps
import all Strata.Util.HMap
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
## Theorems for Type Substitution and Unification

Properties of substitution, and the soundness, most-general-unifier, and matching
completeness of `Constraints.unify`. Key theorems: `Constraints.unify_sound`,
`Constraints.unify_mgu`, and `Constraints_unify_matching_complete`. One-way matching
(`LMonoTy.matchSubst`) is sound: `LMonoTy.matchSubst_sound`.

Also: unification preserves any substitution property that each variable binding preserves
(`Constraint.unify_preserves`), and the ambient renaming of generated type variables keeps a
well-formed substitution well formed (`ambientSubst_WF`).

Further sections cover `Subst.ofZip` (the simultaneous substitution for a quantifier prefix),
`LMonoTy.openVars` and `LMonoTys.instantiateEnv` (defined in `LExprTypeEnv.lean`), and the
ambient renaming of generated type variables.
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
                · right; left; simp only [freeVars, List.mem_append]; right; exact h_orig
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
                · right; left; simp only [freeVars, List.mem_append]; left; exact h_orig
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
                simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
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
            · right; left; simp only [Constraints.freeVars, List.mem_append]; left; exact h1b
            · right; right; exact h1c
          · right; left; simp only [Constraints.freeVars, List.mem_append]; right; exact hk2
          · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
            · right; left; simp only [Constraints.freeVars, List.mem_append]; left
              simp only [Constraints.freeVars, List.append_nil] at h_c; exact h_c
            · right; right; exact h_s

/-- Constraint free variables distribute over concatenation. -/
theorem Constraints.freeVars_append (cs1 cs2 : Constraints) :
    Constraints.freeVars (cs1 ++ cs2) =
      Constraints.freeVars cs1 ++ Constraints.freeVars cs2 := by
  induction cs1 with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.cons_append, Constraints.freeVars, List.append_assoc, ih]

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
            · right; left; simp only [freeVars, List.mem_append]; left; exact h1b
            · right; right; exact h1c
          · right; left; simp only [freeVars, List.mem_append]; right; exact hk2
          · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
            · right; left; simp only [freeVars, List.mem_append]; left
              simp only [freeVars, List.append_nil] at h_c; exact h_c
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

/-- Soundness of one-way matching: a substitution returned by `LMonoTy.matchSubst pat ty` turns
`pat` into `ty`. -/
theorem LMonoTy.matchSubst_sound {pat ty : LMonoTy} {S : Subst}
    (h : pat.matchSubst ty = some S) : pat.subst S = ty := by
  unfold LMonoTy.matchSubst at h
  split at h
  · cases h
  · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    exact h.2 ▸ h.1

/-! ### Substitution -/

/-- Substituting a bound type variable gives its value. -/
theorem LMonoTy.subst_ftvar_of_some {S : Subst} {x : TyIdentifier} {v : LMonoTy}
    (h : HMaps.find? S x = some v) : LMonoTy.subst S (.ftvar x) = v := by
  rw [LMonoTy.subst_unfold]; simp only [h]

/-- Substituting an unbound type variable leaves it alone. -/
theorem LMonoTy.subst_ftvar_of_none {S : Subst} {x : TyIdentifier}
    (h : HMaps.find? S x = none) : LMonoTy.subst S (.ftvar x) = .ftvar x := by
  rw [LMonoTy.subst_unfold]; simp only [h]

/-- Substitutions binding a type variable alike act alike on it. -/
theorem LMonoTy.subst_ftvar_congr {S1 S2 : Subst} (x : TyIdentifier)
    (h : HMaps.find? S1 x = HMaps.find? S2 x) :
    LMonoTy.subst S1 (.ftvar x) = LMonoTy.subst S2 (.ftvar x) := by
  cases hf : HMaps.find? S1 x with
  | none => rw [LMonoTy.subst_ftvar_of_none hf, LMonoTy.subst_ftvar_of_none (h ▸ hf)]
  | some w => rw [LMonoTy.subst_ftvar_of_some hf, LMonoTy.subst_ftvar_of_some (h ▸ hf)]

/-- Substitution maps over constructor arguments. -/
theorem LMonoTy.subst_tcons_map (S : Subst) (nm : String) (args : LMonoTys) :
    LMonoTy.subst S (.tcons nm args) = .tcons nm (args.map (LMonoTy.subst S)) := by
  rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]

/-- If `S1` then `S2` agrees with `S3` on a monotype's free variables, it agrees on the monotype. -/
theorem LMonoTy.subst_subst_of_pointwise (S1 S2 S3 : Subst) (m : LMonoTy)
    (h : ∀ x ∈ LMonoTy.freeVars m,
          LMonoTy.subst S2 (LMonoTy.subst S1 (.ftvar x)) = LMonoTy.subst S3 (.ftvar x)) :
    LMonoTy.subst S2 (LMonoTy.subst S1 m) = LMonoTy.subst S3 m := by
  induction m with
  | ftvar x => exact h x (by simp [LMonoTy.freeVars])
  | bitvec n => rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons nm args ih =>
    rw [LMonoTy.subst_tcons_map, LMonoTy.subst_tcons_map, LMonoTy.subst_tcons_map,
      List.map_map]
    congr 1
    refine List.map_congr_left ?_
    intro a ha
    refine ih a ha ?_
    intro v hv
    have hv_tcons : v ∈ (LMonoTy.tcons nm args).freeVars := by
      simp only [LMonoTy.freeVars]
      exact LMonoTys.freeVars_mem_subset ha hv
    exact h v hv_tcons

/-- A well-formed substitution fixes every type variable of a type it has been applied to. -/
theorem subst_ftvar_of_mem_freeVars_subst {S : Subst} (hwf : SubstWF S) {t : LMonoTy}
    {v : TyIdentifier} (hv : v ∈ LMonoTy.freeVars (LMonoTy.subst S t)) :
    LMonoTy.subst S (.ftvar v) = .ftvar v := by
  have hkeys := LMonoTy.subst_keys_not_in_substituted_type hwf t
  simp only [List.all_eq_true, decide_eq_true_eq] at hkeys
  exact LMonoTy.subst_ftvar_of_none
    (Strata.Util.HMaps.not_mem_keys_find?_none S v (fun hk => hkeys v hk hv))

/-- The empty substitution is the identity. -/
theorem LMonoTy.subst_nil (m : LMonoTy) : LMonoTy.subst [] m = m :=
  LMonoTy.subst_of_hasEmptyScopes (by simp [Subst.hasEmptyScopes]) m

/-- A ground monotype is fixed by every substitution. -/
theorem LMonoTy.subst_ground (S : Subst) (m : LMonoTy) (h : LMonoTy.freeVars m = []) :
    LMonoTy.subst S m = m :=
  LMonoTy.subst_no_relevant_keys S m (fun x hx => absurd (h ▸ hx) (by simp))

/-- A single-variable substitution fixes every other type variable. -/
private theorem Subst.find?_singleton_ne (a x : TyIdentifier) (v : LMonoTy) (h : x ≠ a) :
    HMaps.find? (Subst.singleton a v) x = none := by
  simp only [Subst.singleton, HMaps.find?, HMap.find?_single_ne a x v (by simp [bne, h])]

/-- Substituting `t` for `x` and then `S` is `S` with `x ↦ subst S t` pushed in front. -/
theorem LMonoTy.subst_push_single (x : TyIdentifier) (t : LMonoTy) (S : Subst) (m : LMonoTy) :
    LMonoTy.subst (HMap.single x (LMonoTy.subst S t) :: S) m
      = LMonoTy.subst S (LMonoTy.subst (Subst.singleton x t) m) := by
  induction m with
  | ftvar y =>
    by_cases hy : y = x
    · subst hy
      rw [LMonoTy.subst_ftvar_of_some
          (HMaps.find?_cons_single_self y (LMonoTy.subst S t) S),
        LMonoTy.subst_ftvar_of_some (Subst.find?_singleton_self y t)]
    · have hne : y != x := by simp [bne, hy]
      rw [LMonoTy.subst_ftvar_of_none (Subst.find?_singleton_ne x y t hy)]
      exact LMonoTy.subst_ftvar_congr y
        (HMaps.find?_cons_single_ne x y (LMonoTy.subst S t) S hne)
  | bitvec n =>
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons nm args ih =>
    rw [LMonoTy.subst_tcons_map, LMonoTy.subst_tcons_map, LMonoTy.subst_tcons_map,
      List.map_map]
    congr 1
    exact List.map_congr_left ih

/-- Inserting `a ↦ (ρ ++ S)(a)` between `ρ` and `S` changes no type variable's image. -/
theorem LMonoTy.subst_ftvar_cons_of_value (ρ S : Subst) (a kk : TyIdentifier) :
    LMonoTy.subst (ρ ++ (HMap.single a (LMonoTy.subst (ρ ++ S) (.ftvar a)) :: S)) (.ftvar kk)
      = LMonoTy.subst (ρ ++ S) (.ftvar kk) := by
  cases hfr : HMaps.find? ρ kk with
  | some w =>
    rw [LMonoTy.subst_ftvar_of_some (HMaps.find?_append_of_some hfr
        (HMap.single a (LMonoTy.subst (ρ ++ S) (.ftvar a)) :: S)),
      LMonoTy.subst_ftvar_of_some (HMaps.find?_append_of_some hfr S)]
  | none =>
    rw [LMonoTy.subst_ftvar_congr kk (HMaps.find?_append_of_none hfr
        (HMap.single a (LMonoTy.subst (ρ ++ S) (.ftvar a)) :: S))]
    by_cases hka : kk = a
    · subst hka
      rw [LMonoTy.subst_ftvar_of_some (HMaps.find?_cons_single_self kk
        (LMonoTy.subst (ρ ++ S) (.ftvar kk)) S)]
    · rw [LMonoTy.subst_ftvar_congr kk (HMaps.find?_cons_single_ne a kk
        (LMonoTy.subst (ρ ++ S) (.ftvar a)) S (by simp [bne, hka]))]
      exact (LMonoTy.subst_ftvar_congr kk (HMaps.find?_append_of_none hfr S)).symm

/-- Applying `ρ` and then `S` to a monotype is applying a single substitution to it. -/
theorem LMonoTy.exists_subst_subst (S ρ : Subst) (m : LMonoTy) :
    ∃ τ : Subst, LMonoTy.subst S (LMonoTy.subst ρ m) = LMonoTy.subst τ m := by
  refine ⟨Strata.Util.HMaps.ofScopes [(LMonoTy.freeVars m).map
    (fun v => (v, LMonoTy.subst S (LMonoTy.subst ρ (.ftvar v))))], ?_⟩
  refine LMonoTy.subst_subst_of_pointwise ρ S _ m ?_
  intro v hv
  symm
  apply LMonoTy.subst_ftvar_of_some
  simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]
  exact HMap.find?_ofList_self_map _ _ v hv

/-- A substitution that fixes every free type variable of a monotype fixes the monotype. -/
theorem subst_eq_self_of_fix (σ : Subst) (m : LMonoTy)
    (h : ∀ v ∈ LMonoTy.freeVars m, LMonoTy.subst σ (.ftvar v) = .ftvar v) :
    LMonoTy.subst σ m = m := by
  have hagree : ∀ v ∈ LMonoTy.freeVars m,
      LMonoTy.subst [] (LMonoTy.subst [] (.ftvar v)) = LMonoTy.subst σ (.ftvar v) := by
    intro v hv
    rw [h v hv, LMonoTy.subst_nil, LMonoTy.subst_nil]
  have hag := LMonoTy.subst_subst_of_pointwise [] [] σ m hagree
  rw [LMonoTy.subst_nil, LMonoTy.subst_nil] at hag
  exact hag.symm

/-! ### Simultaneous substitution for a quantifier prefix: `Subst.ofZip` -/

/-- `LTy.openFull` substitutes a scheme's binders simultaneously. -/
theorem LTy.openFull_eq_subst_ofZip (vars : List TyIdentifier) (mty : LMonoTy)
    (vals : List LMonoTy) :
    LTy.openFull (.forAll vars mty) vals = LMonoTy.subst (Subst.ofZip vars vals) mty := by
  simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, Subst.ofZip]

/-- A lookup in `Subst.ofZip` is a lookup in the zipped list. -/
private theorem Subst.find?_ofZip (vars : List TyIdentifier) (vals : List LMonoTy)
    (x : TyIdentifier) :
    HMaps.find? (Subst.ofZip vars vals) x
      = HMap.find? (HMap.ofList (List.zip vars vals)) x := by
  simp only [Subst.ofZip, HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]

/-- `Subst.ofZip` binds only names in `vars`. -/
theorem Subst.mem_keys_ofZip {vars : List TyIdentifier} {vals : List LMonoTy}
    {x : TyIdentifier} (h : x ∈ HMaps.keys (Subst.ofZip vars vals)) : x ∈ vars := by
  simp only [Subst.ofZip, HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.keys,
    List.append_nil] at h
  have hzip := HMap.mem_keys_ofList (List.zip vars vals) x h
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hzip
  exact hpx ▸ (List.of_mem_zip hp).1

/-- `Subst.ofZip` produces only values in `vals`. -/
theorem Subst.mem_values_ofZip {vars : List TyIdentifier} {vals : List LMonoTy} {w : LMonoTy}
    (h : w ∈ HMaps.values (Subst.ofZip vars vals)) : w ∈ vals := by
  simp only [Subst.ofZip, HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.values,
    List.append_nil] at h
  have hzip := HMap.mem_values_ofList (List.zip vars vals) w h
  obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hzip
  exact hpw ▸ (List.of_mem_zip hp).2

/-- `Subst.ofZip` leaves alone every name that is not one of `vars`. -/
theorem Subst.find?_ofZip_of_not_mem {vars : List TyIdentifier} {vals : List LMonoTy}
    {x : TyIdentifier} (h : x ∉ vars) :
    HMaps.find? (Subst.ofZip vars vals) x = none := by
  cases hf : HMaps.find? (Subst.ofZip vars vals) x with
  | none => rfl
  | some v => exact absurd (Subst.mem_keys_ofZip (HMaps.find?_mem_keys _ hf)) h

/-- `Subst.ofZip vars vals` fixes any monotype with no free name in `vars`. -/
theorem LMonoTy.subst_ofZip_eq_self {vars : List TyIdentifier} {vals : List LMonoTy}
    (m : LMonoTy) (h : ∀ x ∈ LMonoTy.freeVars m, x ∉ vars) :
    LMonoTy.subst (Subst.ofZip vars vals) m = m :=
  LMonoTy.subst_no_relevant_keys _ m (fun x hx hk => h x hx (Subst.mem_keys_ofZip hk))

/-- `Subst.ofZip` binds every name of `vars` that has a paired value. -/
theorem Subst.find?_ofZip_isSome_of_mem {vars : List TyIdentifier} {vals : List LMonoTy}
    (hlen : vars.length ≤ vals.length) {x : TyIdentifier} (hx : x ∈ vars) :
    (HMaps.find? (Subst.ofZip vars vals) x).isSome := by
  have hkeys : x ∈ (List.zip vars vals).map Prod.fst := by
    rw [List.map_fst_zip hlen]
    exact hx
  obtain ⟨w, hw⟩ := HMap.find?_ofList_of_mem_keys _ x hkeys
  rw [Subst.find?_ofZip, hw]
  rfl

/-- `Subst.ofZip` sends a head name that does not recur in the tail to the head value. -/
private theorem Subst.find?_ofZip_cons_self {a : TyIdentifier} {rest : List TyIdentifier}
    (v : LMonoTy) (vals : List LMonoTy) (h_a : a ∉ rest) :
    HMaps.find? (Subst.ofZip (a :: rest) (v :: vals)) a = some v := by
  have h_keys : a ∉ (List.zip rest vals).map Prod.fst := fun hmem =>
    h_a ((List.map_fst_zip_sublist rest vals).subset hmem)
  rw [Subst.find?_ofZip,
    show List.zip (a :: rest) (v :: vals) = (a, v) :: List.zip rest vals from rfl,
    HMap.find?_ofList_cons_eq_find?_insert a v (List.zip rest vals) h_keys]
  exact HMap.find?_insert_self _ a v

/-- If the head name does not recur, `Subst.ofZip` agrees with the tails' on every other name. -/
private theorem Subst.find?_ofZip_cons_ne {a : TyIdentifier} {rest : List TyIdentifier}
    (v : LMonoTy) (vals : List LMonoTy) {x : TyIdentifier} (h_a : a ∉ rest) (hxa : x ≠ a) :
    HMaps.find? (Subst.ofZip (a :: rest) (v :: vals)) x
      = HMaps.find? (Subst.ofZip rest vals) x := by
  have h_keys : a ∉ (List.zip rest vals).map Prod.fst := fun hmem =>
    h_a ((List.map_fst_zip_sublist rest vals).subset hmem)
  rw [Subst.find?_ofZip,
    show List.zip (a :: rest) (v :: vals) = (a, v) :: List.zip rest vals from rfl,
    HMap.find?_ofList_cons_eq_find?_insert a v (List.zip rest vals) h_keys,
    HMap.find?_insert_ne _ a x v (by simp [bne, hxa]), ← Subst.find?_ofZip rest vals x]

/-- When the names are distinct, `Subst.ofZip` sends a name to the value paired with it. -/
theorem Subst.find?_ofZip_of_mem_zip {vars : List TyIdentifier} {vals : List LMonoTy}
    (h_nd : vars.Nodup) {x : TyIdentifier} {w : LMonoTy} (h : (x, w) ∈ List.zip vars vals) :
    HMaps.find? (Subst.ofZip vars vals) x = some w := by
  induction vars generalizing vals with
  | nil => simp only [List.zip_nil_left, List.not_mem_nil] at h
  | cons a rest ih =>
    cases vals with
    | nil => simp only [List.zip_nil_right, List.not_mem_nil] at h
    | cons v vs =>
      have h_a_rest : a ∉ rest := (List.nodup_cons.mp h_nd).1
      rcases List.mem_cons.mp h with heq | htl
      · have hxa : x = a := congrArg Prod.fst heq
        have hwv : w = v := congrArg Prod.snd heq
        subst hxa; subst hwv
        exact Subst.find?_ofZip_cons_self w vs h_a_rest
      · have hx_rest : x ∈ rest := (List.of_mem_zip htl).1
        have hxa : x ≠ a := fun hc => h_a_rest (hc ▸ hx_rest)
        rw [Subst.find?_ofZip_cons_ne v vs h_a_rest hxa]
        exact ih (List.nodup_cons.mp h_nd).2 htl

/-- If the head name does not recur and its value avoids the other names, `Subst.ofZip`
    substitutes the head first and the rest after. -/
theorem LMonoTy.subst_ofZip_cons {a : TyIdentifier} {rest : List TyIdentifier} {v : LMonoTy}
    {vals : List LMonoTy} (m : LMonoTy) (h_a : a ∉ rest)
    (h_v : ∀ x ∈ LMonoTy.freeVars v, x ∉ rest) :
    LMonoTy.subst (Subst.ofZip (a :: rest) (v :: vals)) m
      = LMonoTy.subst (Subst.ofZip rest vals) (LMonoTy.subst (Subst.singleton a v) m) := by
  refine (LMonoTy.subst_subst_of_pointwise (Subst.singleton a v) (Subst.ofZip rest vals)
    (Subst.ofZip (a :: rest) (v :: vals)) m ?_).symm
  intro x _
  by_cases hxa : x = a
  · subst hxa
    rw [LMonoTy.subst_ftvar_of_some (Subst.find?_singleton_self x v),
      LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_cons_self v vals h_a)]
    exact LMonoTy.subst_ofZip_eq_self v h_v
  · rw [LMonoTy.subst_ftvar_of_none (Subst.find?_singleton_ne a x v hxa)]
    exact LMonoTy.subst_ftvar_congr x (Subst.find?_ofZip_cons_ne v vals h_a hxa).symm

/-- Applying `Subst.ofZip fs vals` to each name of distinct `fs` gives back `vals`. -/
private theorem map_subst_ofZip_ftvar (fs : List TyIdentifier) (vals : List LMonoTy)
    (hlen : vals.length = fs.length) (hnd : fs.Nodup) :
    (fs.map fun f => LMonoTy.subst (Subst.ofZip fs vals) (.ftvar f)) = vals := by
  induction fs generalizing vals with
  | nil =>
    cases vals with
    | nil => rfl
    | cons v vs => simp at hlen
  | cons f rest ih =>
    cases vals with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons v vs =>
      have hf : f ∉ rest := (List.nodup_cons.mp hnd).1
      have hr : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hlen' : vs.length = rest.length := by
        simp only [List.length_cons] at hlen
        omega
      have hhead : LMonoTy.subst (Subst.ofZip (f :: rest) (v :: vs)) (.ftvar f) = v :=
        LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_cons_self v vs hf)
      have htail : rest.map (fun g =>
          LMonoTy.subst (Subst.ofZip (f :: rest) (v :: vs)) (.ftvar g)) = vs := by
        calc
          _ = rest.map (fun g => LMonoTy.subst (Subst.ofZip rest vs) (.ftvar g)) := by
            apply List.map_congr_left
            intro g hg
            have hgf : g ≠ f := fun h => hf (h ▸ hg)
            exact LMonoTy.subst_ftvar_congr g
              (Subst.find?_ofZip_cons_ne v vs hf hgf)
          _ = vs := ih vs hlen' hr
      rw [List.map_cons, hhead]
      exact congrArg (fun tail => v :: tail) htail

/-- Renaming a prefix, possibly with repeats, to distinct fresh names and substituting `vals` for
    them equals substituting `vals` for the prefix. -/
theorem LMonoTy.subst_ofZip_launder {vars fs : List TyIdentifier} {vals : List LMonoTy}
    (m : LMonoTy) (hfs : fs.length = vars.length) (hvals : vals.length = vars.length)
    (hnd : fs.Nodup) (hfresh : ∀ f ∈ fs, f ∉ LMonoTy.freeVars m) :
    LMonoTy.subst (Subst.ofZip fs vals)
        (LMonoTy.subst (Subst.ofZip vars (fs.map LMonoTy.ftvar)) m) =
      LMonoTy.subst (Subst.ofZip vars vals) m := by
  have hvalsfs : vals.length = fs.length := hvals.trans hfs.symm
  have hmap := map_subst_ofZip_ftvar fs vals hvalsfs hnd
  have hzip : List.zip vars vals =
      (List.zip vars (fs.map LMonoTy.ftvar)).map
        (fun p => (p.1, LMonoTy.subst (Subst.ofZip fs vals) p.2)) := by
    calc
      _ = List.zip vars ((fs.map LMonoTy.ftvar).map
          (LMonoTy.subst (Subst.ofZip fs vals))) := by
            apply congrArg (List.zip vars)
            rw [List.map_map]
            exact hmap.symm
      _ = _ := by rw [List.zip_map_right]; rfl
  refine LMonoTy.subst_subst_of_pointwise _ _ _ m ?_
  intro x hx
  have hfind : HMaps.find? (Subst.ofZip vars vals) x =
      (HMaps.find? (Subst.ofZip vars (fs.map LMonoTy.ftvar)) x).map
        (LMonoTy.subst (Subst.ofZip fs vals)) := by
    simp only [Subst.find?_ofZip]
    rw [hzip, HMap.find?_ofList_map_snd]
  cases hr : HMaps.find? (Subst.ofZip vars (fs.map LMonoTy.ftvar)) x with
  | some w =>
      have hz : HMaps.find? (Subst.ofZip vars vals) x =
          some (LMonoTy.subst (Subst.ofZip fs vals) w) := by
        rw [hfind, hr]
        rfl
      rw [LMonoTy.subst_ftvar_of_some hr, LMonoTy.subst_ftvar_of_some hz]
  | none =>
      have hxvars : x ∉ vars := by
        intro hmem
        have hlen : vars.length ≤ (fs.map LMonoTy.ftvar).length := by
          simp only [List.length_map]
          omega
        have hsome := Subst.find?_ofZip_isSome_of_mem hlen hmem
        rw [hr] at hsome
        contradiction
      have hxfs : x ∉ fs := fun hmem => hfresh x hmem hx
      have hq : HMaps.find? (Subst.ofZip fs vals) x = none :=
        Subst.find?_ofZip_of_not_mem hxfs
      have hz : HMaps.find? (Subst.ofZip vars vals) x = none := by
        rw [hfind, hr]
        rfl
      rw [LMonoTy.subst_ftvar_of_none hr, LMonoTy.subst_ftvar_of_none hq,
        LMonoTy.subst_ftvar_of_none hz]

/-- Opening a scheme whose head binder does not recur drops it and substitutes it in the body. -/
theorem LTy.open_cons_of_not_mem {a : TyIdentifier} {rest : List TyIdentifier} (t : LMonoTy)
    (mty : LMonoTy) (h_a : a ∉ rest) :
    LTy.open a t (.forAll (a :: rest) mty)
      = .forAll rest (LMonoTy.subst (Subst.singleton a t) mty) := by
  have h_keep : ∀ x ∈ rest, (!List.elem x [a]) = true := by
    intro x hx
    have hxa : x ≠ a := fun hc => h_a (hc ▸ hx)
    simp [hxa]
  have h_filter : (a :: rest).removeAll [a] = rest := by
    simp only [List.removeAll, List.filter_cons, List.elem_cons, List.elem_nil,
      beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
    exact List.filter_eq_self.mpr h_keep
  simp only [LTy.open, List.mem_cons, true_or, ite_true, h_filter]

/-! ### Instantiating a scheme that quantifies nothing -/

/-- Lookup in a stack with one empty scope misses. -/
private theorem find?_ofScopes_nilScope (x : TyIdentifier) :
    HMaps.find? (Strata.Util.HMaps.ofScopes ([[]] : List (List (TyIdentifier × LMonoTy)))) x =
      none := by
  simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]
  cases h : HMap.find? (HMap.ofList ([] : List (TyIdentifier × LMonoTy))) x with
  | none => rfl
  | some v => exact absurd (HMap.mem_keys_ofList _ x (HMap.find?_mem_keys _ h)) (by simp)

/-- Substituting over a stack with one empty scope is the identity. -/
theorem subst_ofScopes_nilScope (mty : LMonoTy) :
    LMonoTy.subst (Strata.Util.HMaps.ofScopes ([[]] : List (List (TyIdentifier × LMonoTy)))) mty =
      mty := by
  induction mty with
  | ftvar x => rw [LMonoTy.subst_unfold]; simp only [find?_ofScopes_nilScope]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    congr 1
    rw [List.map_congr_left ih]; exact List.map_id_fun' ▸ rfl

/-- Instantiating a scheme that quantifies nothing returns its body. -/
theorem openFull_of_boundVars_nil (ty : LTy) (h : LTy.boundVars ty = [])
    (tys : List LMonoTy) : LTy.openFull ty tys = LTy.toMonoTypeUnsafe ty := by
  simp only [LTy.openFull, h, List.zip_nil_left]
  exact subst_ofScopes_nilScope _

/-- Opening an unquantified type scheme returns its body. -/
theorem openFull_forAll_nil (t : LMonoTy) (tys : LMonoTys) :
    LTy.openFull (.forAll [] t) tys = t :=
  openFull_of_boundVars_nil (.forAll [] t) rfl tys

/-! ### Substitution and `openVars` -/

namespace LExpr

/-- Looking `x` up in `zip vars vals`, defaulting to `x`, is `openVars vars vals` on `x`. -/
private theorem find?_ofList_zip_eq_openVars_ftvar
    (vars : List TyIdentifier) (vals : LMonoTys) (x : TyIdentifier)
    (h_len : vars.length = vals.length) (h_nodup : vars.Nodup) :
    (match HMap.find? (HMap.ofList (List.zip vars vals)) x with
      | some sty => sty | none => .ftvar x) = LMonoTy.openVars vars vals (.ftvar x) := by
  simp only [LMonoTy.openVars]
  have h_keys : (List.zip vars vals).map Prod.fst = vars := List.map_fst_zip (by omega)
  have h_pw : (List.zip vars vals).Pairwise (fun a b => (a.1 == b.1) = false) := by
    have h_vars_nd : ((List.zip vars vals).map Prod.fst).Nodup := by rw [h_keys]; exact h_nodup
    have h_nd_fst : (List.zip vars vals).Pairwise (fun a b => a.1 ≠ b.1) :=
      (List.pairwise_map).mp ((List.nodup_iff_pairwise_ne).mp h_vars_nd)
    exact h_nd_fst.imp (by intro a b h; simpa using h)
  cases h_find : (List.zip vars vals).find? (fun p => p.1 == x) with
  | some p =>
    obtain ⟨k, v⟩ := p
    have h_mem : (⟨k, v⟩ : TyIdentifier × LMonoTy) ∈ List.zip vars vals :=
      List.mem_of_find?_eq_some h_find
    have h_kx : (k == x) = true := by
      have h_find_eq := List.find?_some h_find; simpa using h_find_eq
    have h_get : HMap.find? (HMap.ofList (List.zip vars vals)) x = some v := by
      simp only [HMap.find?, HMap.ofList]
      exact Std.HashMap.getElem?_ofList_of_mem h_kx h_pw h_mem
    rw [h_get]
  | none =>
    have h_notin : List.contains ((List.zip vars vals).map Prod.fst) x = false := by
      simp only [List.contains_eq_mem, decide_eq_false_iff_not]
      intro hx_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hx_mem
      have h_pred : (fun p : TyIdentifier × LMonoTy => p.1 == x) p = true := by
        simp [hp_eq]
      exact absurd (List.find?_eq_none.mp h_find p hp_mem) (by simp [h_pred])
    have h_none : HMap.find? (HMap.ofList (List.zip vars vals)) x = none := by
      simp only [HMap.find?, HMap.ofList]
      exact Std.HashMap.getElem?_ofList_of_contains_eq_false h_notin
    rw [h_none]

mutual
/-- For distinct `vars` of the same length as `vals`, substituting the scope
    `zip vars vals` into a type is opening it with `vals`. -/
theorem subst_ofScopes_zip_eq_openVars
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_len : vars.length = vals.length) (h_nodup : vars.Nodup) :
    LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip vars vals]) body =
    LMonoTy.openVars vars vals body := by
  match body with
  | .ftvar x =>
    rw [LMonoTy.subst_unfold]
    simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
               HMaps.find?_single_scope]
    exact find?_ofList_zip_eq_openVars_ftvar vars vals x h_len h_nodup
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp only [LMonoTy.openVars]
  | .tcons name args =>
    rw [LMonoTy.subst_tcons]
    simp only [LMonoTy.openVars]
    congr 1
    exact subst_ofScopes_zip_eq_openVarsList vars vals args h_len h_nodup

/-- For distinct `vars` of the same length as `vals`, substituting the scope
    `zip vars vals` into a list of types is opening them with `vals`. -/
private theorem subst_ofScopes_zip_eq_openVarsList
    (vars : List TyIdentifier) (vals : LMonoTys) (bodies : LMonoTys)
    (h_len : vars.length = vals.length) (h_nodup : vars.Nodup) :
    LMonoTys.subst (Strata.Util.HMaps.ofScopes [List.zip vars vals]) bodies =
    LMonoTys.openVars vars vals bodies := by
  match bodies with
  | [] => rw [LMonoTys.subst_nil, LMonoTys.openVars]
  | hd :: tl =>
    rw [LMonoTys.subst_eq_map, List.map_cons, LMonoTys.openVars]
    congr 1
    · exact subst_ofScopes_zip_eq_openVars vars vals hd h_len h_nodup
    · rw [← LMonoTys.subst_eq_map]
      exact subst_ofScopes_zip_eq_openVarsList vars vals tl h_len h_nodup
end

end LExpr


end -- public section

namespace LExpr

mutual
/-- If `x` is free in `body` and first paired with `v`, `openVars` keeps `v`'s free variables. -/
private theorem freeVars_openVars_of_find? (vars : List TyIdentifier) (vals : LMonoTys)
    (x : TyIdentifier) (v : LMonoTy)
    (hfind : (List.zip vars vals).find? (fun q => q.1 == x) = some (x, v))
    (body : LMonoTy) (hx : x ∈ LMonoTy.freeVars body) :
    ∀ tv, tv ∈ LMonoTy.freeVars v →
      tv ∈ LMonoTy.freeVars (LMonoTy.openVars vars vals body) := by
  match body with
  | .ftvar y =>
    have hxy : x = y := by simpa [LMonoTy.freeVars] using hx
    subst hxy
    intro tv htv
    simp only [LMonoTy.openVars, hfind]
    exact htv
  | .bitvec _ => simp [LMonoTy.freeVars] at hx
  | .tcons nm args =>
    intro tv htv
    simp only [LMonoTy.openVars, LMonoTy.freeVars]
    exact freeVarsList_openVars_of_find? vars vals x v hfind args
      (by simpa [LMonoTy.freeVars] using hx) tv htv

/-- If `x` is free in `bodies` and first paired with `v`, `openVars` keeps `v`'s free variables. -/
private theorem freeVarsList_openVars_of_find? (vars : List TyIdentifier) (vals : LMonoTys)
    (x : TyIdentifier) (v : LMonoTy)
    (hfind : (List.zip vars vals).find? (fun q => q.1 == x) = some (x, v))
    (bodies : LMonoTys) (hx : x ∈ LMonoTys.freeVars bodies) :
    ∀ tv, tv ∈ LMonoTy.freeVars v →
      tv ∈ LMonoTys.freeVars (LMonoTys.openVars vars vals bodies) := by
  match bodies with
  | [] => simp [LMonoTys.freeVars] at hx
  | hd :: tl =>
    intro tv htv
    rw [LMonoTys.freeVars_of_cons, List.mem_append] at hx
    show tv ∈ LMonoTys.freeVars
      (LMonoTy.openVars vars vals hd :: LMonoTys.openVars vars vals tl)
    rw [LMonoTys.freeVars_of_cons, List.mem_append]
    rcases hx with hx | hx
    · exact Or.inl (freeVars_openVars_of_find? vars vals x v hfind hd hx tv htv)
    · exact Or.inr (freeVarsList_openVars_of_find? vars vals x v hfind tl hx tv htv)
end

/-- Opening a body containing every name of `vars` keeps the free variables of `vals` free. -/
theorem openVars_freeVars_superset (vars : List TyIdentifier) (vals : LMonoTys)
    (body : LMonoTy) (hnd : vars.Nodup) (hlen : vars.length = vals.length)
    (hused : ∀ tv ∈ vars, tv ∈ LMonoTy.freeVars body) :
    ∀ tv, tv ∈ LMonoTys.freeVars vals →
      tv ∈ LMonoTy.freeVars (LMonoTy.openVars vars vals body) := by
  intro tv htv
  obtain ⟨v, hv, htvv⟩ := LMonoTys.freeVars_exists htv
  obtain ⟨x, hxz⟩ := List.mem_zip_2 hlen hv
  exact freeVars_openVars_of_find? vars vals x v (find?_zip_of_mem vars vals x v hxz hnd)
    body (hused x (List.of_mem_zip hxz).1) tv htvv

mutual
/-- For a body over `vars`, substitution commutes with opening by `vals`. -/
theorem subst_openVars_comm (S : Subst)
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTy.subst S (LMonoTy.openVars vars vals body) =
    LMonoTy.openVars vars (vals.map (LMonoTy.subst S)) body := by
  match body with
  | .ftvar x =>
    have h_x_in : x ∈ vars := h_wf x (by simp [LMonoTy.freeVars])
    clear h_wf
    induction vars generalizing vals with
    | nil => simp at h_x_in
    | cons v vs ih =>
      cases vals with
      | nil => simp at h_len
      | cons vl vls =>
        by_cases h_eq : v = x
        · subst h_eq
          simp only [LMonoTy.openVars, List.map_cons, List.zip_cons_cons,
            List.find?_cons, beq_self_eq_true]
        · have h_x_vs : x ∈ vs := by
            cases h_x_in with
            | head => exact absurd rfl h_eq
            | tail _ h => exact h
          have hbeq : (v == x) = false := by simp [h_eq]
          simp only [LMonoTy.openVars, List.map_cons, List.zip_cons_cons,
            List.find?_cons, hbeq]
          have h_ih := ih vls (by simpa using h_len) h_x_vs
          simpa only [LMonoTy.openVars] using h_ih
  | .bitvec n =>
    simp only [LMonoTy.openVars, LMonoTy.subst_bitvec]
  | .tcons name args =>
    simp only [LMonoTy.openVars, LMonoTy.subst_tcons]
    congr 1
    exact subst_openVarsList_comm S vars vals args
      (fun tv htv => h_wf tv (by simp only [LMonoTy.freeVars]; exact htv)) h_len

/-- For bodies over `vars`, substitution commutes with opening by `vals`. -/
private theorem subst_openVarsList_comm (S : Subst)
    (vars : List TyIdentifier) (vals : LMonoTys) (bodies : LMonoTys)
    (h_wf : ∀ tv, tv ∈ LMonoTys.freeVars bodies → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTys.subst S (LMonoTys.openVars vars vals bodies) =
    LMonoTys.openVars vars (vals.map (LMonoTy.subst S)) bodies := by
  match bodies with
  | [] =>
    rw [LMonoTys.openVars, LMonoTys.subst_nil, LMonoTys.openVars]
  | hd :: tl =>
    rw [LMonoTys.openVars, LMonoTys.subst_eq_map, List.map_cons, LMonoTys.openVars]
    congr 1
    · have h_mem_hd : ∀ tv, tv ∈ hd.freeVars → tv ∈ LMonoTys.freeVars (hd :: tl) := by
        intro tv htv
        simp only [LMonoTys.freeVars]; exact List.mem_append_left _ htv
      exact subst_openVars_comm S vars vals hd
        (fun tv htv => h_wf tv (h_mem_hd tv htv)) h_len
    · rw [← LMonoTys.subst_eq_map]
      have h_mem_tl : ∀ tv, tv ∈ LMonoTys.freeVars tl → tv ∈ LMonoTys.freeVars (hd :: tl) := by
        intro tv htv
        simp only [LMonoTys.freeVars]; exact List.mem_append_right _ htv
      exact subst_openVarsList_comm S vars vals tl
        (fun tv htv => h_wf tv (h_mem_tl tv htv)) h_len
end

/-! ### `LTy.subst.go` and `buildSubstFromFunction` -/

/-- Every key left by `LTy.subst.go` was in the original substitution. -/
private theorem subst_go_key_in_original (S : Subst) (xs : List TyIdentifier)
    (a : TyIdentifier) (h : a ∈ HMaps.keys (LTy.subst.go xs S)) :
    a ∈ HMaps.keys S := by
  induction xs generalizing S with
  | nil => simpa [LTy.subst.go] using h
  | cons x rest ih =>
    simp only [LTy.subst.go] at h
    exact HMaps.keys_remove_subset S x a (ih (S.remove x) h)

/-- A key left by `LTy.subst.go xs S` is not one of the removed names `xs`. -/
theorem subst_go_key_not_in_removed (S : Subst) (xs : List TyIdentifier)
    (a : TyIdentifier) (h : a ∈ HMaps.keys (LTy.subst.go xs S)) :
    a ∉ xs := by
  induction xs generalizing S with
  | nil => simp
  | cons x rest ih =>
    simp only [LTy.subst.go] at h
    intro h_mem
    rcases List.mem_cons.mp h_mem with rfl | h_rest
    · -- a = x: a would be a key of S.remove a
      have h_a_key := subst_go_key_in_original (S.remove a) rest a h
      obtain ⟨v, hv⟩ := HMaps.find?_of_mem_keys (S.remove a) a h_a_key
      rw [HMaps.find?_remove_self S a] at hv
      exact absurd hv (by simp)
    · exact ih (S.remove x) h h_rest

/-- `buildSubstFromFunction l g` sends each member `v` of `l` to `g v`. -/
public theorem find?_buildSubstFromFunction (l : List TyIdentifier) (g : TyIdentifier → LMonoTy)
    (v : TyIdentifier) (hv : v ∈ l) :
    HMap.find? (buildSubstFromFunction l g) v = some (g v) := by
  induction l with
  | nil => simp at hv
  | cons w ws ih =>
    simp only [buildSubstFromFunction, List.foldr_cons]
    by_cases h_eq : v = w
    · subst h_eq; rw [HMap.find?_insert_self]
    · have h_bne : v != w := bne_iff_ne.mpr h_eq
      rw [HMap.find?_insert_ne _ w v (g w) h_bne]
      exact ih (by cases hv with | head => exact absurd rfl h_eq | tail _ h => exact h)

/-- `buildSubstFromFunction l g` binds no name outside `l`. -/
public theorem find?_buildSubstFromFunction_of_not_mem (l : List TyIdentifier)
    (g : TyIdentifier → LMonoTy)
    (v : TyIdentifier) (hv : v ∉ l) :
    HMap.find? (buildSubstFromFunction l g) v = none := by
  induction l with
  | nil => exact HMap.find?_empty v
  | cons w ws ih =>
    have h_eq : v ≠ w := fun hc => hv (by rw [hc]; exact List.mem_cons_self)
    simp only [buildSubstFromFunction, List.foldr_cons]
    rw [HMap.find?_insert_ne _ w v (g w) (bne_iff_ne.mpr h_eq)]
    exact ih (fun hm => hv (List.mem_cons_of_mem w hm))

/-- `LTy.subst.go xs S` fixes a type in which no key of `S` outside `xs` occurs. -/
theorem subst_go_eq_self_of_irrelevant_keys (S : Subst)
    (xs : List TyIdentifier) (body : LMonoTy)
    (h : ∀ k, k ∈ HMaps.keys S → k ∉ xs → k ∉ LMonoTy.freeVars body) :
    LMonoTy.subst (LTy.subst.go xs S) body = body := by
  apply LMonoTy.subst_no_relevant_keys
  intro k hk_fv hk_key
  have hk_S := subst_go_key_in_original S xs k hk_key
  have hk_not_xs := subst_go_key_not_in_removed S xs k hk_key
  exact h k hk_S hk_not_xs hk_fv

end LExpr

/-! ### Opening with closed values, and instantiation as renaming -/

mutual
/-- Opening bodies over `vars` with closed values gives closed types. -/
theorem LMonoTys.freeVars_openVars_eq_nil (vars : List TyIdentifier) (vals : LMonoTys)
    (hlen : vars.length = vals.length)
    (hvals : ∀ t ∈ vals, LMonoTy.freeVars t = [])
    (mtys : LMonoTys) (h : ∀ v ∈ LMonoTys.freeVars mtys, v ∈ vars) :
    LMonoTys.freeVars (LMonoTys.openVars vars vals mtys) = [] := by
  match mtys with
  | [] => simp only [LMonoTys.openVars, LMonoTys.freeVars]
  | hd :: tl =>
    have h1 : ∀ v ∈ LMonoTy.freeVars hd, v ∈ vars := fun v hv =>
      h v (by rw [LMonoTys.freeVars_of_cons, List.mem_append]; exact Or.inl hv)
    have h2 : ∀ v ∈ LMonoTys.freeVars tl, v ∈ vars := fun v hv =>
      h v (by rw [LMonoTys.freeVars_of_cons, List.mem_append]; exact Or.inr hv)
    show LMonoTys.freeVars (LMonoTy.openVars vars vals hd :: LMonoTys.openVars vars vals tl) = []
    rw [LMonoTys.freeVars_of_cons,
      LMonoTy.freeVars_openVars_eq_nil vars vals hlen hvals hd h1,
      LMonoTys.freeVars_openVars_eq_nil vars vals hlen hvals tl h2]
    rfl

/-- Opening every free variable of a type with closed values gives a closed type. -/
theorem LMonoTy.freeVars_openVars_eq_nil (vars : List TyIdentifier) (vals : LMonoTys)
    (hlen : vars.length = vals.length)
    (hvals : ∀ t ∈ vals, LMonoTy.freeVars t = [])
    (mty : LMonoTy) (h : ∀ v ∈ LMonoTy.freeVars mty, v ∈ vars) :
    LMonoTy.freeVars (LMonoTy.openVars vars vals mty) = [] := by
  match mty with
  | .ftvar x =>
    have hx : x ∈ vars := h x (by simp [LMonoTy.freeVars])
    simp only [LMonoTy.openVars]
    split
    · rename_i fst_val v hfind
      exact hvals v (zip_find_mem_snd vars vals x (fst_val, v) hfind)
    · rename_i hfind
      exfalso
      have hxm : x ∈ (List.zip vars vals).map Prod.fst := by
        rw [List.map_fst_zip (by omega)]; exact hx
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hxm
      have hnp := List.find?_eq_none.mp hfind q hq
      simp only [hqe, beq_self_eq_true] at hnp
      exact hnp trivial
  | .bitvec _ => simp only [LMonoTy.openVars, LMonoTy.freeVars]
  | .tcons name args =>
    show LMonoTys.freeVars (LMonoTys.openVars vars vals args) = []
    exact LMonoTys.freeVars_openVars_eq_nil vars vals hlen hvals args
      (by simpa only [LMonoTy.freeVars] using h)
end

/-- A substitution whose values are type variables sends every type variable to one. -/
private theorem subst_ftvar_of_values_ftvar (S : Subst)
    (hvals : ∀ x t, HMaps.find? S x = some t → ∃ y, t = LMonoTy.ftvar y)
    (x : TyIdentifier) :
    ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y := by
  rw [LMonoTy.subst_unfold]
  rcases hfind : HMaps.find? S x with _ | t
  · exact ⟨x, by simp only [hfind]⟩
  · obtain ⟨y, hy⟩ := hvals x t hfind
    exact ⟨y, by simp only [hfind, hy]⟩

/-- Instantiating type parameters renames them to type variables and keeps the context. -/
theorem LMonoTys.instantiateEnv_subst {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env')) :
    ∃ S : Subst, (∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
      mtys' = mtys.map (LMonoTy.subst S) ∧ Env'.context = Env.context := by
  unfold LMonoTys.instantiateEnv at h
  cases hinst : LMonoTys.instantiate ids mtys Env.genEnv with
  | error e => rw [hinst] at h; exact absurd h (by simp)
  | ok v =>
    obtain ⟨mtysI, genEnvI⟩ := v
    rw [hinst] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hmtys, hEnv⟩ := h
    simp only [LMonoTys.instantiate, bind, Except.bind] at hinst
    elim_err hinst with vgen hgen
    obtain ⟨freshtvs, genEnv1⟩ := vgen
    simp only [Except.ok.injEq, Prod.mk.injEq] at hinst
    obtain ⟨hmtysI, hgenEnv⟩ := hinst
    have hctx : Env'.context = Env.context := by
      rw [← hEnv]
      show genEnvI.context = Env.genEnv.context
      rw [← hgenEnv]
      exact TGenEnv.genTyVars_context ids.length Env.genEnv freshtvs genEnv1 hgen
    have hlen : freshtvs.length = ids.length := TGenEnv.genTyVars_length _ _ _ _ hgen
    refine ⟨Strata.Util.HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)],
      ?_, ?_, hctx⟩
    · refine subst_ftvar_of_values_ftvar _ ?_
      intro x t hfind
      have hsingle : HMaps.find? (Strata.Util.HMaps.ofScopes
            [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) x
          = HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) x := by
        simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?]
        cases HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) x <;> rfl
      rw [hsingle] at hfind
      have hval := HMap.find?_mem_values _ hfind
      have hin := HMap.mem_values_ofList _ t hval
      rw [List.map_snd_zip (by simp [hlen])] at hin
      obtain ⟨y, -, hy⟩ := List.mem_map.mp hin
      exact ⟨y, hy.symm⟩
    · rw [← hmtys, ← hmtysI, LMonoTys.subst_eq_map]

/-- `openVars` looks a type variable up in `vars` zipped against `vals`. -/
theorem LMonoTy.openVars_ftvar (vars : List TyIdentifier) (vals : LMonoTys) (x : TyIdentifier) :
    LMonoTy.openVars vars vals (.ftvar x)
      = match (List.zip vars vals).find? (fun p => p.1 == x) with
        | some (_, v) => v
        | none => .ftvar x := by
  unfold LMonoTy.openVars
  rfl

/-- If `vals` entries have `P` when their `vals'` counterparts do, so does opening a variable. -/
theorem LMonoTy.openVars_ftvar_of_zip (P : LMonoTy → Prop) (x : TyIdentifier) :
    ∀ (vars : List TyIdentifier) {vals vals' : LMonoTys}, vals.length = vals'.length →
      (∀ p ∈ List.zip vals vals', P p.2 → P p.1) →
      P (LMonoTy.openVars vars vals' (.ftvar x)) → P (LMonoTy.openVars vars vals (.ftvar x))
  | [], _, _, _, _, h => by
    simp only [LMonoTy.openVars_ftvar, List.zip_nil_left, List.find?_nil] at h ⊢
    exact h
  | _ :: _, [], [], _, _, h => by
    simp only [LMonoTy.openVars_ftvar, List.zip_nil_right, List.find?_nil] at h ⊢
    exact h
  | _ :: _, [], _ :: _, hlen, _, _ => absurd hlen (by simp)
  | _ :: _, _ :: _, [], hlen, _, _ => absurd hlen (by simp)
  | v :: vs, a :: as, b :: bs, hlen, hab, h => by
    rw [LMonoTy.openVars_ftvar] at h ⊢
    simp only [List.zip_cons_cons, List.find?_cons] at h ⊢
    by_cases hvx : (v == x) = true
    · simp only [hvx] at h ⊢
      exact hab (a, b) List.mem_cons_self h
    · simp only [hvx] at h ⊢
      rw [← LMonoTy.openVars_ftvar] at h ⊢
      exact LMonoTy.openVars_ftvar_of_zip P x vs
        (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
        (fun p hp => hab p (List.mem_cons_of_mem _ hp)) h

/-- `openVars` fixes a bitvector type. -/
theorem LMonoTy.openVars_bitvec (vars : List TyIdentifier) (vals : LMonoTys) (n : Nat) :
    LMonoTy.openVars vars vals (.bitvec n) = .bitvec n := by
  unfold LMonoTy.openVars
  rfl

/-- `openVars` keeps a type-constructor head and descends into the arguments. -/
theorem LMonoTy.openVars_tcons (vars : List TyIdentifier) (vals : LMonoTys) (nm : String)
    (args : LMonoTys) :
    LMonoTy.openVars vars vals (.tcons nm args)
      = .tcons nm (LMonoTys.openVars vars vals args) := by
  unfold LMonoTy.openVars
  rfl

public section

/-! ### Properties preserved by unification -/

/-- `unifyOne` and `unifyCore` preserve `P` on `Q`-constraints when `P []` holds, binding a variable
    from a `Q` constraint preserves `P`, and `Q` passes to the subproblems unification creates. -/
theorem Constraint.unify_preserves (P : Subst → Prop) (Q : Constraint → Prop)
    (hempty : P [])
    (hbind : ∀ (S : Subst) (id : TyIdentifier) (orig_lty : LMonoTy), P S →
      Q (.ftvar id, orig_lty) ∨ Q (orig_lty, .ftvar id) →
      P (HMaps.insert (Subst.apply (HMap.single id (LMonoTy.subst S orig_lty)) S) id
        (LMonoTy.subst S orig_lty)))
    (hbound : ∀ (S : Subst) (id : TyIdentifier) (orig_lty sty : LMonoTy), P S →
      Q (.ftvar id, orig_lty) ∨ Q (orig_lty, .ftvar id) → HMaps.find? S id = some sty →
      Q (sty, LMonoTy.subst S orig_lty))
    (hargs : ∀ (name1 name2 : String) (args1 args2 : LMonoTys),
      Q (.tcons name1 args1, .tcons name2 args2) → ∀ p ∈ List.zip args1 args2, Q p) :
    (∀ (c : Constraint) (S : SubstInfo) (relS : ValidSubstRelation [c] S),
      Constraint.unifyOne c S = .ok relS → P S.subst → Q c → P relS.newS.subst) ∧
    (∀ (cs : Constraints) (S : SubstInfo) (relS : ValidSubstRelation cs S),
      Constraints.unifyCore cs S = .ok relS → P S.subst → (∀ c ∈ cs, Q c) →
      P relS.newS.subst) := by
  apply Constraint.unifyOne.mutual_induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS →
      P S.subst → Q c → P relS.newS.subst)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS →
      P S.subst → (∀ c ∈ cs, Q c) → P relS.newS.subst)
  -- t1 == t2
  · intro S t1 t2 h_eq _ relS h hS _
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h; exact hS
    · exact absurd h_eq ‹_›
  -- ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _ _ _ _ relS h hS _
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; exact hS
  -- ftvar id, orig_lty; occurs check
  · intro S id orig_lty h_neq _ _ _ _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- ftvar id, orig_lty; bound to sty
  · intro S id orig_lty h_neq _ _ _ _ _ sty h_some ih_rec relS h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        elim_err h with relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]
        exact ih_rec relS' h_call hS (hbound S.subst id orig_lty sty hS (.inl hc) h_some)
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- ftvar id, orig_lty; unbound
  · intro S id orig_lty h_neq _ _ _ _ _ h_none _ _ _ _ _ _ _ relS h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        exact hbind S.subst id orig_lty hS (.inl hc)
  -- orig_lty, ftvar id; ftvar id == lty
  · intro S orig_lty id h_neq _ _ _ _ _ relS h hS _
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; exact hS
  -- orig_lty, ftvar id; occurs check
  · intro S orig_lty id h_neq _ _ _ _ _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- orig_lty, ftvar id; bound to sty
  · intro S orig_lty id h_neq _ _ _ _ _ _ sty h_some ih_rec relS h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        elim_err h with relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]
        exact ih_rec relS' h_call hS (hbound S.subst id orig_lty sty hS (.inr hc) h_some)
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- orig_lty, ftvar id; unbound
  · intro S orig_lty id h_neq _ _ _ _ _ _ h_none _ _ _ _ _ _ _ relS h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        exact hbind S.subst id orig_lty hS (.inr hc)
  -- bitvec n1 == n2
  · intro S n1 n2 h_neq h_eq_n relS h _ _
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      exact hempty
  -- bitvec n1 ≠ n2
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- tcons match
  · intro S name1 args1 name2 args2 h_neq h_match _ ih_core relS h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      elim_err h with relS' h_call
      simp only [Except.ok.injEq] at h; rw [← h]
      exact ih_core relS' h_call hS (hargs name1 name2 args1 args2 hc)
  -- tcons mismatch
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- bitvec, tcons
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- tcons, bitvec
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- unifyCore []
  · intro S relS h hS _
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h; exact hS
  -- unifyCore (c :: rest)
  · intro S c c_rest ih1 ih2 relS h hS hcs
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    elim_err h with relS_one h_one_raw
    have h_one := Except.mapError_ok_h' h_one_raw
    elim_err h with relS_rest h_rest
    simp only [Except.ok.injEq] at h; subst h
    exact ih2 relS_one relS_rest h_rest (ih1 relS_one h_one hS (hcs c List.mem_cons_self))
      (fun p hp => hcs p (List.mem_cons_of_mem c hp))

/-! ### `renameAfter` and `removeKeys` -/

/-- `renameAfter S ρ` maps a key of `S` to its value renamed by `ρ`, and other variables by `ρ`. -/
private theorem Subst.find?_renameAfter (S ρ : Subst) (x : TyIdentifier) :
    HMaps.find? (Subst.renameAfter S ρ) x =
      match HMaps.find? S x with
      | some t => some (LMonoTy.subst ρ t)
      | none => HMaps.find? ρ x := by
  rw [Subst.renameAfter, HMaps.find?_append, HMaps.find?_mapValues]
  cases HMaps.find? S x with
  | none => simp only [Option.map_none]
  | some t => simp only [Option.map_some]

/-- A free variable of `subst ρ t` is in a value of `ρ`, or free in `t` and unmapped by `ρ`. -/
theorem LMonoTy.mem_freeVars_subst (ρ : Subst) (t : LMonoTy) (x : TyIdentifier)
    (hx : x ∈ LMonoTy.freeVars (LMonoTy.subst ρ t)) :
    x ∈ Subst.freeVars ρ ∨ (x ∈ LMonoTy.freeVars t ∧ HMaps.find? ρ x = none) := by
  induction t with
  | ftvar y =>
    rw [LMonoTy.subst_unfold] at hx
    cases hfind : HMaps.find? ρ y with
    | some sty =>
      simp only [hfind] at hx
      exact Or.inl (Subst.freeVars_of_find_subset ρ hfind hx)
    | none =>
      simp only [hfind, LMonoTy.freeVars, List.mem_singleton] at hx
      subst hx
      have hmem : x ∈ LMonoTy.freeVars (.ftvar x) := by
        simp only [LMonoTy.freeVars, List.mem_singleton]
      exact Or.inr ⟨hmem, hfind⟩
  | bitvec n =>
    simp only [LMonoTy.subst_bitvec, LMonoTy.freeVars, List.not_mem_nil] at hx
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTy.freeVars] at hx
    obtain ⟨u, hu, hxu⟩ := LMonoTys.freeVars_exists hx
    obtain ⟨a, ha, hau⟩ := List.mem_map.mp hu
    subst hau
    rcases ih a ha hxu with hρ | ⟨hfa, hnone⟩
    · exact Or.inl hρ
    · exact Or.inr ⟨LMonoTys.freeVars_mem_subset ha hfa, hnone⟩

/-- After removing keys, a removed key is unbound and other lookups are unchanged. -/
private theorem Subst.find?_removeKeys (X : Subst) (R : List TyIdentifier) (x : TyIdentifier) :
    HMaps.find? (Subst.removeKeys X R) x = if x ∈ R then none else HMaps.find? X x := by
  induction R generalizing X with
  | nil => simp only [Subst.removeKeys, List.not_mem_nil, ite_false]
  | cons r rs ih =>
    rw [Subst.removeKeys, ih]
    by_cases hxs : x ∈ rs
    · simp only [hxs, ite_true, List.mem_cons, or_true]
    · by_cases hxr : x = r
      · subst hxr
        simp only [hxs, ite_false, List.mem_cons, true_or, ite_true, HMaps.find?_remove_self]
      · have hne : (x != r) = true := by simpa only [bne_iff_ne, ne_eq] using hxr
        simp only [hxs, ite_false, List.mem_cons, hxr, false_or, HMaps.find?_remove_ne X r x hne]

/-- Every key left after removing keys was a key before and was not removed. -/
theorem Subst.keys_removeKeys_subset (X : Subst) (R : List TyIdentifier) (k : TyIdentifier)
    (hk : k ∈ HMaps.keys (Subst.removeKeys X R)) : k ∈ HMaps.keys X ∧ k ∉ R := by
  constructor
  · induction R generalizing X with
    | nil => exact hk
    | cons r rs ih => exact HMaps.keys_remove_subset X r k (ih (X.remove r) hk)
  · intro hkR
    obtain ⟨v, hv⟩ := HMaps.find?_of_mem_keys _ k hk
    rw [Subst.find?_removeKeys, ite_eq_left hkR] at hv
    cases hv

/-- Every value left after removing keys was a value before. -/
theorem Subst.values_removeKeys_subset (X : Subst) (R : List TyIdentifier) (v : LMonoTy)
    (hv : v ∈ HMaps.values (Subst.removeKeys X R)) : v ∈ HMaps.values X := by
  induction R generalizing X with
  | nil => exact hv
  | cons r rs ih => exact HMaps.values_remove_subset X r v (ih (X.remove r) hv)

/-! ### Renamings that undo bindings -/

/-- If `S` binds each `r ∈ R` to a variable that `ρ` sends back to `r`, then removing `R` from
    `renameAfter S ρ` gives a substitution that acts as `S` followed by `ρ`. -/
private theorem LMonoTy.subst_ambientRenaming (S ρ : Subst) (R : List TyIdentifier)
    (hR : AmbientRenaming S ρ R) (t : LMonoTy) :
    LMonoTy.subst (Subst.removeKeys (Subst.renameAfter S ρ) R) t
      = LMonoTy.subst ρ (LMonoTy.subst S t) := by
  symm
  apply LMonoTy.subst_subst_of_pointwise
  intro x _
  by_cases hxR : x ∈ R
  · obtain ⟨g, hSx, hρg⟩ := hR x hxR
    rw [LMonoTy.subst_ftvar_of_some hSx, LMonoTy.subst_ftvar_of_some hρg]
    have hnone : HMaps.find? (Subst.removeKeys (Subst.renameAfter S ρ) R) x = none := by
      rw [Subst.find?_removeKeys, ite_eq_left hxR]
    rw [LMonoTy.subst_ftvar_of_none hnone]
  · have hfind : HMaps.find? (Subst.removeKeys (Subst.renameAfter S ρ) R) x
        = HMaps.find? (Subst.renameAfter S ρ) x := by
      rw [Subst.find?_removeKeys, ite_eq_right hxR]
    rw [LMonoTy.subst_ftvar_congr x hfind]
    cases hSx : HMaps.find? S x with
    | some t =>
      have hre : HMaps.find? (Subst.renameAfter S ρ) x = some (LMonoTy.subst ρ t) := by
        rw [Subst.find?_renameAfter, hSx]
      rw [LMonoTy.subst_ftvar_of_some hSx, LMonoTy.subst_ftvar_of_some hre]
    | none =>
      have hre : HMaps.find? (Subst.renameAfter S ρ) x = HMaps.find? ρ x := by
        rw [Subst.find?_renameAfter, hSx]
      rw [LMonoTy.subst_ftvar_of_none hSx]
      exact LMonoTy.subst_ftvar_congr x hre.symm

/-- If `S'` acts as `S` then `ρ`, then `S'` absorbs every `X` that `S` absorbs. -/
private theorem Subst.absorbs_of_subst_comp (S S' ρ X : Subst)
    (hcomp : ∀ t, LMonoTy.subst S' t = LMonoTy.subst ρ (LMonoTy.subst S t))
    (h : Subst.absorbs S X) : Subst.absorbs S' X := by
  intro a t hfind
  rw [hcomp, hcomp, h a t hfind]

/-- Removing `R` from `renameAfter S ρ` gives a well-formed substitution when `S` and `ρ` are and
    every key of `S` in a value of `ρ` is in `R`. -/
private theorem Subst.renameAfter_removeKeys_WF (S ρ : Subst) (R : List TyIdentifier)
    (hS : SubstWF S) (hρ : SubstWF ρ)
    (hdisj : ∀ x, x ∈ Subst.freeVars ρ → x ∈ HMaps.keys S → x ∈ R) :
    SubstWF (Subst.removeKeys (Subst.renameAfter S ρ) R) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at hS hρ ⊢
  intro k hk hkfv
  obtain ⟨hk, hkR⟩ := Subst.keys_removeKeys_subset _ R k hk
  have hkfv : k ∈ Subst.freeVars (Subst.renameAfter S ρ) := by
    simp only [Subst.freeVars, List.mem_flatMap] at hkfv ⊢
    obtain ⟨v, hv, hkv⟩ := hkfv
    exact ⟨v, Subst.values_removeKeys_subset _ R v hv, hkv⟩
  rw [Subst.renameAfter, HMaps.keys_append] at hk
  rw [Subst.freeVars, Subst.renameAfter, HMaps.values_append, List.flatMap_append,
    List.mem_append] at hkfv
  have hk' : k ∈ HMaps.keys S ∨ k ∈ HMaps.keys ρ := by
    rcases List.mem_append.mp hk with h | h
    · exact Or.inl ((HMaps.mem_keys_mapValues_iff _ S k).mp h)
    · exact Or.inr h
  have hfromρ : k ∈ Subst.freeVars ρ → False := fun hkρ =>
    hk'.elim (fun hkS => hkR (hdisj k hkρ hkS)) (fun hkR' => hρ k hkR' hkρ)
  rcases hkfv with hval | hval
  · obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.mp hval
    obtain ⟨v, hv, rfl⟩ := (HMaps.mem_values_mapValues _ S w).mp hw
    rcases LMonoTy.mem_freeVars_subst ρ v k hkw with hkρ | ⟨hkv, hnone⟩
    · exact hfromρ hkρ
    · rcases hk' with hkS | hkR'
      · exact hS k hkS (List.mem_flatMap.mpr ⟨v, hv, hkv⟩)
      · obtain ⟨u, hu⟩ := HMaps.find?_of_mem_keys ρ k hkR'
        rw [hnone] at hu
        cases hu
  · exact hfromρ hval

/-! ### The ambient renaming (`gen` marks generated type variables) -/

/-- An ambient key is a non-generated key of `S` that `S` binds to a generated variable. -/
theorem mem_ambientKeys {gen : TyIdentifier → Bool} {S : Subst} {k : TyIdentifier}
    (hk : k ∈ ambientKeys gen S) :
    k ∈ HMaps.keys S ∧ gen k = false ∧ ∃ g, ambientTarget S k = some g ∧ gen g = true := by
  obtain ⟨hkS, hp⟩ := List.mem_filter.mp hk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨hng, hany⟩ := hp
  cases ht : ambientTarget S k with
  | none => simp only [ht, Option.any_none, Bool.false_eq_true] at hany
  | some g =>
    simp only [ht, Option.any_some] at hany
    exact ⟨hkS, hng, g, rfl, hany⟩

/-- If `ambientTarget S k = some g`, then `S` binds `k` to `g`. -/
private theorem find?_of_ambientTarget {S : Subst} {k g : TyIdentifier}
    (h : ambientTarget S k = some g) : HMaps.find? S k = some (.ftvar g) := by
  unfold ambientTarget at h
  split at h
  · rename_i g' hf
    cases h
    exact hf
  · cases h

/-- A target's representative is an ambient key that `S` binds to the target. -/
theorem ambientRep_spec {gen : TyIdentifier → Bool} {S : Subst} {g : TyIdentifier}
    (hg : g ∈ ambientTargets gen S) :
    ambientRep S (ambientKeys gen S) g ∈ ambientKeys gen S ∧
      ambientTarget S (ambientRep S (ambientKeys gen S) g) = some g := by
  have hg' := List.mem_eraseDups.mp hg
  obtain ⟨k, hk, hkg⟩ := List.mem_filterMap.mp hg'
  cases hfind : (ambientKeys gen S).find? (fun k => ambientTarget S k == some g) with
  | none =>
    have hnot := (List.find?_eq_none.mp hfind) k hk
    simp only [hkg, beq_self_eq_true, not_true_eq_false] at hnot
  | some k0 =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp only [beq_iff_eq] at hp
    simp only [ambientRep, hfind, Option.getD_some]
    exact ⟨hmem, hp⟩

/-- Every target of the ambient renaming is a generated variable. -/
theorem ambientTargets_generated {gen : TyIdentifier → Bool} {S : Subst} {g : TyIdentifier}
    (hg : g ∈ ambientTargets gen S) : gen g = true := by
  obtain ⟨k, hk, hkg⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hg)
  obtain ⟨-, -, g', hg', hgen⟩ := mem_ambientKeys hk
  rw [hkg] at hg'
  cases hg'
  exact hgen

/-- Every key of `Subst.ofRenaming ρ` is a renamed variable of `ρ`. -/
theorem Subst.mem_keys_ofRenaming {ρ : List (TyIdentifier × TyIdentifier)} {x : TyIdentifier}
    (hx : x ∈ HMaps.keys (Subst.ofRenaming ρ)) : x ∈ ρ.map Prod.fst := by
  simp only [Subst.ofRenaming, HMaps.keys, List.append_nil] at hx
  have hmem := HMap.mem_keys_ofList _ x hx
  simpa only [List.map_map, Function.comp_def] using hmem

/-- Every free variable in a value of `Subst.ofRenaming ρ` is a target of `ρ`. -/
theorem Subst.mem_freeVars_ofRenaming {ρ : List (TyIdentifier × TyIdentifier)} {x : TyIdentifier}
    (hx : x ∈ Subst.freeVars (Subst.ofRenaming ρ)) : x ∈ ρ.map Prod.snd := by
  simp only [Subst.freeVars, Subst.ofRenaming, HMaps.values, List.append_nil,
    List.mem_flatMap] at hx
  obtain ⟨v, hv, hxv⟩ := hx
  have hv' := HMap.mem_values_ofList _ v hv
  simp only [List.map_map, Function.comp_def, List.mem_map] at hv'
  obtain ⟨q, hq, rfl⟩ := hv'
  simp only [LMonoTy.freeVars, List.mem_singleton] at hxv
  subst hxv
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- `Subst.ofRenaming ρ` is well formed when no target name of `ρ` is also a renamed variable. -/
private theorem Subst.ofRenaming_WF (ρ : List (TyIdentifier × TyIdentifier))
    (h : ∀ p ∈ ρ, p.2 ∉ ρ.map Prod.fst) : SubstWF (Subst.ofRenaming ρ) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro k hk hkfv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (Subst.mem_freeVars_ofRenaming hkfv)
  exact h q hq (Subst.mem_keys_ofRenaming hk)

/-- The ambient renaming sends each target to its representative. -/
private theorem find?_ambientRenaming {gen : TyIdentifier → Bool} {S : Subst} {g : TyIdentifier}
    (hg : g ∈ ambientTargets gen S) :
    HMaps.find? (ambientRenaming gen S) g
      = some (.ftvar (ambientRep S (ambientKeys gen S) g)) := by
  simp only [ambientRenaming, Subst.ofRenaming, List.map_map, Function.comp_def]
  rw [HMaps.find?_single_scope]
  exact HMap.find?_ofList_self_map _
    (fun g => LMonoTy.ftvar (ambientRep S (ambientKeys gen S) g)) g hg

/-- Every variable in a value of the ambient renaming is a representative. -/
private theorem mem_freeVars_ambientRenaming {gen : TyIdentifier → Bool} {S : Subst}
    {x : TyIdentifier} (hx : x ∈ Subst.freeVars (ambientRenaming gen S)) :
    x ∈ ambientReps gen S := by
  simpa only [ambientReps, List.map_map, Function.comp_def] using Subst.mem_freeVars_ofRenaming hx

/-- Each representative is bound by `S` to a target the ambient renaming sends back to it. -/
private theorem ambientRenaming_spec (gen : TyIdentifier → Bool) (S : Subst) :
    AmbientRenaming S (ambientRenaming gen S) (ambientReps gen S) := by
  intro r hr
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
  exact ⟨g, find?_of_ambientTarget (ambientRep_spec hg).2, find?_ambientRenaming hg⟩

/-- The ambient renaming is well formed. -/
private theorem ambientRenaming_WF (gen : TyIdentifier → Bool) (S : Subst) :
    SubstWF (ambientRenaming gen S) := by
  refine Subst.ofRenaming_WF _ fun p hp hmem => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  simp only [List.map_map, Function.comp_def, List.map_id'] at hmem
  have hng := (mem_ambientKeys (ambientRep_spec hg).1).2.1
  rw [ambientTargets_generated hmem] at hng
  cases hng

/-- The ambient substitution is `S` followed by a renaming. -/
private theorem ambientSubst_comp (gen : TyIdentifier → Bool) (S : Subst) :
    ∃ ρ, ∀ t, LMonoTy.subst (ambientSubst gen S) t = LMonoTy.subst ρ (LMonoTy.subst S t) := by
  unfold ambientSubst
  split
  · exact ⟨[], fun t => (LMonoTy.subst_nil _).symm⟩
  · exact ⟨ambientRenaming gen S,
      LMonoTy.subst_ambientRenaming S _ _ (ambientRenaming_spec gen S)⟩

/-- The ambient substitution absorbs every `X` that `S` absorbs. -/
theorem ambientSubst_absorbs (gen : TyIdentifier → Bool) (S X : Subst)
    (h : Subst.absorbs S X) : Subst.absorbs (ambientSubst gen S) X := by
  obtain ⟨ρ, hρ⟩ := ambientSubst_comp gen S
  exact Subst.absorbs_of_subst_comp S _ ρ X hρ h

/-- The ambient substitution of a well-formed substitution is well formed. -/
theorem ambientSubst_WF (gen : TyIdentifier → Bool) (S : Subst) (hS : SubstWF S) :
    SubstWF (ambientSubst gen S) := by
  unfold ambientSubst
  split
  · exact hS
  · exact Subst.renameAfter_removeKeys_WF S _ _ hS (ambientRenaming_WF gen S)
      (fun x hx _ => mem_freeVars_ambientRenaming hx)

end -- public section

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.LTyProps

public import Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTy
public import Strata.DL.Util.List
import all Strata.DL.Util.List
public import Strata.Util.HMaps
import all Strata.Util.HMaps
import all Strata.Util.HMap
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
## Type Substitution and Unification

Implementation of type substitution and unification for Lambda. This is similar
to Algorithm J in Hindley-Milner systems.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open Strata.Util (HMap HMaps)

public section

/-! ### Type Substitution -/

/-- Substitution mapping type variables to `LMonoTy`. -/
@[expose] abbrev SubstOne := HMap TyIdentifier LMonoTy

/--
Substitution mapping type variables to `LMonoTy`, taking scopes into
account (newest-first).
-/
@[expose] abbrev Subst := HMaps TyIdentifier LMonoTy
@[expose] abbrev Subst.empty : Subst := []

instance : ToFormat Subst where
  format s := format (s.map (fun m => m.toList.mergeSort (fun a b => a.1 ≤ b.1)))

/--
Check if `Subst` contains only empty scopes.
-/
def Subst.hasEmptyScopes (S : Subst) : Bool :=
  S.all (fun s => s.isEmpty)

@[simp]
theorem Subst.hasEmptyScopes_empty : Subst.hasEmptyScopes Subst.empty := by
  simp [Subst.hasEmptyScopes, Subst.empty]

/--
The free variables in a substitution `S` are the union of the free variables in
every type in `S`.

Note that we do not deduplicate the resulting list.
-/
def Subst.freeVars (S : Subst) : List TyIdentifier :=
  S.values.flatMap LMonoTy.freeVars

theorem Subst.freeVars_of_find_subset (S : Subst) (hi : HMaps.find? S i = some sty) :
    LMonoTy.freeVars sty ⊆ Subst.freeVars S := by
  have h_val := HMaps.find?_mem_values S hi
  simp only [Subst.freeVars]
  intro x hx
  exact List.mem_flatMap.mpr ⟨sty, h_val, hx⟩

/--
A substitution map `S` is well-formed if no key appears in the free type
variables of the values.
-/
def SubstWF (S : Subst) : Bool :=
  S.keys.all (fun k => k ∉ Subst.freeVars S)

@[simp]
theorem SubstWF_of_empty : SubstWF Subst.empty := by
  simp [SubstWF, HMaps.keys]

/-- Pushing an empty scope preserves well-formedness: the new scope adds no keys
    and no values, so both `keys` and `freeVars` are unchanged. -/
theorem SubstWF_of_pushEmptyScope (S : Subst) (h : SubstWF S) :
    SubstWF (S.push (HMap.empty : SubstOne)) := by
  simp only [SubstWF, Subst.freeVars, HMaps.push, HMaps.keys, HMaps.values,
    HMap.keys_empty, HMap.values_empty, List.nil_append] at h ⊢
  exact h

/-- Popping a scope preserves well-formedness: removing the newest scope only
    removes keys and values, so no key can newly collide. -/
theorem SubstWF_of_popScope (S : Subst) (h : SubstWF S) :
    SubstWF S.pop := by
  cases S with
  | nil => simp [HMaps.pop]
  | cons m rest =>
    simp only [SubstWF, Subst.freeVars, HMaps.pop, HMaps.keys, HMaps.values,
      List.all_eq_true, List.mem_append, List.flatMap_append, decide_eq_true_eq] at h ⊢
    intro k hk hmem
    exact h k (Or.inr hk) (Or.inr hmem)

/-- The single-scope substitution `[single id ty]` and its key/value/freeVars. -/
@[expose] def Subst.singleton (tv : TyIdentifier) (ty : LMonoTy) : Subst :=
  [HMap.single tv ty]

theorem Subst.find?_singleton_self
    (tv : TyIdentifier) (ty : LMonoTy) :
    HMaps.find? (Subst.singleton tv ty) tv = some ty := by
  simp [Subst.singleton, HMaps.find?, HMap.find?_single_self]

/-- Free variables of a singleton substitution are contained in `ty`'s. -/
theorem Subst.freeVars_singleton_subset
    (tv : TyIdentifier) (ty : LMonoTy) :
    Subst.freeVars (Subst.singleton tv ty) ⊆ ty.freeVars := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap] at hx
  obtain ⟨v, hv, hxv⟩ := hx
  -- v is a value of the singleton scope, so v = ty
  have hv' : v ∈ (HMap.single tv ty).values := by
    simpa [Subst.singleton, HMaps.values] using hv
  rw [(HMap.mem_values_single_iff tv ty v).mp hv'] at hxv
  exact hxv

/-- Every free variable of `ty` is a free variable of the singleton substitution. -/
theorem Subst.freeVars_singleton_superset
    (tv : TyIdentifier) (ty : LMonoTy) :
    ty.freeVars ⊆ Subst.freeVars (Subst.singleton tv ty) := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap]
  refine ⟨ty, ?_, hx⟩
  simpa [Subst.singleton, HMaps.values] using (HMap.mem_values_single_iff tv ty ty).mpr rfl

/-- `SubstWF` for the single-scope substitution `[single tv ty]` when `tv` is not
    free in `ty`. -/
theorem SubstWF.single_subst
    (tv : TyIdentifier) (ty : LMonoTy) (h : tv ∉ ty.freeVars) :
    SubstWF (Subst.singleton tv ty) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro k hk
  have hk_id : k = tv := by
    have : k ∈ (HMap.single tv ty).keys := by
      simpa [Subst.singleton, HMaps.keys] using hk
    exact (HMap.mem_keys_single_iff tv k ty).mp this
  rw [hk_id]
  exact fun hmem => h (Subst.freeVars_singleton_subset tv ty hmem)

/-- If `xty` is free in `remove S id`, it is free in `S`. -/
theorem Subst.mem_freeVars_of_mem_freeVars_remove
    (S : Subst) (id : TyIdentifier)
    (h : xty ∈ Subst.freeVars (HMaps.remove S id)) :
    xty ∈ Subst.freeVars S := by
  simp only [Subst.freeVars, List.mem_flatMap] at h ⊢
  obtain ⟨aty, h1, h2⟩ := h
  exact ⟨aty, HMaps.values_remove_subset S id aty h1, h2⟩

/-- Removing a key preserves well-formedness. Discharges the map-shaped obligation
    inside `resolveAux`'s `app` case. -/
theorem SubstWF_of_remove
    (id : TyIdentifier) (h : SubstWF S) :
    SubstWF (HMaps.remove S id) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h ⊢
  intro xty h_xty_in_keys h_xty_in_fvs
  have h_xty_in_s_keys := HMaps.keys_remove_subset S id xty h_xty_in_keys
  have h_xty_not_in_fvs := h xty h_xty_in_s_keys
  exact h_xty_not_in_fvs (Subst.mem_freeVars_of_mem_freeVars_remove S id h_xty_in_fvs)

/--
A type substitution, along with a proof that it is well-formed.
-/
structure SubstInfo where
  subst : Subst
  isWF : SubstWF subst
  deriving Repr

def SubstInfo.empty : SubstInfo :=
  { subst := Subst.empty,
    isWF := SubstWF_of_empty }

instance : Inhabited SubstInfo where
  default := SubstInfo.empty

mutual
/--
Core recursion for substitution, WITHOUT the `hasEmptyScopes` short-circuit.
Callers should go through `LMonoTy.subst`, which performs the check once at the
top level. Proofs use `LMonoTy.subst_unfold`, which hides the distinction.
-/
@[expose] def LMonoTy.substCore (S : Subst) (mty : LMonoTy) : LMonoTy :=
  match mty with
  | .ftvar x => match S.find? x with
                | some sty => sty | none => mty
  | .bitvec n => .bitvec n
  | .tcons name ltys => .tcons name (LMonoTys.substCore S ltys)
@[expose] def LMonoTys.substCore (S : Subst) (mtys : LMonoTys) : LMonoTys :=
  match mtys with
  | [] => []
  | ty :: rest => LMonoTy.substCore S ty :: LMonoTys.substCore S rest
end

/--
Apply substitution `S` to monotype `mty`.
-/
@[expose] def LMonoTy.subst (S : Subst) (mty : LMonoTy) : LMonoTy :=
  if Subst.hasEmptyScopes S then mty else LMonoTy.substCore S mty

/--
Apply substitution `S` to monotypes `mtys`.
-/
@[expose] def LMonoTys.subst (S : Subst) (mtys : LMonoTys) : LMonoTys :=
  if Subst.hasEmptyScopes S then mtys else LMonoTys.substCore S mtys

/-- If all scopes are empty, `find?` is always `none`. -/
theorem Subst.find?_none_of_hasEmptyScopes
    (h : Subst.hasEmptyScopes S) (x : TyIdentifier) : HMaps.find? S x = none := by
  induction S with
  | nil => rfl
  | cons m rest ih =>
    simp only [Subst.hasEmptyScopes, List.all_cons, Bool.and_eq_true] at h
    simp only [HMaps.find?, HMap.find?_of_isEmpty m x h.1]
    exact ih (by simp only [Subst.hasEmptyScopes]; exact h.2)

theorem LMonoTys.substCore_eq_map (S : Subst) (mtys : LMonoTys) :
    LMonoTys.substCore S mtys = mtys.map (LMonoTy.substCore S) := by
  induction mtys with
  | nil => rfl
  | cons hd tl ih => simp only [LMonoTys.substCore, List.map, ih]

/-- When `S` has only empty scopes, `subst` is the identity. -/
theorem LMonoTy.subst_of_hasEmptyScopes
    (h : Subst.hasEmptyScopes S) (ty : LMonoTy) :
    LMonoTy.subst S ty = ty := by
  simp only [LMonoTy.subst, h, if_true]

/-- `subst` reduces to `substCore` when `S` has a non-empty scope. -/
theorem LMonoTy.subst_eq_substCore (S : Subst) (ty : LMonoTy)
    (h : Subst.hasEmptyScopes S = false) :
    LMonoTy.subst S ty = LMonoTy.substCore S ty := by
  simp only [LMonoTy.subst, h, Bool.false_eq_true, if_false]

/-- `subst` distributes into `tcons` (short-circuit handled). -/
theorem LMonoTy.subst_tcons (S : Subst) (name : String) (args : LMonoTys) :
    LMonoTy.subst S (.tcons name args) = .tcons name (LMonoTys.subst S args) := by
  simp only [LMonoTy.subst, LMonoTys.subst]
  split
  · rfl
  · simp only [LMonoTy.substCore]

theorem LMonoTys.subst_nil (S : Subst) : LMonoTys.subst S [] = [] := by
  simp only [LMonoTys.subst]; split <;> rfl

theorem LMonoTy.subst_bitvec (S : Subst) (n : Nat) :
    LMonoTy.subst S (.bitvec n) = .bitvec n := by
  simp only [LMonoTy.subst]; split <;> rfl

/-- `subst` as an explicit `map` over `tcons` args (short-circuit handled). -/
theorem LMonoTys.subst_eq_map (S : Subst) (mtys : LMonoTys) :
    LMonoTys.subst S mtys = mtys.map (LMonoTy.subst S) := by
  simp only [LMonoTys.subst]
  split
  · rename_i h
    have h_map : mtys.map (LMonoTy.subst S) = mtys.map id :=
      List.map_congr_left (fun a _ => LMonoTy.subst_of_hasEmptyScopes h a)
    rw [h_map, List.map_id]
  · rename_i h
    have h' : Subst.hasEmptyScopes S = false := by
      simpa using h
    rw [LMonoTys.substCore_eq_map]
    exact List.map_congr_left (fun a _ => (LMonoTy.subst_eq_substCore S a h').symm)

/-- Unfold `subst` one level, INCLUDING the short-circuit: when a variable is
    absent the ftvar branch returns the variable, exactly as if there were no
    short-circuit. This is the only equation downstream proofs use. -/
theorem LMonoTy.subst_unfold (S : Subst) (ty : LMonoTy) :
    LMonoTy.subst S ty = match ty with
      | .ftvar x => match S.find? x with | some sty => sty | none => .ftvar x
      | .bitvec n => .bitvec n
      | .tcons name args => .tcons name (args.map (LMonoTy.subst S)) := by
  cases ty with
  | ftvar x =>
    by_cases h : Subst.hasEmptyScopes S
    · simp only [LMonoTy.subst_of_hasEmptyScopes h, Subst.find?_none_of_hasEmptyScopes h x]
    · simp only [Bool.not_eq_true] at h
      rw [LMonoTy.subst_eq_substCore S _ h, LMonoTy.substCore]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args => rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]

/-- `subst` distributes over `mkArrow'`. -/
theorem subst_mkArrow' (S : Subst) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.subst S (LMonoTy.mkArrow' ret ins) =
    LMonoTy.mkArrow' (LMonoTy.subst S ret) (ins.map (LMonoTy.subst S)) := by
  induction ins with
  | nil => rfl
  | cons t ts ih =>
    simp only [LMonoTy.mkArrow'_cons, List.map]
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.arrow, List.map]
    rw [ih]

/-! ## Type substitution agreement lemmas

These lemmas establish that if two substitutions produce the same result on a
type, they must agree on all free variables of that type — and conversely, if
they agree on all free variables, they produce the same result. -/

/-- If two substitutions produce the same result on a type `ty`, then they
agree on every free variable of `ty` (in the sense of producing the same
substitution result on that variable). -/
theorem subst_eq_implies_agree_on_freeVars
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty)
    (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars ty)
    : LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v) := by
  induction ty with
  | ftvar x =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv; exact h
  | bitvec n =>
    simp [LMonoTy.freeVars] at hv
  | tcons name args ih =>
    simp only [LMonoTy.subst_unfold] at h
    simp only [LMonoTy.freeVars] at hv
    have h_args := LMonoTy.tcons.inj h |>.2
    -- v ∈ freeVars of some ty ∈ args; find it and apply IH
    have h_map_eq := List.map_eq_map_iff.mp h_args
    have ⟨ty, ht, hv_ty⟩ := LMonoTys.freeVars_exists hv
    exact ih ty ht (h_map_eq ty ht) hv_ty

/-- If two substitutions agree on all free variables of `ty` (in the sense of
producing the same substitution result), then they produce the same result
on `ty`. -/
theorem agree_on_freeVars_implies_subst_eq
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : ∀ v, v ∈ LMonoTy.freeVars ty →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v))
    : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty := by
  induction ty with
  | ftvar v =>
    exact h v (by simp [LMonoTy.freeVars])
  | bitvec n =>
    simp only [LMonoTy.subst_unfold]
  | tcons name args ih =>
    simp only [LMonoTy.subst_unfold]
    congr 1
    simp only [LMonoTy.freeVars] at h
    exact List.map_eq_map_iff.mpr fun ty ht =>
      ih ty ht fun v hv => h v (LMonoTys.freeVars_mem_subset ht hv)

/-- List version: if two substitutions agree on all free variables of every
type in a list, then mapping `subst` over the list produces the same result. -/
theorem agree_on_freeVars_implies_subst_eq_list
    {S₁ S₂ : Subst}
    {tys : List LMonoTy}
    (h : ∀ v, v ∈ LMonoTys.freeVars tys →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v))
    : tys.map (LMonoTy.subst S₁) = tys.map (LMonoTy.subst S₂) :=
  List.map_eq_map_iff.mpr fun _ ht =>
    agree_on_freeVars_implies_subst_eq fun v hv =>
      h v (LMonoTys.freeVars_mem_subset ht hv)

/-- If a key `id` of a well-formed `S` appears free in `subst S ty`, we derive a
    contradiction. Stated as the membership form used by the mutual proof. -/
theorem Subst.key_not_free_of_find
    (h : SubstWF S) (id : TyIdentifier) (hid : id ∈ S.keys) (x : TyIdentifier) :
    id ∉ LMonoTy.freeVars (LMonoTy.subst S (.ftvar x)) := by
  rw [LMonoTy.subst_unfold]
  cases hfind : S.find? x with
  | some sty =>
    simp only [hfind]
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h
    exact fun hmem => h id hid (Subst.freeVars_of_find_subset S hfind hmem)
  | none =>
    simp only [hfind, LMonoTy.freeVars, List.mem_singleton]
    intro h_id_eq; subst h_id_eq
    obtain ⟨v, hv⟩ := HMaps.find?_of_mem_keys S id hid
    rw [hv] at hfind; simp at hfind

mutual
/--
No key (i.e., type identifier) in a well-formed substitution `S` can appear as a
free variable in a substituted type (i.e., in `LMonoTy.subst S ty`).
-/
theorem LMonoTy.subst_keys_not_in_substituted_type
    (h : SubstWF S) (ty : LMonoTy) :
    S.keys.all (fun k => k ∉ LMonoTy.freeVars (LMonoTy.subst S ty)) := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro id hid
  match ty with
  | .ftvar x => exact Subst.key_not_free_of_find h id hid x
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp [LMonoTy.freeVars]
  | .tcons name args =>
    rw [LMonoTy.subst_tcons, LMonoTy.freeVars]
    have hlist := LMonoTys.subst_keys_not_in_substituted_type h args
    simp only [List.all_eq_true, decide_eq_true_eq] at hlist
    exact hlist id hid

/-- List version: no key in a well-formed `S` is free in `LMonoTys.subst S mtys`. -/
theorem LMonoTys.subst_keys_not_in_substituted_type
    (h : SubstWF S) (mtys : LMonoTys) :
    S.keys.all (fun k => k ∉ LMonoTys.freeVars (LMonoTys.subst S mtys)) := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro id hid
  rw [LMonoTys.subst_eq_map]
  match mtys with
  | [] => simp [LMonoTys.freeVars]
  | ty :: rest =>
    simp only [List.map_cons, LMonoTys.freeVars, List.mem_append, not_or]
    have h_hd := LMonoTy.subst_keys_not_in_substituted_type h ty
    have h_tl := LMonoTys.subst_keys_not_in_substituted_type h rest
    rw [LMonoTys.subst_eq_map] at h_tl
    simp only [List.all_eq_true, decide_eq_true_eq] at h_hd h_tl
    exact ⟨h_hd id hid, h_tl id hid⟩
end

mutual
/--
The free variables in a type `mty` after the application of a substitution `S`
are a subset of the free variables in `mty` and the free variables in `S`.
-/
theorem LMonoTy.freeVars_of_subst_subset (S : Subst) (mty : LMonoTy) :
    LMonoTy.freeVars (LMonoTy.subst S mty) ⊆
    LMonoTy.freeVars mty ++ Subst.freeVars S := by
  match mty with
  | .ftvar x =>
    rw [LMonoTy.subst_unfold]
    cases hfind : S.find? x with
    | some sty =>
      simp only [hfind]
      intro v hv
      exact List.mem_append_right _ (Subst.freeVars_of_find_subset S hfind hv)
    | none => simp only [hfind, LMonoTy.freeVars]; intro v hv; exact List.mem_append_left _ hv
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp [LMonoTy.freeVars]
  | .tcons name args =>
    rw [LMonoTy.subst_tcons, LMonoTy.freeVars, LMonoTy.freeVars]
    exact LMonoTys.freeVars_of_subst_subset S args

theorem LMonoTys.freeVars_of_subst_subset (S : Subst) (mtys : LMonoTys) :
    LMonoTys.freeVars (LMonoTys.subst S mtys) ⊆
    LMonoTys.freeVars mtys ++ Subst.freeVars S := by
  rw [LMonoTys.subst_eq_map]
  match mtys with
  | [] => simp [LMonoTys.freeVars]
  | ty :: rest =>
    simp only [List.map_cons, LMonoTys.freeVars]
    have h_hd := LMonoTy.freeVars_of_subst_subset S ty
    have h_tl := LMonoTys.freeVars_of_subst_subset S rest
    rw [LMonoTys.subst_eq_map] at h_tl
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · rcases List.mem_append.mp (h_hd h) with h' | h'
      · exact List.mem_append_left _ (List.mem_append_left _ h')
      · exact List.mem_append_right _ h'
    · rcases List.mem_append.mp (h_tl h) with h' | h'
      · exact List.mem_append_left _ (List.mem_append_right _ h')
      · exact List.mem_append_right _ h'
end

/--
Apply the `new` substitution to the `old` one.
-/
def Subst.apply (new : SubstOne) (old : Subst) : Subst :=
  old.mapValues (LMonoTy.subst [new])

/-- `apply` preserves the key set (as membership). -/
theorem Subst.mem_keys_apply_iff
    (new : SubstOne) (old : Subst) (k : TyIdentifier) :
    k ∈ (Subst.apply new old).keys ↔ k ∈ old.keys :=
  HMaps.mem_keys_mapValues_iff _ old k

/-- `find?` after `apply` maps the value through `subst [new]`. -/
theorem Subst.find?_apply
    (new : SubstOne) (S : Subst) (x : TyIdentifier) :
    HMaps.find? (Subst.apply new S) x = (HMaps.find? S x).map (LMonoTy.subst [new]) :=
  HMaps.find?_mapValues _ S x

/--
No key in a well-formed substitution `newS` appears in the free variables of a
composed substitution `(Subst.apply newS oldS)`. Note that there are no
restrictions on `oldS` here.
-/
theorem Subst.keys_not_in_apply
    (newS : SubstOne) (oldS : Subst) (h : SubstWF [newS]) :
    (HMaps.keys [newS]).all (fun k => k ∉ Subst.freeVars (Subst.apply newS oldS)) := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro k hk hmem
  -- Any x ∈ freeVars (apply newS oldS) lies in freeVars (subst [newS] v) for some
  -- value v of oldS. But k is a key of [newS], and subst_keys_not_in_substituted_type
  -- says no key of [newS] is free in any subst [newS] _.
  simp only [Subst.freeVars, List.mem_flatMap] at hmem
  obtain ⟨mty, h_mty, h_fv⟩ := hmem
  rw [Subst.apply, HMaps.mem_values_mapValues] at h_mty
  obtain ⟨v, _hv, rfl⟩ := h_mty
  have h_keys := LMonoTy.subst_keys_not_in_substituted_type h v
  simp only [List.all_eq_true, decide_eq_true_eq] at h_keys
  exact h_keys k hk h_fv

/--
For every type `mty` among the values of `apply new S`, its free variables are a
subset of those in `[new]` and `S`.
-/
theorem Subst.freeVars_of_apply_subset
    (new : SubstOne) (S : Subst) (mty : LMonoTy)
    (h : mty ∈ HMaps.values (Subst.apply new S)) :
    LMonoTy.freeVars mty ⊆ Subst.freeVars [new] ++ Subst.freeVars S := by
  rw [Subst.apply, HMaps.mem_values_mapValues] at h
  obtain ⟨v, hv, rfl⟩ := h
  have h_sub := LMonoTy.freeVars_of_subst_subset [new] v
  intro x hx
  rcases List.mem_append.mp (h_sub hx) with h1 | h1
  · refine List.mem_append_right _ ?_
    simp only [Subst.freeVars]
    exact List.mem_flatMap.mpr ⟨v, hv, h1⟩
  · exact List.mem_append_left _ h1

/--
The free variables of `apply new S` are a subset of those in `[new]` and `S`.
-/
theorem Subst.freeVars_of_apply_subset_alt
    (new : SubstOne) (S : Subst) :
    Subst.freeVars (Subst.apply new S) ⊆
    Subst.freeVars [new] ++ Subst.freeVars S := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap] at hx
  obtain ⟨mty, h_mty, h_fv⟩ := hx
  exact Subst.freeVars_of_apply_subset new S mty h_mty h_fv

/-- After applying `S` to `ty` and composing, the result is well-formed. -/
theorem SubstWF.apply_one_substituted_type
    (S : Subst) (hS : SubstWF S) (id : TyIdentifier) (ty : LMonoTy) :
    SubstWF (Subst.apply (HMap.single id (LMonoTy.subst S ty)) S) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro k hk hmem
  -- k is a key of (apply _ S), so k is a key of S (apply preserves keys)
  have hk_S : k ∈ S.keys := (Subst.mem_keys_apply_iff _ S k).mp hk
  -- and k ∈ freeVars (apply ...) ⊆ freeVars [single ...] ++ freeVars S
  have h_sub := Subst.freeVars_of_apply_subset_alt (HMap.single id (LMonoTy.subst S ty)) S hmem
  rcases List.mem_append.mp h_sub with h1 | h1
  · -- k ∈ freeVars [single id (subst S ty)] ⊆ freeVars (subst S ty)
    have h_single := Subst.freeVars_singleton_subset id (LMonoTy.subst S ty)
    simp only [Subst.singleton] at h_single
    have h_key := LMonoTy.subst_keys_not_in_substituted_type hS ty
    simp only [List.all_eq_true, decide_eq_true_eq] at h_key
    exact h_key k hk_S (h_single h1)
  · -- k ∈ freeVars S, but k is a key of S and S is WF
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at hS
    exact hS k hk_S h1

/-! ### Type Unification -/

/-- Free variables after `insert` are bounded by the old ones plus `ty`'s. -/
theorem Subst.freeVars_of_insert
    (S : Subst) (id : TyIdentifier) (ty : LMonoTy) :
    Subst.freeVars (HMaps.insert S id ty) ⊆ Subst.freeVars S ++ LMonoTy.freeVars ty := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap] at hx
  obtain ⟨v, hv, hxv⟩ := hx
  -- v ∈ values (insert S id ty) ⊆ ty :: values S
  have h_val := HMaps.insert_values_subset S id ty v hv
  rcases List.mem_cons.mp h_val with h1 | h1
  · subst h1; exact List.mem_append_right _ hxv
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨v, h1, hxv⟩)

/-- Well-formedness of an `insert` given: `i` not free in `S`'s values, no key of
    `S` free in `ty`, the singleton `i ↦ ty` WF, and `S` WF. -/
theorem SubstWF_mk_insert
    (S : Subst) (i : TyIdentifier) (ty : LMonoTy)
    (h_i_not_in_S_values : i ∉ Subst.freeVars S)
    (h_keys_not_in_ty : S.keys.all (fun k => k ∉ ty.freeVars))
    (h_s_WF : SubstWF (Subst.singleton i ty))
    (h_S_WF : SubstWF S) :
    SubstWF (HMaps.insert S i ty) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro x hx_keys hx_fv
  have h_keys := HMaps.insert_keys_subset S i ty x hx_keys
  have h_fv := Subst.freeVars_of_insert S i ty hx_fv
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_S_WF
  simp only [List.all_eq_true, decide_eq_true_eq] at h_keys_not_in_ty
  rcases List.mem_cons.mp h_keys with hx_i | hx_S
  · rw [hx_i] at h_fv
    rcases List.mem_append.mp h_fv with h | h
    · exact h_i_not_in_S_values h
    · simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_s_WF
      exact h_s_WF i (by simp [Subst.singleton, HMaps.keys, HMap.mem_keys_single_iff])
        (Subst.freeVars_singleton_superset i ty h)
  · rcases List.mem_append.mp h_fv with h | h
    · exact h_S_WF x hx_S h
    · exact h_keys_not_in_ty x hx_S h

/-- The full composition step: inserting `(id, ty)` into `apply [single id ty] S`
    is well-formed, given `id` not free in `ty` and `S` WF. This is exactly what
    the unifier's fresh-binding branch produces. -/
theorem SubstWF.cons_of_subst_apply
    (S : Subst) (hS : SubstWF S) (id : TyIdentifier) (ty newty : LMonoTy)
    (h_newty : newty = LMonoTy.subst S ty)
    (h_id_not_in_newty : id ∉ newty.freeVars) :
    SubstWF (HMaps.insert (Subst.apply (HMap.single id newty) S) id newty) := by
  have h_apply_WF : SubstWF (Subst.apply (HMap.single id newty) S) := by
    rw [h_newty]; exact SubstWF.apply_one_substituted_type S hS id ty
  -- id not free in (apply [single id newty] S)'s values
  have h_id_not_free : id ∉ Subst.freeVars (Subst.apply (HMap.single id newty) S) := by
    have := Subst.keys_not_in_apply (HMap.single id newty) S
      (SubstWF.single_subst id newty h_id_not_in_newty)
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this id (by simp [HMaps.keys, HMap.mem_keys_single_iff])
  -- every key of (apply ...) not free in newty: keys are S's keys, and no key of S free in subst S ty
  have h_keys_not_in_newty :
      (Subst.apply (HMap.single id newty) S).keys.all (fun k => k ∉ newty.freeVars) := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro k hk
    have hk_S : k ∈ S.keys := (Subst.mem_keys_apply_iff _ S k).mp hk
    rw [h_newty]
    have h_key := LMonoTy.subst_keys_not_in_substituted_type hS ty
    simp only [List.all_eq_true, decide_eq_true_eq] at h_key
    exact h_key k hk_S
  exact SubstWF_mk_insert (Subst.apply (HMap.single id newty) S) id newty
    h_id_not_free h_keys_not_in_newty
    (SubstWF.single_subst id newty h_id_not_in_newty) h_apply_WF

/--
Apply substitution `S` to the free type variables in `ty`.
-/
def LTy.subst (S : Subst) (ty : LTy) : LTy :=
  match ty with
  | .forAll xs ty =>
    let S' := go xs S
    .forAll xs (LMonoTy.subst S' ty)
  where go xs S :=
  match xs with
  | [] => S | x :: rest => go rest (S.remove x)

/--
Open `ty` by instantiating the bound type variable `x` with `xty`.
Note: there is function LTy.close in LTy.lean. LTy.open is located in
this file because it uses LMonoTy.subst.
-/
def LTy.open (x : TyIdentifier) (xty : LMonoTy) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty =>
    if x ∈ vars then
      .forAll (vars.removeAll [x]) (LMonoTy.subst (Subst.singleton x xty) lty)
    else
      ty

/--
Open `ty` by instantiating all its bound variables with `tys`, giving the
`LMonoTy` that results. `tys` should have length equal to the number of bound
variables in `ty`.
-/
def LTy.openFull (ty: LTy) (tys: List LMonoTy) : LMonoTy :=
  LMonoTy.subst (Strata.Util.HMaps.ofScopes [(List.zip (LTy.boundVars ty) tys)])
    (LTy.toMonoTypeUnsafe ty)

---------------------------------------------------------------------

/-! ### Substitution Properties -/

/-- Substitution on `LMonoTy.bool` is the identity (ground type). -/
theorem LMonoTy.subst_bool (S : Subst) :
    LMonoTy.subst S LMonoTy.bool = LMonoTy.bool := by
  simp [LMonoTy.bool, LMonoTy.subst_unfold]

/-- `subst` over the single empty scope is the identity, via `subst_unfold`. -/
theorem LMonoTy.subst_single_empty (ann : LMonoTy) :
    LMonoTy.subst [HMap.empty] ann = ann := by
  induction ann with
  | ftvar x =>
    rw [LMonoTy.subst_unfold]
    simp only [HMaps.find?_single_scope, HMap.find?_empty]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    congr 1
    rw [List.map_congr_left ih]; exact List.map_id_fun' ▸ rfl

/-- `subst` distributes over a two-argument `tcons` (e.g. `arrow`). -/
theorem LMonoTy.subst_tcons_pair (S : Subst) (name : String) (a b : LMonoTy) :
    LMonoTy.subst S (.tcons name [a, b]) = .tcons name [LMonoTy.subst S a, LMonoTy.subst S b] := by
  rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]; simp

/-- If no key of `S` appears in `freeVars mty`, then `subst S mty = mty`. -/
theorem LMonoTy.subst_no_relevant_keys (S : Subst) (mty : LMonoTy)
    (h : ∀ x, x ∈ LMonoTy.freeVars mty → x ∉ HMaps.keys S) :
    LMonoTy.subst S mty = mty := by
  induction mty with
  | ftvar x =>
    rw [LMonoTy.subst_unfold]
    simp only [HMaps.not_mem_keys_find?_none S x (h x (by simp [LMonoTy.freeVars]))]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    congr 1
    have h_map : args.map (LMonoTy.subst S) = args.map id :=
      List.map_congr_left (fun a ha => ih a ha (fun x hx =>
        h x (by simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha hx)))
    rw [h_map, List.map_id]

/-- Two `Subst` that agree on `find?` at every key produce the same substitution
    result. Since `subst` reads `S` only through `find?`, find?-equivalent
    substitutions are interchangeable. -/
theorem LMonoTy.subst_find?_congr (S1 S2 : Subst) (mty : LMonoTy)
    (h : ∀ k, HMaps.find? S1 k = HMaps.find? S2 k) :
    LMonoTy.subst S1 mty = LMonoTy.subst S2 mty := by
  induction mty with
  | ftvar x => rw [LMonoTy.subst_unfold, LMonoTy.subst_unfold]; simp only [h x]
  | bitvec n => rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map]
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha)

/-- Extensionality: substitutions agreeing on all free variables of `mty`
    produce the same result. -/
theorem LMonoTy.subst_ext (S1 S2 : Subst) (mty : LMonoTy)
    (h : ∀ x, x ∈ LMonoTy.freeVars mty → HMaps.find? S1 x = HMaps.find? S2 x) :
    LMonoTy.subst S1 mty = LMonoTy.subst S2 mty := by
  induction mty with
  | ftvar x =>
    rw [LMonoTy.subst_unfold, LMonoTy.subst_unfold]
    simp only [h x (by simp [LMonoTy.freeVars])]
  | bitvec n => rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map]
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha (fun x hx =>
      h x (by simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha hx)))

/--
If `t` is a value in a well-formed substitution `S` (i.e., `HMaps.find? S a = some t`),
then `subst S t = t`. This is because `SubstWF` guarantees no key of `S` appears
in the free variables of any value in `S`.
-/
theorem LMonoTy.subst_idempotent_value
    (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : HMaps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S t = t := by
  apply LMonoTy.subst_no_relevant_keys
  intro x hx
  have h_x_in_fvs : x ∈ Subst.freeVars S := Subst.freeVars_of_find_subset S h_find hx
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_wf
  intro h_x_key
  exact h_wf x h_x_key h_x_in_fvs

/--
If no key of a substitution `S` appears free in `ty`, then applying `S` to
`ty` leaves it unchanged. This is the key lemma for proving idempotence.
-/
theorem LMonoTy.subst_no_key_free (S : Subst) (ty : LMonoTy)
    (h : S.keys.all (fun k => k ∉ ty.freeVars)) :
    LMonoTy.subst S ty = ty := by
  apply LMonoTy.subst_no_relevant_keys
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun x hx h_key => h x h_key hx

/--
Well-formed substitutions are idempotent: applying the substitution twice
gives the same result as applying it once. Follows from `subst_no_key_free`
and `subst_keys_not_in_substituted_type`.
-/
theorem LMonoTy.subst_idempotent
    (S : Subst) (hWF : SubstWF S) (ty : LMonoTy) :
    LMonoTy.subst S (LMonoTy.subst S ty) = LMonoTy.subst S ty :=
  LMonoTy.subst_no_key_free S (LMonoTy.subst S ty)
    (LMonoTy.subst_keys_not_in_substituted_type hWF ty)

---------------------------------------------------------------------

/-! ### Type Constraints -/

/--
A type constraint `(ty1, ty2)` that records that `ty1` and `ty2` must
have a common substitution instance.
-/
@[expose] abbrev Constraint := (LMonoTy × LMonoTy)
/--
A list of type constraints. These should really be viewed as a set.
-/
@[expose] abbrev Constraints := List Constraint

/--
Get the free type variables in the type constraint `c`.
-/
def Constraint.freeVars (c : Constraint) : List TyIdentifier :=
  let (t1, t2) := c
  LMonoTy.freeVars t1 ++ LMonoTy.freeVars t2

/--
Get the free type variables in type constraints `cs`.
-/
def Constraints.freeVars (cs : Constraints) : List TyIdentifier :=
  match cs with
  | [] => []
  | c :: c_rest =>
    c.freeVars ++ Constraints.freeVars c_rest

theorem Constraints.freeVars_length_cons :
    (freeVars cs).length < (freeVars (c :: cs)).length ∨
    (freeVars cs).length = (freeVars (c :: cs)).length := by
  simp [freeVars, Constraint.freeVars]
  omega

theorem Constraints.freeVars_single_constraint_comm_subset :
    Constraints.freeVars [(t1, t2)] ⊆ Constraints.freeVars [(t2, t1)] := by
  simp [Constraints.freeVars, Constraint.freeVars]

@[simp]
theorem Constraints.freeVars_of_cons_zip :
    Constraints.freeVars ((a :: as).zip (b :: bs)) =
    LMonoTy.freeVars a ++ LMonoTy.freeVars b ++ Constraints.freeVars (as.zip bs) := by
  simp [Constraints.freeVars, Constraint.freeVars]

theorem Constraints.freeVars_of_zip_subset :
    (Constraints.freeVars (args1.zip args2)) ⊆
    (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2) := by
  induction args1 generalizing args2 with
  | nil => simp_all [freeVars]
  | cons head tail ih =>
    unfold List.zip List.zipWith
    split
    · rename_i xs ys xs' y ys' heq
      simp_all [freeVars]
      obtain ⟨heq1, heq2⟩ := heq
      subst ys xs'
      apply And.intro
      · simp [Constraint.freeVars, Constraint.freeVars]
        simp_all (config := {maxDischargeDepth := 10})
      · have ih' := @ih ys'
        unfold List.zip at ih'
        apply List.subset_append_of_subset_right head.freeVars
        generalize LMonoTys.freeVars tail = A at *
        generalize y.freeVars = B at *
        generalize LMonoTys.freeVars ys' = C at *
        have : A ++ C ⊆ A ++ (B ++ C) := by simp_all
        exact fun _ x => this (ih' x)
    · simp_all [freeVars]
  done

theorem Constraints.freeVars_of_zip_superset (h : args1.length = args2.length) :
    (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2) ⊆
    (Constraints.freeVars (args1.zip args2)) := by
  induction args1 generalizing args2 with
  | nil =>
    simp_all [freeVars, LMonoTys.freeVars]
    have : args2 = [] := by exact List.length_eq_zero_iff.mp (id (Eq.symm h))
    simp_all [LMonoTys.freeVars]
  | cons head tail ih =>
    cases args2
    case cons.nil =>
      simp_all
    case cons.cons x xs =>
      have ih' := @ih xs (by simp_all)
      simp only [LMonoTys.freeVars_of_cons, Constraints.freeVars_of_cons_zip]
      -- We give Lean permission to do increased backchaining to allow automatic
      -- application of lemmas like
      -- `List.subset_append_of_subset_left` and
      -- `List.subset_append_of_subset_right`,
      simp_all (config := {maxDischargeDepth := 10})
    done

theorem Constraints.freeVars_zip_dedup_length (h : args1.length = args2.length) :
  (Constraints.freeVars (args1.zip args2)).dedup.length =
  (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2).dedup.length := by
  have h1 := @Constraints.freeVars_of_zip_superset args1 args2 h
  have h2 := @Constraints.freeVars_of_zip_subset args1 args2
  have h3 := @List.length_dedup_subset_eq _ _
              (args1.freeVars ++ args2.freeVars) (freeVars (List.zip args1 args2)) h1 h2
  exact id (Eq.symm h3)

/--
The size of a constraint, useful for termination arguments.
-/
def Constraint.size (c : Constraint) : Nat :=
  c.fst.size + c.snd.size

@[simp]
theorem Constraint.size_gt_zero : 0 < Constraint.size c := by
  simp_all [Constraint.size]
  have := @LMonoTy.size_gt_zero c.fst
  omega

/--
The size of a set of constraint, where each constituent type is sized as a tree.
-/
def Constraints.size (cs : Constraints) : Nat :=
  match cs with
  | [] => 0
  | c :: rest => c.size + Constraints.size rest

@[simp]
theorem Constraints.size_cons :
    Constraints.size rest < Constraints.size (c :: rest) := by
  simp [Constraints.size, Constraint.size]
  have := @LMonoTy.size_gt_zero c.fst
  have := @LMonoTy.size_gt_zero c.snd
  omega

@[simp]
theorem Constraints.size_append :
    Constraints.size (xs ++ ys) = Constraints.size xs + Constraints.size ys := by
  induction xs
  case nil => simp_all [size]
  case cons x xs ih =>
    simp_all [size]; omega

theorem Constraints.size_zip_eq (h : args1.length = args2.length) :
    Constraints.size (args1.zip args2) = LMonoTys.size args1 + LMonoTys.size args2 := by
  induction args1 generalizing args2
  case nil =>
    simp_all [size, LMonoTys.size]
    have : args2 = [] := by exact List.length_eq_zero_iff.mp (id (Eq.symm h))
    simp_all [LMonoTys.size]
  case cons head tail ih =>
    cases args2
    case nil => simp_all
    case cons x xs =>
      simp_all [size, Constraint.size, LMonoTys.size]
      omega

/--
Function encoding the property that the free variables in a substitution `newS`
are a subset of those in constraints `cs` and substitution `oldS`.
-/
def Subst.freeVars_subset_prop (cs : Constraints) (newS oldS : SubstInfo) : Prop :=
  Subst.freeVars newS.subst ⊆
  Constraints.freeVars cs ++ Subst.freeVars oldS.subst

/--
The free variables in a well-formed type substitution (i.e., `newS.subst` and
`newS.isWF`) are bounded by those in the type constraints `cs` and in the old
substitution `oldS`.
-/
structure ValidSubstRelation (cs : Constraints) (oldS : SubstInfo) where
  newS : SubstInfo
  goodSubset : Subst.freeVars_subset_prop cs newS oldS

@[simp]
theorem Subst.freeVars_subset_prop_of_empty (S : SubstInfo) :
    Subst.freeVars_subset_prop [] S S := by
  simp [Subst.freeVars_subset_prop]

theorem Subst.freeVars_subset_prop_single_constraint_comm :
    Subst.freeVars_subset_prop [(t1, t2)] newS oldS =
    Subst.freeVars_subset_prop [(t2, t1)] newS oldS := by
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars]
  apply propext
  constructor
  · intro h x hx
    have hmem := h hx
    simp only [List.append_assoc, List.nil_append, List.mem_append] at hmem ⊢
    rcases hmem with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2
    · exact Or.inr (Or.inr h3)
  · intro h x hx
    have hmem := h hx
    simp only [List.append_assoc, List.nil_append, List.mem_append] at hmem ⊢
    rcases hmem with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2
    · exact Or.inr (Or.inr h3)

private theorem Subst.freeVars_subset_prop_mk_cons
    (R1 : ValidSubstRelation [c] S)
    (R2 : ValidSubstRelation c_rest R1.newS) :
    Subst.freeVars_subset_prop (c :: c_rest) R2.newS S := by
  obtain ⟨h_si_1, h_prop_1⟩ := R1
  obtain ⟨h_si_2, h_prop_2⟩ := R2
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    List.append_assoc, List.nil_append] at h_prop_1 h_prop_2 ⊢
  intro x hx
  have hB := h_prop_2 hx
  rcases List.mem_append.mp hB with h | h
  · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))
  · have hA := h_prop_1 h
    rcases List.mem_append.mp hA with h' | h'
    · exact List.mem_append_left _ h'
    · rcases List.mem_append.mp h' with h'' | h''
      · exact List.mem_append_right _ (List.mem_append_left _ h'')
      · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h''))

private theorem ugly_subset_lemma {α : Type} [DecidableEq α]
    (newS oldS sty lty orig_lty : List α)
    (h1 : newS ⊆ sty ++ (lty ++ oldS))
    (h2 : sty ⊆ oldS)
    (h3 : lty ⊆ orig_lty ++ oldS) :
    newS ⊆ orig_lty ++ oldS := by
  have h1' : newS ⊆ sty ++ lty ++ oldS := by simp_all
  clear h1
  have h2 : sty ++ lty ++ oldS ⊆ (lty ++ oldS) := by simp_all
  have h3 : newS ⊆ (lty ++ oldS) := fun _ a_1 => h2 (h1' a_1)
  have h4 : lty ++ oldS ⊆ orig_lty ++ oldS := by simp_all
  exact fun _ a_1 => h4 (h3 a_1)

theorem Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S
    (S : SubstInfo) (id : TyIdentifier) (orig_lty sty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : HMaps.find? S.subst id = some sty)
    (relS : ValidSubstRelation [(sty, lty)] S) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] relS.newS S := by
  obtain ⟨newS, h_newS_subset⟩ := relS
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    LMonoTy.freeVars, List.append_assoc, List.nil_append] at h_newS_subset ⊢
  have h_sty := Subst.freeVars_of_find_subset S.subst _h5
  have h_lty_sub := LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  apply List.subset_append_of_subset_right
  have key := ugly_subset_lemma (Subst.freeVars newS.subst) (Subst.freeVars S.subst)
    sty.freeVars lty.freeVars orig_lty.freeVars
  apply key
  · intro x hx
    have := h_newS_subset hx
    simpa [List.append_assoc] using this
  · exact h_sty
  · rw [h_lty]; exact h_lty_sub

theorem Subst.freeVars_subset_prop_of_single_constraint
    (S newS : SubstInfo) (new_subst : Subst) (id : TyIdentifier) (orig_lty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (h_new_subst : new_subst = HMaps.insert (Subst.apply (HMap.single id lty) S.subst) id lty)
    (h' : SubstWF new_subst)
    (h_newS : newS = { subst := new_subst, isWF := h' }) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
  subst h_newS h_new_subst h_lty
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    LMonoTy.freeVars, List.append_assoc, List.nil_append]
  have h_ins := Subst.freeVars_of_insert
    (Subst.apply (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst)
    id (LMonoTy.subst S.subst orig_lty)
  have h_apply := Subst.freeVars_of_apply_subset_alt
    (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst
  have h_orig := LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_single := Subst.freeVars_singleton_subset id (LMonoTy.subst S.subst orig_lty)
  simp only [Subst.singleton] at h_single
  intro x hx
  suffices hsuff : x ∈ orig_lty.freeVars ++ Subst.freeVars S.subst by
    exact List.mem_cons_of_mem _ hsuff
  have hx1 := h_ins hx
  rcases List.mem_append.mp hx1 with h | h
  · rcases List.mem_append.mp (h_apply h) with h2 | h2
    · exact h_orig (h_single h2)
    · exact List.mem_append_right _ h2
  · exact h_orig h

theorem Subst.freeVars_subset_prop_of_tcons (S : SubstInfo)
    (name1 name2 : String) (args1 args2 : List LMonoTy)
    (h_new_constraints : new_constraints = args1.zip args2)
    (relS : ValidSubstRelation new_constraints S)  :
    Subst.freeVars_subset_prop
      [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
  obtain ⟨newS, h_newS_subset⟩ := relS
  subst h_new_constraints
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    LMonoTy.freeVars, List.append_assoc, List.nil_append] at h_newS_subset ⊢
  have h_zip := @Constraints.freeVars_of_zip_subset args1 args2
  intro x hx
  have hmem := h_newS_subset hx
  rcases List.mem_append.mp hmem with h | h
  · rcases List.mem_append.mp (h_zip h) with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_append_left _ h1)
  · exact List.mem_append_right _ (List.mem_append_right _ h)

private theorem Constraint.unify_termination_goal_1
    (S : SubstInfo) (id : TyIdentifier)
    (orig_lty lty sty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : HMaps.find? S.subst id = some sty) :
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length <
    (Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length =
    (Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] ++ S.subst.freeVars).dedup.length ∧
    Constraints.size [(sty, LMonoTy.subst S.subst orig_lty)] <
    Constraints.size [(LMonoTy.ftvar id, orig_lty)] := by
  have h_sty := Subst.freeVars_of_find_subset S.subst _h5
  have h_subst_orig_lty := LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_subset :
        (id :: (sty.freeVars ++
               ((LMonoTy.subst S.subst orig_lty).freeVars ++ S.subst.freeVars))) ⊆
        (id :: (orig_lty.freeVars ++ S.subst.freeVars)) := by
    simp_all
  generalize h_l1 : (sty.freeVars ++
                      ((LMonoTy.subst S.subst orig_lty).freeVars ++ S.subst.freeVars)) = l1 at *
  generalize h_l2 : (orig_lty.freeVars ++ S.subst.freeVars) = l2 at *
  have h_subset_right := @List.length_dedup_append_subset_right _ _ (id :: l1) (id :: l2) h_subset
  have h_len := @List.length_dedup_append_le_left _ _ (id :: l1) (id :: l2)
  have h_id : id ∉ l1 := by
    subst l1; simp_all
    have h_S_ok := S.isWF
    simp [SubstWF] at h_S_ok
    apply And.intro
    · have h_sty_values := HMaps.find?_mem_values S.subst _h5
      have h_id_keys := HMaps.find?_mem_keys S.subst _h5
      exact fun a => h_S_ok id h_id_keys (h_sty a)
    · have h_id_keys := HMaps.find?_mem_keys S.subst _h5
      exact h_S_ok id h_id_keys
  have h_dedup1 := @List.length_dedup_cons_of_not_mem _ _ id l1 h_id
  simp_all
  simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, h_l1, h_l2]
  omega
  done

-- This theorem follows from `Constraints.unify_termination_goal_1`, but also
-- requires the proof that
-- `Constraints.size [(t1, t2)] == Constraints.size [(t2, t1)]`
-- and similarly, `Constraints.freeVars_single_constraint_comm_subset`.
private theorem Constraint.unify_termination_goal_2
    (S : SubstInfo) (id : TyIdentifier)
    (orig_lty lty sty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : HMaps.find? S.subst id = some sty) :
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length <
    (Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length =
    (Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] ++ S.subst.freeVars).dedup.length ∧
    Constraints.size [(sty, LMonoTy.subst S.subst orig_lty)] <
    Constraints.size [(orig_lty, LMonoTy.ftvar id)] := by
  have h1 := @Constraints.freeVars_single_constraint_comm_subset orig_lty (LMonoTy.ftvar id)
  have h2 := @Constraints.freeVars_single_constraint_comm_subset (LMonoTy.ftvar id) orig_lty
  have h3 := Constraint.unify_termination_goal_1 S id orig_lty lty sty h_lty _h4 _h5
  generalize Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] = A at *
  generalize Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] = B at *
  generalize Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] = X at *
  generalize S.subst.freeVars = Y at *
  simp_all [Constraints.size, Constraint.size]
  have h_sub1 : A ++ Y ⊆ B ++ Y := by simp_all
  have h_sub2 : B ++ Y ⊆ A ++ Y := by simp_all
  have h_sub : (B ++ Y).dedup.length = (A ++ Y).dedup.length := by
    exact List.length_dedup_subset_eq (B ++ Y) (A ++ Y) h_sub2 h_sub1
  simp_all
  omega
  done

private theorem Constraint.unify_termination_goal_3
    (S : SubstInfo) (name1 name2 : String) (args1 args2 : List LMonoTy)
    (h_tcons : name1 = name2 ∧ args1.length = args2.length) :
    (Constraints.freeVars (args1.zip args2) ++ S.subst.freeVars).dedup.length <
    (Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] ++
     S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars (args1.zip args2) ++ S.subst.freeVars).dedup.length =
    (Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] ++
     S.subst.freeVars).dedup.length ∧
    Constraints.size (args1.zip args2) <
    Constraints.size [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] := by
  have h_zip_fvs_super := @Constraints.freeVars_of_zip_superset args1 args2 h_tcons.right
  have h_zip_fvs_sub := @Constraints.freeVars_of_zip_subset args1 args2
  have h_zip_size := @Constraints.size_zip_eq args1 args2 h_tcons.right
  have h_fvs_tcons :
    Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] =
    LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2 := by
    simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars]
  have h_size_tcons :
    Constraints.size [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] =
    1 + LMonoTys.size args1 + (1 + LMonoTys.size args2) := by
    simp_all [Constraints.size, Constraint.size, LMonoTy.size]
  simp_all
  clear h_size_tcons h_zip_size h_tcons h_fvs_tcons
  generalize Constraints.freeVars (args1.zip args2) = A at *
  generalize LMonoTys.freeVars args1 = B1 at *
  generalize LMonoTys.freeVars args2 = B2 at *
  generalize S.subst.freeVars = C at *
  have h1 : (A ++ C) ⊆ (B1 ++ (B2 ++ C)) := by
    simp_all
    have : B1 ++ B2 ⊆ B1 ++ (B2 ++ C) := by simp_all
    exact fun _ x => this (h_zip_fvs_sub x)
  have h2 : (B1 ++ (B2 ++ C)) ⊆ (A ++ C) := by
    simp_all
  have h_len_eq := @List.length_dedup_subset_eq _ _
                   (A ++ C) (B1 ++ (B2 ++ C)) h1 h2
  omega
  done

private theorem Constraints.unify_termination_goal_1
    (cs : Constraints) (c : Constraint) (S : SubstInfo) :
    (Constraints.freeVars [c] ++ S.subst.freeVars).dedup.length <
      (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars [c] ++ S.subst.freeVars).dedup.length =
        (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length ∧
    (Constraints.size [c] < Constraints.size (c :: cs) ∨
     Constraints.size [c] = Constraints.size (c :: cs)) := by
  simp_all [Constraints.freeVars, Constraints.size]
  have h_sub : (c.freeVars ++ S.subst.freeVars) ⊆
               (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) := by
    simp_all
  generalize (c.freeVars ++ S.subst.freeVars) = l1 at *
  generalize (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) = l2 at *
  have h1 : (l1.dedup.length < l2.dedup.length) ∨ (l1.dedup.length = l2.dedup.length) := by
    have := @List.length_dedup_of_subset_le _ _ l1 l2 h_sub
    exact Or.symm (Nat.eq_or_lt_of_le this)
  cases h1 <;> try simp_all
  exact Or.symm (Nat.eq_zero_or_pos (Constraints.size cs))
  done

private theorem Constraints.unify_termination_goal_2
    (cs : Constraints) (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S) :
    (Constraints.freeVars cs ++ relS.newS.subst.freeVars).dedup.length <
    (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars cs ++ relS.newS.subst.freeVars).dedup.length =
    (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length := by
  obtain ⟨newS, h_subset_prop⟩ := relS
  simp [Subst.freeVars_subset_prop, Constraints.freeVars] at h_subset_prop
  simp [Constraints.freeVars] at *
  have h_sub : (cs.freeVars ++ newS.subst.freeVars) ⊆
               (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) := by
    simp_all
    generalize newS.subst.freeVars = A at *
    generalize c.freeVars = B at *
    generalize cs.freeVars = C at *
    generalize S.subst.freeVars = D at *
    have : B ++ D ⊆ B ++ (C ++ D) := by simp_all
    exact fun _ x => this (h_subset_prop x)
  have := @List.length_dedup_of_subset_le _ _
            (cs.freeVars ++ newS.subst.freeVars)
            (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars))
            h_sub
  omega
  done

/--
Kinds of errors that can occur during type unification. Also includes the
failing constraint.
-/
inductive UnifyError where
  | ImpossibleToUnify (c : Constraint) (original : Option Constraint := .none)
  | FailedOccursCheck (tyvar : TyIdentifier) (ty : LMonoTy) (c : Constraint) (original : Option Constraint := .none)
  deriving Repr, Inhabited, DecidableEq

def UnifyError.addOriginalConstraint (e : UnifyError) (o : Constraint) : UnifyError :=
  match e with
  | ImpossibleToUnify c _ => ImpossibleToUnify c o
  | FailedOccursCheck tyvar ty c _ => FailedOccursCheck tyvar ty c o

instance : ToFormat UnifyError where
  format u := match u with
    | .ImpossibleToUnify c opt_original =>
      let msg_fn := fun (x : Constraint) => f!"Impossible to unify {x.fst} with {x.snd}."
      match opt_original with
      | none => msg_fn c
      | some original =>
        if c == original then
          msg_fn c
        else
          (msg_fn original) ++ f!"\nFirst mismatch: {c.fst} with {c.snd}."
    | .FailedOccursCheck tyvar ty c opt_original =>
      let msg_fn := f!"Failed occurs check: \
                      {tyvar} cannot be unified with {ty} because it would \
                      create a circular dependency during unification."
        match opt_original with
        | none => msg_fn
        | some original =>
          if original == c then msg_fn
          else msg_fn ++ f!" Failure occurred when unifying {original.fst} with {original.snd}."

mutual
/--
Type unification for a single constraint `c` w.r.t. a well-formed type
substitution `S`. See `Constraints.unify` for the top-level function.
-/
def Constraint.unifyOne (c : Constraint) (S : SubstInfo) :
  Except UnifyError (ValidSubstRelation [c] S) :=
  let (t1, t2) := c
  if _h1: t1 == t2 then
     have h_sub : Subst.freeVars_subset_prop [(t1, t2)] S S := by
      simp [Subst.freeVars_subset_prop]
    .ok { newS := S, goodSubset := h_sub }
  else
    match _h2: t1, t2 with
    | .ftvar id, orig_lty | orig_lty, .ftvar id => do
      -- Unification for variable `id`
      let lty := LMonoTy.subst S.subst orig_lty
      have h_sub1 : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] S S := by
        simp [Subst.freeVars_subset_prop]
      have h_sub2 : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] S S := by
        simp [Subst.freeVars_subset_prop]
      if _h3 : (.ftvar id) == lty then
        .ok { newS := S, goodSubset := by all_goals simp [h_sub1, h_sub2] }
      else if _h4 : id ∈ lty.freeVars then
        -- Occurs check: `id` should not appear in the free type variables of
        -- `lty`.
        .error (.FailedOccursCheck id lty (t1, t2))
      else
        -- At this point, `id` cannot be a free variable in `lty`.
        match _h5 : S.subst.find? id with
        | some sty =>
          -- `sty` must unify with `lty`.
          let relS ← Constraint.unifyOne (sty, lty) S
          have h_sub1_new : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] relS.newS S := by
            exact Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S
                  S id orig_lty sty lty rfl _h4 _h5 relS
          have h_sub2_new : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] relS.newS S := by
            simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
          .ok { newS := relS.newS,
                goodSubset := by all_goals simp [h_sub1_new, h_sub2_new] }
        | none =>
          -- `id` must unify with `lty`. We then add `[id ↦ lty]` to the
          -- substitution.
          have h_id_lty_WF : SubstWF (Subst.singleton id lty) = true :=
            SubstWF.single_subst id lty _h4
          have h_subst_apply_WF : SubstWF (Subst.apply (HMap.single id lty) S.subst) := by
            have := SubstWF.apply_one_substituted_type S.subst S.isWF id orig_lty
            simpa using this
          let new_subst := (Subst.apply (HMap.single id lty) S.subst).insert id lty
          have h' : SubstWF new_subst := by
            exact SubstWF.cons_of_subst_apply S.subst S.isWF id orig_lty lty rfl _h4
          let newS := SubstInfo.mk new_subst h'
          have h_sub1 : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
            exact Subst.freeVars_subset_prop_of_single_constraint S newS new_subst
                   id orig_lty (LMonoTy.subst S.subst orig_lty) rfl rfl h' rfl
          have h_sub2 : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] newS S := by
            simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
          .ok { newS := newS, goodSubset := by all_goals simp [h_sub1, h_sub2] }
    | .bitvec n1, .bitvec n2 =>
      if _h7 : n1 == n2 then
        .ok { newS := SubstInfo.mk [] (by simp [SubstWF, HMaps.keys]), goodSubset := by grind }
      else
        .error (.ImpossibleToUnify (t1, t2))
    | .tcons name1 args1, .tcons name2 args2 => do
      if _h6 : name1 == name2 && args1.length == args2.length then
       let new_constraints := List.zip args1 args2
       let relS ← Constraints.unifyCore new_constraints S
       have h_sub : Subst.freeVars_subset_prop
                    [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
         exact Subst.freeVars_subset_prop_of_tcons S name1 name2 args1 args2 rfl relS
       .ok { newS := relS.newS, goodSubset := by simp [h_sub] }
      else
        .error (.ImpossibleToUnify (t1, t2))
    | .bitvec _, .tcons _ _ =>
        .error (.ImpossibleToUnify (t1, t2))
    | .tcons _ _, .bitvec _ =>
        .error (.ImpossibleToUnify (t1, t2))
  termination_by ((((Constraints.freeVars [c]) ++ S.subst.freeVars).dedup.length),
                  Constraints.size [c],
                  0)
  decreasing_by
    all_goals simp_all [Prod.lex_def]
    -- Subgoal 1
    · exact Constraint.unify_termination_goal_1 S id orig_lty lty sty (by exact rfl) _h4 _h5
    -- Subgoal 2
    · exact Constraint.unify_termination_goal_2 S id orig_lty lty sty (by exact rfl) _h4 _h5
    -- Subgoal 3
    · exact Constraint.unify_termination_goal_3 S name1 name2 args1 args2 _h6

/--
Type unification for constraints `cs` w.r.t. a well-formed type
substitution `S`. See `Constraints.unify` for the top-level function.
-/
def Constraints.unifyCore (cs : Constraints) (S : SubstInfo) :
    Except UnifyError (ValidSubstRelation cs S) := do
  match _h0 : cs with
  | [] => .ok { newS := S, goodSubset := by simp [Subst.freeVars_subset_prop_of_empty] }
  | c :: c_rest =>
    let relS ← Constraint.unifyOne c S |> .mapError (fun e => UnifyError.addOriginalConstraint e c)
    let new_relS ← Constraints.unifyCore c_rest relS.newS
    .ok { newS := new_relS.newS, goodSubset := by simp [Subst.freeVars_subset_prop_mk_cons] }
  termination_by ((((Constraints.freeVars cs) ++ S.subst.freeVars).dedup.length),
                  Constraints.size cs,
                  1)

  decreasing_by
    all_goals simp_all [Prod.lex_def]
    -- Subgoal 1
    · exact Constraints.unify_termination_goal_1 c_rest c S
    -- Subgoal 2
    · exact Constraints.unify_termination_goal_2 c_rest c S relS
end

/--
`Constraints.unify` is Lambda's type unification function, which implements a
bottom-up Hindley-Milner style algorithm that finds the most general type
(principal type) of an expression by finding a substitution that makes all the
types in the input constraints equal.

On failure, returns the constraint that cannot be unified --
note that this can be different from a constraint `c` in `cs` because it could
involve subterms of types in `c` (e.g., `Map int bool` and `Map int int` fail to
unify because `bool` and `int` can't be unified). The constraint returned on
failure would be the _first_ mismatching one, not necessarily the only one.

Returns a well-formed `S` w.r.t. `cs` otherwise.
-/
def Constraints.unify (constraints : Constraints) (S : SubstInfo) :
    Except UnifyError SubstInfo := do
    let relS ← Constraints.unifyCore constraints S
    .ok relS.newS

---------------------------------------------------------------------

end -- public section
end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Util.Name
import all Strata.Util.Name
import Std.Data.HashSet.Lemmas
import Strata.Util.ListUtilsProps
import Std.Data.String.ToNat

/-!
# Proofs about `Strata.Name.findUnique` and `Strata.Name.freshName`

`findUniqueFast_not_mem` and `findUniqueSlow_not_mem` prove that both the
fast and slow paths return a name not in `usedNames`.  `findUnique_not_mem`
combines them into a single correctness theorem for `findUnique`.

`freshNameBy_not_taken` proves that `freshNameBy` returns a name `taken` rejects when at most
`fuel` names are taken, and `freshName_not_mem` that `freshName` returns a name not in `taken`.
`freshNamesBy_fresh` and `freshNames_fresh` prove the same for several names at once, and that
the names are pairwise distinct.
-/

public section

namespace Strata.Name

/-- `disambiguate` is injective in its suffix when the base name is fixed.
    This follows from `Nat.repr` injectivity, which is not yet available in our
    Lean toolchain. -/
def DisambiguateInjective : Prop :=
  ∀ (baseName : String) (m n : Nat), disambiguate baseName m = disambiguate baseName n → m = n

/-- When `findUniqueFast` returns `some result`, the result is not in `usedNames`. -/
theorem findUniqueFast_not_mem (baseName candidate : String) (suffix : Nat)
    (usedNames : Std.HashSet String) (fuel : Nat) (result : String)
    (h : findUniqueFast baseName candidate suffix usedNames fuel = some result) :
    result ∉ usedNames := by
  induction fuel generalizing candidate suffix with
  | zero =>
    unfold findUniqueFast at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hc; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · simp at h
  | succ n ih =>
    unfold findUniqueFast at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hc; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · exact ih _ _ h

/-- When `findUniqueSlow` returns `some result`, the result is not in `usedSet`. -/
theorem findUniqueSlow_not_mem (baseName candidate : String) (suffix : Nat)
    (usedSet : Std.HashSet String) (remaining : List String) (result : String)
    (h : findUniqueSlow baseName candidate suffix usedSet remaining = some result) :
    result ∉ usedSet := by
  generalize hlen : remaining.length = n at *
  induction n using Nat.strongRecOn generalizing candidate suffix remaining with
  | _ n ih =>
    unfold findUniqueSlow at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hc; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · split at h
      · have : (remaining.erase candidate).length < remaining.length := by grind
        exact ih _ (by omega) _ _ _ h rfl
      · simp at h

/-- The slow path never returns `none` when `remaining` covers `usedSet` and
    `disambiguate` is injective. The invariant tracks that every member of `usedSet`
    is either still in `remaining` or was a previously tried candidate. -/
private theorem findUniqueSlow_ne_none
    (h_inj : DisambiguateInjective)
    (baseName : String) (suffix : Nat)
    (usedSet : Std.HashSet String) (remaining : List String)
    (h_covers : ∀ s, s ∈ usedSet → s ∈ remaining ∨
      ∃ k, k < suffix ∧ s = disambiguate baseName k) :
    findUniqueSlow baseName (disambiguate baseName suffix) (suffix + 1)
      usedSet remaining ≠ none := by
  generalize hlen : remaining.length = n
  induction n using Nat.strongRecOn generalizing suffix remaining with
  | _ n ih =>
    unfold findUniqueSlow
    split
    · simp
    · rename_i h_in_set
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem,
    Decidable.not_not] at h_in_set
      have h_in_rem : disambiguate baseName suffix ∈ remaining := by
        rcases h_covers _ h_in_set with h | ⟨k, hk, heq⟩
        · exact h
        · exact absurd (h_inj _ _ _ heq) (by omega)
      split
      · have h_len : (remaining.erase (disambiguate baseName suffix)).length <
            remaining.length := by grind
        refine ih _ (by omega) (suffix + 1)
          (remaining.erase (disambiguate baseName suffix)) ?_ rfl
        intro s hs
        rcases h_covers s hs with h_in_rem' | ⟨k, hk, heq⟩
        · by_cases heq : s = disambiguate baseName suffix
          · exact Or.inr ⟨suffix, by omega, heq⟩
          · exact Or.inl ((List.mem_erase_of_ne heq).mpr h_in_rem')
        · exact Or.inr ⟨k, by omega, heq⟩
      · exact absurd (List.contains_iff_mem.mpr h_in_rem) ‹_›

/-- `findUnique` returns a name not in `usedNames`, given that `disambiguate` is
    injective in its suffix argument. -/
theorem findUnique_not_mem (h_inj : DisambiguateInjective)
    (baseName : String) (startSuffix : Nat)
    (usedNames : Std.HashSet String) :
    findUnique baseName startSuffix usedNames ∉ usedNames := by
  unfold findUnique
  simp only
  split
  · next hfast => exact findUniqueFast_not_mem _ _ _ _ _ _ hfast
  · next hfast =>
    split
    · next hslow => exact findUniqueSlow_not_mem _ _ _ _ _ _ hslow
    · next hslow =>
      exfalso
      exact findUniqueSlow_ne_none h_inj baseName (startSuffix + 1000000) usedNames
        usedNames.toList (fun s hs => Or.inl (Std.HashSet.mem_toList.mpr hs)) hslow

/-- The candidates `freshNameBy` tries, `base`, `base_1`, `base_2`, …, are pairwise distinct. -/
private theorem freshCandidate_inj (base : String) :
    Function.Injective (fun k : Nat => if k = 0 then base else base ++ "_" ++ toString k) := by
  intro j k h
  have hlen := congrArg String.length h
  have hu : ("_" : String).length = 1 := rfl
  by_cases hj : j = 0 <;> by_cases hk : k = 0
  · omega
  · simp only [hj, hk, ↓reduceIte, String.length_append] at hlen
    omega
  · simp only [hj, hk, ↓reduceIte, String.length_append] at hlen
    omega
  · simp only [hj, hk, ↓reduceIte] at h
    have h' := congrArg String.toList h
    simp only [String.toList_append] at h'
    exact Nat.repr_injective (String.toList_inj.1 (List.append_cancel_left h'))

/-- `firstUntaken taken cand fuel i` is `cand k` for some `k` from `i` to `i + fuel`, and either
    `taken` rejects `cand k`, or it accepts every candidate from `cand i` to `cand (i + fuel)`. -/
private theorem firstUntaken_spec (taken : String → Bool) (cand : Nat → String) :
    ∀ fuel i, ∃ k, firstUntaken taken cand fuel i = cand k ∧ i ≤ k ∧ k ≤ i + fuel ∧
      (taken (cand k) = false ∨ ∀ j, i ≤ j → j ≤ i + fuel → taken (cand j) = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i
    refine ⟨i, rfl, Nat.le_refl _, by omega, ?_⟩
    cases h : taken (cand i)
    · exact .inl rfl
    · exact .inr fun j hj hj' => by rw [show j = i by omega]; exact h
  | succ fuel ih =>
    intro i
    unfold firstUntaken
    cases h : taken (cand i)
    · exact ⟨i, by simp, Nat.le_refl _, by omega, .inl h⟩
    · obtain ⟨k, hk, hik, hki, hor⟩ := ih (i + 1)
      refine ⟨k, by simp [hk], by omega, by omega, ?_⟩
      rcases hor with hf | hall
      · exact .inl hf
      · refine .inr fun j hj hj' => ?_
        by_cases hji : j = i
        · rw [hji]; exact h
        · exact hall j (by omega) (by omega)

/-- If every name `taken` accepts is in `L`, and `L` has at most `fuel` names, then `taken`
    rejects the name `freshNameBy taken fuel base` returns. -/
theorem freshNameBy_not_taken (taken : String → Bool) (fuel : Nat) (base : String)
    (L : List String) (hL : ∀ s, taken s = true → s ∈ L) (hlen : L.length ≤ fuel) :
    taken (freshNameBy taken fuel base) = false := by
  let cand := fun k : Nat => if k = 0 then base else base ++ "_" ++ toString k
  obtain ⟨k, hk, -, -, hor⟩ := firstUntaken_spec taken cand (fuel + 1) 0
  unfold freshNameBy
  rw [hk]
  rcases hor with hf | hall
  · exact hf
  · exfalso
    have hnd : ((List.range (fuel + 2)).map cand).Nodup :=
      List.nodup_range.map _ fun i j hne he => hne (freshCandidate_inj base he)
    have hsub : (List.range (fuel + 2)).map cand ⊆ L := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      exact hL _ (hall j (Nat.zero_le _) (by simp at hj; omega))
    have := List.subset_nodup_length hnd hsub
    simp at this
    omega

/-- `freshName taken base` is not in `taken`. -/
theorem freshName_not_mem (taken : Std.HashSet String) (base : String) :
    freshName taken base ∉ taken := by
  intro hmem
  have h := freshNameBy_not_taken taken.contains taken.size base taken.toList
    (fun s hs => Std.HashSet.mem_toList.2 (Std.HashSet.mem_iff_contains.2 hs))
    (by simp [Std.HashSet.length_toList])
  exact absurd (Std.HashSet.mem_iff_contains.1 hmem) (by simpa [freshName] using h)

/-- If every name `taken` accepts is in a list of at most `fuel` names, the names
    `freshNamesBy taken fuel bases` returns are pairwise distinct and `taken` rejects each. -/
theorem freshNamesBy_fresh (bases : List String) :
    ∀ (taken : String → Bool) (fuel : Nat) (L : List String),
      (∀ s, taken s = true → s ∈ L) → L.length ≤ fuel →
      (∀ n ∈ freshNamesBy taken fuel bases, taken n = false) ∧
        (freshNamesBy taken fuel bases).Nodup := by
  induction bases with
  | nil => intro _ _ _ _ _; simp [freshNamesBy]
  | cons b rest ih =>
    intro taken fuel L hL hlen
    have hn := freshNameBy_not_taken taken fuel b L hL hlen
    obtain ⟨hrest, hnd⟩ := ih (fun m => taken m || m == freshNameBy taken fuel b) (fuel + 1)
      (freshNameBy taken fuel b :: L)
      (fun s hs => by
        rcases Bool.or_eq_true _ _ ▸ hs with h | h
        · exact List.mem_cons_of_mem _ (hL s h)
        · exact (beq_iff_eq.1 h) ▸ List.mem_cons_self)
      (by simp; omega)
    simp only [freshNamesBy, List.mem_cons, List.nodup_cons]
    refine ⟨fun m hm => ?_, fun hm => ?_, hnd⟩
    · rcases hm with rfl | hm
      · exact hn
      · have := hrest m hm
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
    · have := hrest _ hm
      simp at this

/-- The names `freshNames taken bases` returns are pairwise distinct and none is in `taken`. -/
theorem freshNames_fresh (taken : Std.HashSet String) (bases : List String) :
    (∀ n ∈ (freshNames taken bases).1, n ∉ taken) ∧ (freshNames taken bases).1.Nodup := by
  obtain ⟨hnt, hnd⟩ := freshNamesBy_fresh bases taken.contains taken.size taken.toList
    (fun s hs => Std.HashSet.mem_toList.2 (Std.HashSet.mem_iff_contains.2 hs))
    (by simp [Std.HashSet.length_toList])
  refine ⟨fun n hn hmem => ?_, hnd⟩
  have := hnt n hn
  rw [Std.HashSet.mem_iff_contains.1 hmem] at this
  cases this

end Strata.Name

end -- public section

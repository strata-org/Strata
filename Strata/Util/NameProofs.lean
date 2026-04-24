/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Util.Name
import Std.Data.HashSet.Lemmas

/-!
# Proofs about `Strata.Name.findUnique`

`findUniqueFast_not_mem` and `findUniqueSlow_not_mem` prove that both the
fast and slow paths return a name not in `usedNames`.  `findUnique_not_mem`
combines them into a single correctness theorem for `findUnique`.
-/

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
    · simp at h; subst h
      rename_i hc; simp [Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · simp at h
  | succ n ih =>
    unfold findUniqueFast at h
    split at h
    · simp at h; subst h
      rename_i hc; simp [Std.HashSet.contains_eq_false_iff_not_mem] at hc
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
    · simp at h; subst h
      rename_i hc; simp [Std.HashSet.contains_eq_false_iff_not_mem] at hc
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
      simp at h_in_set
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

end Strata.Name

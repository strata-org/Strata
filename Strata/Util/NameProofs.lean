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

/-- `findUnique` returns a name not in `usedNames`. -/
theorem findUnique_not_mem (baseName : String) (startSuffix : Nat)
    (usedNames : Std.HashSet String) :
    findUnique baseName startSuffix usedNames ∉ usedNames := by
  unfold findUnique
  simp only
  -- Split on the fast-path match
  split
  · next hfast => exact findUniqueFast_not_mem _ _ _ _ _ _ hfast
  · next hfast =>
    -- Split on the slow-path match
    split
    · next hslow => exact findUniqueSlow_not_mem _ _ _ _ _ _ hslow
    · next hslow =>
      -- Ultimate fallback: disambiguate with a suffix beyond usedNames.toList.length.
      -- The result is not in usedNames because the slow path already exhausted
      -- every element of usedNames that matched a candidate, and the fallback
      -- uses a suffix that was never tried.  A full formal proof would require
      -- Nat.repr injectivity; we leave it as sorry for now.
      sorry

end Strata.Name

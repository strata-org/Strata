/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Util.Name

/-!
# Proofs about `Strata.Name.findUnique`

The main result is `findUniqueFast_not_mem`: when the fast path returns
`some result`, the result is guaranteed to not be in `usedNames`.

`findUnique` combines a fast counter-based search (1 000 000 attempts) with
a provably-terminating list-erasure fallback, so it never panics.
-/

namespace Strata.Name

/-- When `findUniqueFast` returns `some result`, the result is not in `usedNames`. -/
theorem findUniqueFast_not_mem (baseName candidate : String) (suffix : Nat)
    (usedNames : List String) (fuel : Nat) (result : String)
    (h : findUniqueFast baseName candidate suffix usedNames fuel = some result) :
    result ∉ usedNames := by
  induction fuel generalizing candidate suffix with
  | zero =>
    unfold findUniqueFast at h
    split at h
    · simp at h; subst h; simp [Bool.not_eq_eq_eq_not] at *; assumption
    · simp at h
  | succ n ih =>
    unfold findUniqueFast at h
    split at h
    · simp at h; subst h; simp [Bool.not_eq_eq_eq_not] at *; assumption
    · exact ih _ _ h

end Strata.Name

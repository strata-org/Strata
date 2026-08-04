/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Identifiers
import all Strata.Languages.Core.Identifiers
import all Init.Data.String.Lemmas.Pattern.String.ForwardPattern
import all Init.Data.String.TakeDrop
import all Init.Data.String.Slice
import all Init.Data.String.Basic

/-!
# Properties of `Core` identifiers

Theorems about the identifier predicates defined in
`Strata.Languages.Core.Identifiers` (`CoreIdent.isOldIdent`, `CoreIdent.mkOld`).

### Key results
* `isOldIdent_iff_exists_mkOld` — the `old`-prefix predicate holds exactly for
  identifiers produced by `mkOld`.
* `not_isOldIdent_of_ne_mkOld` — its contrapositive: an identifier that is no
  `mkOld s` is not `old`-prefixed.
-/

public section

namespace Core

/-- `isOldIdent id ↔ ∃ s, id = mkOld s`.  `String.startsWith` in this toolchain
    routes through the `Slice`/iterator machinery and does not reduce by `decide`;
    the proof goes via the `startsWith_iff` characterization plus `copy_toSlice`. -/
theorem isOldIdent_iff_exists_mkOld (id : CoreIdent) :
    CoreIdent.isOldIdent id = true ↔ ∃ s, id = CoreIdent.mkOld s := by
  unfold CoreIdent.isOldIdent
  rw [show (id.name.startsWith CoreIdent.oldStr)
        = String.Slice.Pattern.ForwardSliceSearcher.startsWith
            CoreIdent.oldStr.toSlice id.name.toSlice
      from rfl]
  rw [String.Slice.Pattern.ForwardSliceSearcher.startsWith_iff,
      String.copy_toSlice, String.copy_toSlice]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    obtain ⟨name, m⟩ := id
    cases m
    simp only [CoreIdent.mkOld, CoreIdent.oldStr] at ht ⊢
    rw [ht]
  · rintro ⟨s, rfl⟩
    exact ⟨s, by simp [CoreIdent.mkOld, CoreIdent.oldStr]⟩

/-- Contrapositive of `isOldIdent_iff_exists_mkOld`: if `id ≠ mkOld x` for all
    `x`, then `id` is not `old`-prefixed. -/
theorem not_isOldIdent_of_ne_mkOld (id : CoreIdent)
    (h : ∀ x, id ≠ CoreIdent.mkOld x) : ¬ CoreIdent.isOldIdent id := by
  intro hc
  obtain ⟨s, hs⟩ := (isOldIdent_iff_exists_mkOld id).1 hc
  exact h s hs

end Core

end -- public section

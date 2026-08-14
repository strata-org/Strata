/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Identifiers
import all Strata.Languages.Core.Identifiers

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

/-- `isOldIdent id ↔ ∃ s, id = mkOld s`: the `old`-prefix predicate holds exactly
    for identifiers produced by `mkOld`. -/
theorem isOldIdent_iff_exists_mkOld (id : CoreIdent) :
    CoreIdent.isOldIdent id = true ↔ ∃ s, id = CoreIdent.mkOld s := by
  unfold CoreIdent.isOldIdent
  rw [List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨String.ofList t, ?_⟩
    obtain ⟨name, m⟩ := id
    cases m
    simp only [CoreIdent.mkOld, Lambda.Identifier.mk.injEq, and_true]
    apply String.ext
    simp only [String.toList_append, String.toList_ofList]
    exact ht.symm
  · rintro ⟨s, rfl⟩
    exact ⟨s.toList, by simp [CoreIdent.mkOld, String.toList_append]⟩

/-- Contrapositive of `isOldIdent_iff_exists_mkOld`: if `id ≠ mkOld x` for all
    `x`, then `id` is not `old`-prefixed. -/
theorem not_isOldIdent_of_ne_mkOld (id : CoreIdent)
    (h : ∀ x, id ≠ CoreIdent.mkOld x) : ¬ CoreIdent.isOldIdent id := by
  intro hc
  obtain ⟨s, hs⟩ := (isOldIdent_iff_exists_mkOld id).1 hc
  exact h s hs

end Core

end -- public section

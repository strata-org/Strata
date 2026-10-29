/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Identifiers
import all Strata.Languages.Core.Identifiers
import all Strata.DL.Lambda.LExpr

/-!
# Properties of `Core` identifiers

Theorems about the identifier predicates defined in
`Strata.Languages.Core.Identifiers` (`CoreIdent.isOldIdent`, `CoreIdent.mkOld`,
`isAllowedName`).

### Key results
* `isOldIdent_iff_exists_mkOld` — the `old`-prefix predicate holds exactly for
  identifiers produced by `mkOld`.
* `not_isOldIdent_of_ne_mkOld` — its contrapositive: an identifier that is no
  `mkOld s` is not `old`-prefixed.
* `not_genTyPrefix_of_isAllowedName` — a name a user may write does not start
  with the generated type-variable prefix.
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

/-- `isAllowedName` stated on character lists. -/
theorem isAllowedName_eq_toList :
    isAllowedName =
      fun n => !(reservedNamePrefixes.any (fun p => p.toList.isPrefixOf n.toList)) := by
  funext n
  have hpfx : ∀ p : String, n.startsWith p = p.toList.isPrefixOf n.toList := fun p => by
    rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, String.startsWith_string_iff]
  simp only [isAllowedName, hpfx]

section
open Lambda

/-- A name a user may write does not start with the prefix of generated type variables. -/
theorem not_genTyPrefix_of_isAllowedName {n : String} (h : isAllowedName n = true) :
    ¬ (genTyPrefix.toList.isPrefixOf n.toList = true) := by
  simp only [isAllowedName_eq_toList, reservedNamePrefixes, List.any_cons, List.any_nil,
    Bool.or_false, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  simp only [h.1, Bool.false_eq_true, not_false_eq_true]

end

end Core

end -- public section

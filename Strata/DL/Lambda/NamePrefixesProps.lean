/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.NamePrefixes

/-! Properties of `isAllowedName`, the check that a name uses no reserved prefix. The main
fact is `not_genTyPrefix_of_isAllowedName`: an allowed name does not start with the prefix of
generated type variables. -/

public section

namespace Lambda

/-- `isAllowedName` stated on character lists. -/
theorem isAllowedName_eq_toList :
    isAllowedName =
      fun n => !(reservedNamePrefixes.any (fun p => p.toList.isPrefixOf n.toList)) := by
  funext n
  have hpfx : ∀ p : String, n.startsWith p = p.toList.isPrefixOf n.toList := fun p => by
    rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, String.startsWith_string_iff]
  simp only [isAllowedName, hpfx]

/-- A name a user may write does not start with the prefix of generated type variables. -/
theorem not_genTyPrefix_of_isAllowedName {n : String} (h : isAllowedName n = true) :
    ¬ (genTyPrefix.toList.isPrefixOf n.toList = true) := by
  simp only [isAllowedName_eq_toList, reservedNamePrefixes, List.any_cons, List.any_nil,
    Bool.or_false, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  simp only [h.1, Bool.false_eq_true, not_false_eq_true]

end Lambda

end -- public section

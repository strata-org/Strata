/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Str.LeanString

/-! # Properties of the conversions between Lean strings and code points

Key theorems: `toLeanString?_ofLeanString` and `ofLeanString_of_toLeanString?`, the two
round trips, and `scalar_ofLeanString`, which a front end for a language whose strings
are Lean's or Rust's uses to assume `scalar` of every string it reads. -/

@[expose] public section

namespace Strata.Str

/-- Every code point of a Lean string is a scalar value. -/
theorem scalar_ofLeanString (s : String) : scalar (ofLeanString s) = true := by
  simp only [scalar, ofLeanString, List.all_map, List.all_eq_true, Function.comp_apply]
  intro c _
  exact (isScalarValue_iff_isValidChar c.toNat).mpr c.valid

/-- `Char.ofNat` gives back a scalar value. -/
private theorem toNat_charOfNat {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, Char.ofNatAux, h]

/-- Reading a Lean string's code points back gives the string. -/
theorem toLeanString?_ofLeanString (s : String) : toLeanString? (ofLeanString s) = some s := by
  simp only [toLeanString?, scalar_ofLeanString, ↓reduceIte]
  rw [ofLeanString, List.map_map]
  have : (Char.ofNat ∘ Char.toNat) = id := by
    funext c
    simp [Char.ofNat_toNat]
  rw [this, List.map_id, String.ofList_toList]

/-- A code-point string that reads as a Lean string is that string's code points. -/
theorem ofLeanString_of_toLeanString? {cs : List Nat} {s : String}
    (h : toLeanString? cs = some s) : ofLeanString s = cs := by
  simp only [toLeanString?] at h
  split at h
  · rename_i hsc
    cases h
    simp only [ofLeanString, String.toList_ofList, List.map_map]
    rw [scalar_iff] at hsc
    conv => rhs; rw [← List.map_id cs]
    apply List.map_congr_left
    intro u hu
    simp only [Function.comp_apply, id]
    exact toNat_charOfNat ((isScalarValue_iff_isValidChar u).mp (hsc u hu))
  · cases h

end Strata.Str

end

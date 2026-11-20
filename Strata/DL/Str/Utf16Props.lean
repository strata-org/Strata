/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Str.Utf16

/-! # Properties of UTF-16 encoding and decoding

Key theorems: `encodeUtf16_decodeUtf16` (decoding then encoding is the identity on
every unit string), `decodeUtf16_injective`, `decodeUtf16_encodeUtf16` (encoding then
decoding is the identity on code-point strings with no high surrogate directly before a
low one), `decodeUtf16_encodeUtf16_pair` (the round trip that fails), and
`encodeUtf16_wf`. -/

@[expose] public section

namespace Strata.Str

/-- The empty string encodes to no units. -/
@[simp] theorem encodeUtf16_nil : encodeUtf16 [] = [] := rfl

/-- A code point's units come first, then the rest's. -/
@[simp] theorem encodeUtf16_cons (c : Nat) (cs : List Nat) :
    encodeUtf16 (c :: cs) = utf16Units c ++ encodeUtf16 cs := by
  simp [encodeUtf16]

/-- A surrogate pair encodes the code point its halves join to. -/
private theorem utf16Units_joinSurrogates {u v : Nat} (hu : isHighSurrogate u = true)
    (hv : isLowSurrogate v = true) : utf16Units (joinSurrogates u v) = [u, v] := by
  simp only [isHighSurrogate, isLowSurrogate, Bool.and_eq_true, decide_eq_true_eq] at hu hv
  unfold utf16Units joinSurrogates
  have hge : ¬ (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00) < 0x10000) := by omega
  have h1 : (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00) - 0x10000) / 0x400 = u - 0xD800 := by
    omega
  have h2 : (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00) - 0x10000) % 0x400 = v - 0xDC00 := by
    omega
  simp only [hge, ite_false, h1, h2, List.cons.injEq, and_true]
  omega

/-- A unit encodes to itself. -/
private theorem utf16Units_of_lt {u : Nat} (h : u < 0x10000) : utf16Units u = [u] := by
  simp [utf16Units, h]

/-- The units a code point at or above `0x10000` encodes to: a high surrogate, then a
    low one. -/
private theorem utf16Units_of_ge {c : Nat} (h : ¬ c < 0x10000) :
    utf16Units c = [0xD800 + (c - 0x10000) / 0x400, 0xDC00 + (c - 0x10000) % 0x400] := by
  simp [utf16Units, h]

/-- A non-empty unit string: its first element is below `0x10000`, and the rest is a unit string. -/
private theorem units_wf_cons_iff (u : Nat) (us : List Nat) :
    Carrier.units.wf (u :: us) = true ↔ u < 0x10000 ∧ Carrier.units.wf us = true := by
  rw [Carrier.wf_cons_iff, Carrier.bound]

/-- A non-empty code-point string: its first element is below `0x110000`, and the rest is a code-point string. -/
private theorem codePoints_wf_cons_iff (c : Nat) (cs : List Nat) :
    Carrier.codePoints.wf (c :: cs) = true ↔ c < 0x110000 ∧ Carrier.codePoints.wf cs = true := by
  rw [Carrier.wf_cons_iff, Carrier.bound]

/-- Joining the halves a code point at or above `0x10000` encodes to gives it back. -/
private theorem joinSurrogates_split {c : Nat} (h1 : ¬ c < 0x10000) (h2 : c < 0x110000) :
    joinSurrogates (0xD800 + (c - 0x10000) / 0x400) (0xDC00 + (c - 0x10000) % 0x400) = c := by
  unfold joinSurrogates
  omega

/-- Decoding units, then encoding the code points, gives the units back. -/
theorem encodeUtf16_decodeUtf16 :
    ∀ (us : List Nat), Carrier.units.wf us = true → encodeUtf16 (decodeUtf16 us) = us
  | [] => fun _ => rfl
  | [u] => fun h => by
    have hu := ((units_wf_cons_iff u []).mp h).1
    simp [decodeUtf16, utf16Units_of_lt hu]
  | u :: v :: rest => fun h => by
    obtain ⟨hu, h'⟩ := (units_wf_cons_iff u _).mp h
    obtain ⟨_, hrest⟩ := (units_wf_cons_iff v _).mp h'
    unfold decodeUtf16
    split
    · rename_i hpair
      simp only [Bool.and_eq_true] at hpair
      rw [encodeUtf16_cons, utf16Units_joinSurrogates hpair.1 hpair.2,
        encodeUtf16_decodeUtf16 rest hrest]
      rfl
    · rw [encodeUtf16_cons, utf16Units_of_lt hu, encodeUtf16_decodeUtf16 (v :: rest) h']
      rfl

/-- Two unit strings that decode to the same code points are equal. -/
theorem decodeUtf16_injective {us vs : List Nat} (hus : Carrier.units.wf us = true)
    (hvs : Carrier.units.wf vs = true) (h : decodeUtf16 us = decodeUtf16 vs) : us = vs := by
  rw [← encodeUtf16_decodeUtf16 us hus, ← encodeUtf16_decodeUtf16 vs hvs, h]

/-- The encoding of a code-point string starts with a low surrogate only when the
    string starts with that very code point: a code point at or above `0x10000`
    encodes to a high surrogate first. -/
private theorem encodeUtf16_head_low {c : Nat} {cs : List Nat} {e : Nat} {es : List Nat}
    (hc : c < 0x110000) (h : encodeUtf16 (c :: cs) = e :: es)
    (he : isLowSurrogate e = true) : e = c := by
  rw [encodeUtf16_cons] at h
  by_cases hsmall : c < 0x10000
  · rw [utf16Units_of_lt hsmall] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact h.1.symm
  · rw [utf16Units_of_ge hsmall] at h
    simp only [List.cons_append, List.cons.injEq] at h
    simp only [isLowSurrogate, Bool.and_eq_true, decide_eq_true_eq] at he
    omega

/-- Encoding a code-point string, then decoding the units, gives the code points back
    when no high surrogate is directly followed by a low one. -/
theorem decodeUtf16_encodeUtf16 :
    ∀ (cs : List Nat), Carrier.codePoints.wf cs = true → noPairing cs = true →
      decodeUtf16 (encodeUtf16 cs) = cs
  | [] => fun _ _ => rfl
  | c :: cs => fun hwf hnp => by
    obtain ⟨hc, hcs⟩ := (codePoints_wf_cons_iff c cs).mp hwf
    have hnp' : noPairing cs = true := by
      cases cs with
      | nil => rfl
      | cons d ds =>
        simp only [noPairing, Bool.and_eq_true] at hnp
        exact hnp.2
    have ih := decodeUtf16_encodeUtf16 cs hcs hnp'
    rw [encodeUtf16_cons]
    by_cases hsmall : c < 0x10000
    · rw [utf16Units_of_lt hsmall]
      cases he : encodeUtf16 cs with
      | nil =>
        rw [he] at ih
        simp only [List.cons_append, List.nil_append, decodeUtf16, ← ih]
      | cons e es =>
        rw [he] at ih
        simp only [List.cons_append, List.nil_append]
        unfold decodeUtf16
        split
        · rename_i hpair
          simp only [Bool.and_eq_true] at hpair
          exfalso
          cases cs with
          | nil => simp at he
          | cons d ds =>
            have hd := ((codePoints_wf_cons_iff d ds).mp hcs).1
            have hed := encodeUtf16_head_low hd he hpair.2
            subst hed
            simp only [noPairing, Bool.and_eq_true, hpair.1, hpair.2, Bool.and_self,
              Bool.not_true] at hnp
            exact Bool.false_ne_true hnp.1
        · rw [ih]
    · rw [utf16Units_of_ge hsmall]
      simp only [List.cons_append, List.nil_append]
      have hhi : isHighSurrogate (0xD800 + (c - 0x10000) / 0x400) = true := by
        simp only [isHighSurrogate, Bool.and_eq_true, decide_eq_true_eq]
        omega
      have hlo : isLowSurrogate (0xDC00 + (c - 0x10000) % 0x400) = true := by
        simp only [isLowSurrogate, Bool.and_eq_true, decide_eq_true_eq]
        omega
      have hj := joinSurrogates_split hsmall hc
      unfold decodeUtf16
      simp only [hhi, hlo, Bool.and_self, ite_true, hj, ih]

/-- The round trip through UTF-16 joins two lone surrogates into one code point. -/
theorem decodeUtf16_encodeUtf16_pair :
    decodeUtf16 (encodeUtf16 [0xD83D, 0xDE00]) = [0x1F600] := by
  rw [encodeUtf16_cons, encodeUtf16_cons, encodeUtf16_nil, utf16Units_of_lt (by omega),
    utf16Units_of_lt (by omega)]
  have hpair : (isHighSurrogate 0xD83D && isLowSurrogate 0xDE00) = true := rfl
  have hj : joinSurrogates 0xD83D 0xDE00 = 0x1F600 := rfl
  simp only [List.cons_append, List.nil_append, decodeUtf16, hpair, ite_true, hj]

/-- Every UTF-16 encoding is a unit string. -/
theorem encodeUtf16_wf {cs : List Nat} (h : Carrier.codePoints.wf cs = true) :
    Carrier.units.wf (encodeUtf16 cs) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨hc, hcs⟩ := (codePoints_wf_cons_iff c cs).mp h
    rw [encodeUtf16_cons, Carrier.wf_append, ih hcs, Bool.and_true]
    by_cases hsmall : c < 0x10000
    · rw [utf16Units_of_lt hsmall]
      exact (units_wf_cons_iff c []).mpr ⟨hsmall, rfl⟩
    · rw [utf16Units_of_ge hsmall]
      refine (units_wf_cons_iff _ _).mpr ⟨by omega, (units_wf_cons_iff _ _).mpr ⟨by omega, rfl⟩⟩

end Strata.Str

end

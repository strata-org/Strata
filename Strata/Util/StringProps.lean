/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.String
import all Strata.Util.String
import all Init.Data.Repr

/-!
# Properties of the `String` / `Nat` utilities

## Key theorems

* `Nat.toString_injective` — decimal `toString` on `Nat` is injective
* `listCharToNat?_roundtrip` — parsing the decimal digits of `n` recovers `n`
* `isPrefixOf_append_self` — a list is a prefix of itself appended with any suffix
* `hexVal_hexDigit` — reading back a hex digit recovers the value it names
* `isHexDigit_hexDigit` — every character `hexDigit` produces is a hex digit
* `char_toNat_lt` — every code point is below `0x110000`
* `hexDigit_isAlphanum` — a hex digit is alphanumeric
* `length_hexDigits`, `hexDigits_all_isHexDigit`, `mem_hexDigits` — the shape of a
  fixed-width hex body
* `hexValue_append_digit`, `hexValue_hexDigits` — reading a hex body back
-/

public section

theorem digitLoop_eq_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char),
    digitLoop fuel n ds = Nat.toDigitsCore 10 fuel n ds
  | 0, _, ds => by
    simp only [digitLoop]
    rw [Nat.toDigitsCore.eq_def]
  | fuel + 1, n, ds => by
    simp only [digitLoop]
    rw [Nat.toDigitsCore.eq_def]
    dsimp only []
    split
    · rfl
    · rw [digitLoop_eq_toDigitsCore]


theorem digitLoop_acc (fuel n : Nat) (ds : List Char) :
    digitLoop fuel n ds = digitLoop fuel n [] ++ ds := by
  induction fuel generalizing n ds with
  | zero => simp [digitLoop]
  | succ fuel ih =>
    simp only [digitLoop]; split
    · simp
    · rw [ih, ih (ds := [(n % 10).digitChar])]; simp [List.append_assoc]


theorem digitLoop_extra (fuel₁ fuel₂ n : Nat) (ds : List Char)
    (h₁ : fuel₁ > n) (h₂ : fuel₂ > n) :
    digitLoop fuel₁ n ds = digitLoop fuel₂ n ds := by
  induction n using Nat.strongRecOn generalizing fuel₁ fuel₂ ds with
  | _ n ih =>
    cases fuel₁ with
    | zero => omega
    | succ f₁ => cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        simp only [digitLoop]; split
        · rfl
        · exact ih (n / 10) (by omega) f₁ f₂ _ (by omega) (by omega)


theorem digitChar_val {n : Nat} (h : n < 10) :
    n.digitChar.toNat - '0'.toNat = n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide


theorem readBack_digitLoop (n : Nat) :
    List.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      (digitLoop (n + 1) n []) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    simp only [digitLoop]
    split
    · simp only [List.foldl]
      rw [digitChar_val (Nat.mod_lt n (by omega))]
      omega
    · rw [digitLoop_acc, List.foldl_append, List.foldl]
      rw [digitChar_val (Nat.mod_lt n (by omega))]
      rw [digitLoop_extra _ (n / 10 + 1) (n / 10) [] (by omega) (by omega)]
      rw [ih (n / 10) (by omega)]
      simp [List.foldl]
      omega


theorem toDigits_injective : Function.Injective (Nat.toDigits 10) := by
  intro a b h
  have ha := readBack_digitLoop a
  have hb := readBack_digitLoop b
  rw [Nat.toDigits.eq_def, Nat.toDigits.eq_def] at h
  rw [← digitLoop_eq_toDigitsCore, ← digitLoop_eq_toDigitsCore] at h
  rw [← h] at hb
  omega


/-- `toString` on `Nat` is injective (decimal representation is unique). -/
theorem Nat.toString_injective : Function.Injective (toString : Nat → String) := by
  intro a b h
  simp only [toString] at h
  rw [Nat.repr.eq_def, Nat.repr.eq_def] at h
  exact toDigits_injective (String.ofList_injective h)


/-! ### List-based prefix lemma -/

/-- A list is a prefix of itself appended with any suffix. -/
theorem isPrefixOf_append_self (pfx sfx : List Char) :
    pfx.isPrefixOf (pfx ++ sfx) = true := by
  rw [List.isPrefixOf_iff_prefix]
  exact List.prefix_append pfx sfx


/-! ### `listCharToNat?` roundtrip -/

theorem digitChar_is_digit (n : Nat) (h : n < 10) :
    '0' ≤ n.digitChar ∧ n.digitChar ≤ '9' := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by native_decide, by native_decide⟩


theorem listCharToNatAux_digits (acc : Nat) (cs : List Char)
    (h_digits : ∀ c, c ∈ cs → '0' ≤ c ∧ c ≤ '9') :
    listCharToNatAux acc cs = some (cs.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) acc) := by
  induction cs generalizing acc with
  | nil => simp [listCharToNatAux]
  | cons c cs ih =>
    simp only [listCharToNatAux, List.foldl_cons]
    have hc := h_digits c (List.mem_cons_self ..)
    simp [hc]
    exact ih _ (fun c' hc' => h_digits c' (List.mem_cons_of_mem c hc'))


theorem digitLoop_all_digits (fuel n : Nat) (ds : List Char)
    (h_ds : ∀ c, c ∈ ds → '0' ≤ c ∧ c ≤ '9') :
    ∀ c, c ∈ digitLoop fuel n ds → '0' ≤ c ∧ c ≤ '9' := by
  induction fuel generalizing n ds with
  | zero => simp [digitLoop]; exact h_ds
  | succ fuel ih =>
    simp only [digitLoop]
    split
    · intro c hc; simp at hc
      rcases hc with rfl | hc
      · exact digitChar_is_digit (n % 10) (Nat.mod_lt n (by omega))
      · exact h_ds c hc
    · exact ih _ _ (fun c hc => by
        simp at hc; rcases hc with rfl | hc
        · exact digitChar_is_digit (n % 10) (Nat.mod_lt n (by omega))
        · exact h_ds c hc)


theorem digitLoop_ne_nil (n : Nat) : digitLoop (n + 1) n [] ≠ [] := by
  simp only [digitLoop]
  split
  · simp
  · rw [digitLoop_acc]; simp


theorem toString_toList_eq (n : Nat) :
    (toString n).toList = digitLoop (n + 1) n [] := by
  simp only [toString, Nat.repr.eq_def, Nat.toDigits.eq_def, String.toList_ofList]
  exact (digitLoop_eq_toDigitsCore (n + 1) n []).symm


/-- Parsing the decimal representation of `n` back as a `Nat` recovers `n`. -/
theorem listCharToNat?_roundtrip (n : Nat) :
    listCharToNat? (toString n).toList = some n := by
  rw [toString_toList_eq]
  have h_ne := digitLoop_ne_nil n
  have h_digits := digitLoop_all_digits (n + 1) n [] (by simp)
  match h : digitLoop (n + 1) n [] with
  | [] => exact absurd h h_ne
  | c :: cs =>
    simp only [listCharToNat?]
    rw [listCharToNatAux_digits 0 (c :: cs)
      (fun c' hc' => by rw [← h] at hc'; exact h_digits c' hc')]
    congr 1
    have : List.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 (c :: cs) =
           List.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 (digitLoop (n + 1) n []) := by
      rw [h]
    rw [this]
    exact readBack_digitLoop n

/-! ### Hex digits -/

/-- `hexVal` inverts `hexDigit` on its range. -/
theorem hexVal_hexDigit (n : Nat) (h : n < 16) : hexVal (hexDigit n) = n := by
  match n, h with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
  | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
  | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
  | _ + 16, h => omega

/-- Everything `hexDigit` produces is recognized by `isHexDigit`, so a decoder that
    guards on it never rejects a digit an encoder emitted. -/
theorem isHexDigit_hexDigit (n : Nat) : isHexDigit (hexDigit n) = true := by
  unfold hexDigit
  split <;> decide

/-- Every character's code point is below `0x110000`, the bound Unicode sets, which
    is what makes six hex digits enough to name any character. -/
theorem char_toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have h : c.val.toNat < 0xd800 ∨ (0xdfff < c.val.toNat ∧ c.val.toNat < 0x110000) := c.valid
  show c.val.toNat < 0x110000
  rcases h with h | ⟨_, h⟩ <;> omega

/-- A hex digit is alphanumeric. -/
theorem hexDigit_isAlphanum (n : Nat) : (hexDigit n).isAlphanum = true := by
  unfold hexDigit
  split <;> decide

/-- `hexDigits` emits exactly `w` digits, which is what lets a decoder read a
    fixed-width body without a terminator. -/
theorem length_hexDigits (w n : Nat) : (hexDigits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [hexDigits, ih]

/-- Every digit `hexDigits` emits is one `isHexDigit` accepts, so a decoder that
    guards on it never rejects a body an encoder wrote. -/
theorem hexDigits_all_isHexDigit (w n : Nat) :
    (hexDigits w n).all isHexDigit = true := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [hexDigits, ih, isHexDigit_hexDigit]

/-- Every character of a hex body is one of the digits `hexDigit` produces, which
    is how a per-digit fact lifts to the whole body. -/
theorem mem_hexDigits (w n : Nat) {c : Char} (h : c ∈ hexDigits w n) :
    ∃ k, k < 16 ∧ c = hexDigit k := by
  induction w generalizing n with
  | zero => simp [hexDigits] at h
  | succ w ih =>
    simp [hexDigits] at h
    rcases h with h | h
    · exact ih _ h
    · exact ⟨n % 16, by omega, h⟩

/-- Extending a hex body by one digit multiplies the value read so far by sixteen
    and adds the new digit, which is what makes `hexValue` read a body
    most-significant digit first. -/
theorem hexValue_append_digit (l : List Char) (d : Char) :
    hexValue (l ++ [d]) = hexValue l * 16 + hexVal d := by
  simp [hexValue, List.foldl_append]

/-- `hexValue` inverts `hexDigits` on a value `w` digits can name. -/
theorem hexValue_hexDigits (w n : Nat) (h : n < 16 ^ w) :
    hexValue (hexDigits w n) = n := by
  induction w generalizing n with
  | zero =>
    have h0 : n = 0 := by simp at h; omega
    subst h0
    rfl
  | succ w ih =>
    have hpow : 16 ^ (w + 1) = 16 ^ w * 16 := by rw [Nat.pow_succ]
    have hlt : n / 16 < 16 ^ w := by omega
    have hd : hexVal (hexDigit (n % 16)) = n % 16 := hexVal_hexDigit _ (by omega)
    show hexValue (hexDigits w (n / 16) ++ [hexDigit (n % 16)]) = n
    rw [hexValue_append_digit, ih _ hlt, hd]
    omega

end

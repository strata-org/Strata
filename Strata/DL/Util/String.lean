/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Needed for Nat.toDigitsCore.eq_def, Nat.toDigits.eq_def, Nat.repr.eq_def
import all Init.Data.Repr

public section

/-! ## String / Nat Utilities

General-purpose definitions and lemmas for parsing and printing natural numbers
as decimal strings, and for `List.isPrefixOf` on `Char` lists.

These are used by the Lambda type-inference machinery (`LExprTypeEnv.lean`,
`LExprTypeSpec.lean`) but are not Lambda-specific.
-/

/-! ### Parsing: `listCharToNatAux` and `listCharToNat?` -/

/-- Parse a `List Char` of decimal digits as a natural number.
    Returns `none` for empty or non-digit input. -/
def listCharToNatAux : Nat → List Char → Option Nat
  | acc, [] => some acc
  | acc, c :: cs =>
    if '0' ≤ c ∧ c ≤ '9' then
      listCharToNatAux (acc * 10 + (c.toNat - '0'.toNat)) cs
    else none

/-- Parse a non-empty `List Char` of decimal digits as a natural number. -/
def listCharToNat? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ => listCharToNatAux 0 cs

/-! ### Printing: structurally recursive digit generation

`Nat.toDigitsCore` uses `brecOn` (bounded recursion on Nat), which is hard to
reason about directly. We define an equivalent structurally recursive version
and prove it equal to `Nat.toDigitsCore`. -/

def digitLoop : Nat → Nat → List Char → List Char
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    let d := (n % 10).digitChar
    let n' := n / 10
    if n' = 0 then d :: ds else digitLoop fuel n' (d :: ds)

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

end

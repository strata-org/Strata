/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Encoder

/-! ## Tests and proofs for Strata.Name.disambiguate / Strata.Name.breakDisambiguated -/

namespace Strata.SMT.Encoder

/-! ### Concrete roundtrip checks -/

#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "x" 1) == ("x", 2)
#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "x" 0) == ("x", 1)
#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "foo" 42) == ("foo", 43)
#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "$__bv0" 1) == ("$__bv0", 2)
-- Non-disambiguated names
#guard Strata.Name.breakDisambiguated "x" == ("x", 1)
#guard Strata.Name.breakDisambiguated "hello" == ("hello", 1)
-- Names with @ but no numeric suffix
#guard Strata.Name.breakDisambiguated "x@y" == ("x@y", 1)
-- Names with existing disambiguation
#guard Strata.Name.breakDisambiguated "x@1" == ("x", 2)

/-! ### Roundtrip proof -/

/-! #### Helper: digitChar properties -/

private theorem Nat.digitChar_val {n : Nat} (h : n < 10) :
    n.digitChar.toNat - '0'.toNat = n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem Nat.digitChar_isDigit {n : Nat} (h : n < 10) : n.digitChar.isDigit = true := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-! ### Structurally recursive digit generation

`Nat.toDigitsCore` uses `brecOn` (bounded recursion on Nat), which is hard to
reason about directly. We define an equivalent structurally recursive version
and prove it equal to `Nat.toDigitsCore`. -/

private def digitLoopFuel : Nat → Nat → List Char → List Char
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    let d := (n % 10).digitChar
    let n' := n / 10
    if n' = 0 then d :: ds else digitLoopFuel fuel n' (d :: ds)

private theorem digitLoopFuel_acc (fuel n : Nat) (ds : List Char) :
    digitLoopFuel fuel n ds = digitLoopFuel fuel n [] ++ ds := by
  induction fuel generalizing n ds with
  | zero => simp [digitLoopFuel]
  | succ fuel ih =>
    simp only [digitLoopFuel]; split
    · simp
    · rw [ih, ih (ds := [(n % 10).digitChar])]; simp [List.append_assoc]

private theorem digitLoopFuel_extra (fuel₁ fuel₂ n : Nat) (ds : List Char)
    (h₁ : fuel₁ > n) (h₂ : fuel₂ > n) :
    digitLoopFuel fuel₁ n ds = digitLoopFuel fuel₂ n ds := by
  induction n using Nat.strongRecOn generalizing fuel₁ fuel₂ ds with
  | _ n ih =>
    cases fuel₁ with
    | zero => omega
    | succ f₁ => cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        simp only [digitLoopFuel]; split
        · rfl
        · exact ih (n / 10) (by omega) f₁ f₂ _ (by omega) (by omega)

/-! ### Bridge: digitLoopFuel = Nat.toDigitsCore -/

theorem digitLoopFuel_eq_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char),
    digitLoopFuel fuel n ds = Nat.toDigitsCore 10 fuel n ds
  | 0, _, ds => by simp [digitLoopFuel, Nat.toDigitsCore]
  | fuel + 1, n, ds => by
    simp only [digitLoopFuel, Nat.toDigitsCore]; split
    · rfl
    · rw [digitLoopFuel_eq_toDigitsCore]

/-! ### All digits in Nat.repr are digit characters -/

private theorem digitLoopFuel_all_isDigit : ∀ (fuel n : Nat) (ds : List Char),
    ds.all Char.isDigit = true → (digitLoopFuel fuel n ds).all Char.isDigit = true
  | 0, _, _, hds => hds
  | fuel + 1, n, ds, hds => by
    simp only [digitLoopFuel]
    have hd := Nat.digitChar_isDigit (Nat.mod_lt n (by omega))
    split
    · simp [List.all_cons, hd, hds]
    · exact digitLoopFuel_all_isDigit fuel _ _ (by simp [List.all_cons, hd, hds])

theorem repr_digits_all_isDigit (n : Nat) :
    ∀ c ∈ n.repr.toList, c.isDigit = true := by
  rw [List.all_eq_true.symm, Nat.repr, String.toList_ofList, Nat.toDigits,
    ← digitLoopFuel_eq_toDigitsCore]
  exact digitLoopFuel_all_isDigit (n + 1) n [] (by simp)

/-! ### Reading back digits recovers the original number -/

private theorem readBack_digitLoopFuel (n : Nat) :
    List.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      (digitLoopFuel (n + 1) n []) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    simp only [digitLoopFuel]
    split
    · simp only [List.foldl]
      rw [Nat.digitChar_val (Nat.mod_lt n (by omega))]
      omega
    · rw [digitLoopFuel_acc, List.foldl_append, List.foldl]
      rw [Nat.digitChar_val (Nat.mod_lt n (by omega))]
      rw [digitLoopFuel_extra _ (n / 10 + 1) (n / 10) [] (by omega) (by omega)]
      rw [ih (n / 10) (by omega)]
      simp [List.foldl]
      omega

/-- `Strata.Name.digitsToNat` on the digits of `n` recovers `n`. -/
theorem digitsToNat_digitLoopFuel (n : Nat) :
    Strata.Name.digitsToNat (digitLoopFuel (n + 1) n []) = n :=
  readBack_digitLoopFuel n

/-- `Nat.repr n` is non-empty. -/
private theorem digitLoopFuel_ne_nil (n : Nat) : digitLoopFuel (n + 1) n [] ≠ [] := by
  simp only [digitLoopFuel]
  split
  · simp
  · rw [digitLoopFuel_acc]; simp

private theorem repr_toList_ne_nil (n : Nat) : n.repr.toList ≠ [] := by
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits, ← digitLoopFuel_eq_toDigitsCore]
  exact digitLoopFuel_ne_nil n

/-! ### Helper lemmas for the main roundtrip proof -/

private theorem List.takeWhile_eq_of_all {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) : List.takeWhile p xs = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.takeWhile, h x (.head xs), ih (fun y hy => h y (.tail x hy))]

private theorem List.dropWhile_eq_nil_of_all {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) : List.dropWhile p xs = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.dropWhile, h x (.head xs), ih (fun y hy => h y (.tail x hy))]

set_option linter.deprecated false in
private theorem String.mk_eq_ofList (cs : List Char) : String.mk cs = String.ofList cs := rfl

/-! ### Main roundtrip theorem -/

set_option linter.unusedSimpArgs false

/-- Breaking a disambiguated name recovers the base name and incremented suffix,
    provided the base name does not contain `@`. -/
theorem breakDisambiguated_disambiguate (baseName : String) (n : Nat)
    (_h : ¬ baseName.any (· == '@')) :
    Strata.Name.breakDisambiguated (Strata.Name.disambiguate baseName n) = (baseName, n + 1) := by
  simp only [Strata.Name.disambiguate, Strata.Name.breakDisambiguated,
    Strata.Name.digitsToNat,
    toString, String.toList_append,
    List.reverse_append, List.append_assoc]
  have hat : "@".toList.reverse = ['@'] := by native_decide
  rw [hat]
  have hdigrev : ∀ c ∈ n.repr.toList.reverse, Char.isDigit c = true :=
    fun c hc => repr_digits_all_isDigit n c (List.mem_reverse.mp hc)
  simp only [List.takeWhile_append, List.takeWhile_eq_of_all hdigrev,
    List.dropWhile_append, List.dropWhile_eq_nil_of_all hdigrev,
    List.isEmpty, List.dropWhile, List.takeWhile,
    show Char.isDigit '@' = false from by native_decide,
    ite_true, List.nil_append, List.reverse_reverse,
    show (false = true) = False from by simp,
    show (0 = 0 + 1) = False from by simp,
    ite_false, List.append_nil, List.cons_append]
  -- digitSuffix = n.repr.toList (non-empty), rest.reverse = '@' :: baseName.toList.reverse
  -- Match on ('@' :: _, _ :: _) succeeds since n.repr.toList is non-empty
  have hne : n.repr.toList ≠ [] := repr_toList_ne_nil n
  match h : n.repr.toList with
  | [] => exact absurd h hne
  | c :: cs =>
    simp only []
    -- Strata.Name.digitsToNat (c :: cs) = Strata.Name.digitsToNat n.repr.toList = n
    -- via digitLoopFuel bridge
    simp only [Strata.Name.digitsToNat,
      Nat.repr, String.toList_ofList, Nat.toDigits,
      ← digitLoopFuel_eq_toDigitsCore] at h
    rw [← h, readBack_digitLoopFuel]
    simp only [List.reverse_cons, List.reverse_reverse, List.dropLast_concat,
      String.mk_eq_ofList, String.ofList_toList]

end Strata.SMT.Encoder

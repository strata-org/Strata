/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.RealProps

/-! # `Strata.Util.Real` tests

Checks that the field and order instances let `grind` reason about `Real`, that completeness
gives a square root of `2` (so `Real` differs from `Rat`), and that the main results use only
Lean's standard axioms (no `sorryAx`).
-/

namespace Strata.Util.Real.Test

open Strata.Util Lean.Grind.OrderedRing

-- Ring identities.
example (a b : Real) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by grind

-- Linear arithmetic over the order.
example (a b c : Real) (h₁ : a < b) (h₂ : b ≤ c) : a + 1 < c + 1 := by grind

-- Field reasoning with a nonzero divisor.
example (a : Real) (h : a ≠ 0) : a / a = 1 := by grind

-- The rationals embed into the reals, including division.
example : Real.ofRat (1 / 2) = 1 / 2 := by
  rw [Real.ofRat_div]
  rfl

-- The rationals embed into the reals.
example : Real.ofRat (1 / 2) + Real.ofRat (1 / 2) = 1 := by
  rw [← Real.ofRat_add]
  show Real.ofRat _ = Real.ofRat 1
  rw [Real.ofRat_inj]
  grind

/-- Some real number squares to `2`, which no rational does. The proof uses only the public API
of `Strata.Util.RealProps`. -/
theorem exists_sq_eq_two : ∃ x : Real, x * x = 2 := by
  obtain ⟨s, hub, hleast⟩ := Real.exists_isLUB (fun x => x * x < 2) ⟨1, by grind⟩
    ⟨2, fun x hx => by
      apply Classical.byContradiction
      intro hx2
      have h1 : (2 : Real) < x := by grind
      have h2 : 2 * x < x * x := mul_lt_mul_of_pos_right h1 (by grind)
      grind⟩
  have hs1 : 1 ≤ s := hub 1 (by grind)
  have hs2 : s ≤ 2 := hleast 2 fun x hx => by
    apply Classical.byContradiction
    intro hx2
    have h1 : (2 : Real) < x := by grind
    have h2 : 2 * x < x * x := mul_lt_mul_of_pos_right h1 (by grind)
    grind
  have hss : 0 ≤ s * s := mul_nonneg (by grind) (by grind)
  refine ⟨s, ?_⟩
  rcases Real.lt_trichotomy (s * s) 2 with hlt | heq | hgt
  · -- `s + h` is in the set for a small `h > 0`, contradicting that `s` is an upper bound.
    exfalso
    have hh : 0 < (2 - s * s) / 6 := by grind
    have hh1 : (2 - s * s) / 6 ≤ 1 := by grind
    have k1 : s * ((2 - s * s) / 6) ≤ 2 * ((2 - s * s) / 6) :=
      mul_le_mul_of_nonneg_right hs2 (by grind)
    have k2 : (2 - s * s) / 6 * ((2 - s * s) / 6) ≤ 1 * ((2 - s * s) / 6) :=
      mul_le_mul_of_nonneg_right hh1 (by grind)
    have hmem := hub (s + (2 - s * s) / 6) (by grind)
    grind
  · exact heq
  · -- `s - h` is still an upper bound for a small `h > 0`, contradicting that `s` is least.
    exfalso
    have hh : 0 < (s * s - 2) / 4 := by grind
    have hs4 : s * s ≤ 2 * 2 := by
      have hss2 := mul_le_mul_of_nonneg_right hs2 (show (0 : Real) ≤ s by grind)
      have h2s := mul_le_mul_of_nonneg_left hs2 (show (0 : Real) ≤ 2 by grind)
      grind
    have k1 : s * ((s * s - 2) / 4) ≤ 2 * ((s * s - 2) / 4) :=
      mul_le_mul_of_nonneg_right hs2 (by grind)
    have k2 : 0 < (s * s - 2) / 4 * ((s * s - 2) / 4) := mul_pos hh hh
    have hub' := hleast (s - (s * s - 2) / 4) fun x hx => by
      apply Classical.byContradiction
      intro hx'
      have h1 : s - (s * s - 2) / 4 < x := by grind
      have h2 : 0 < s - (s * s - 2) / 4 := by grind
      have k3 : (s - (s * s - 2) / 4) * (s - (s * s - 2) / 4) < x * (s - (s * s - 2) / 4) :=
        mul_lt_mul_of_pos_right h1 h2
      have k4 : x * (s - (s * s - 2) / 4) < x * x := mul_lt_mul_of_pos_left h1 (by grind)
      grind
    grind

/--
info: 'Strata.Util.Real.exists_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.exists_isLUB

/--
info: 'Strata.Util.Real.instField' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.instField

/--
info: 'Strata.Util.Real.instOrderedRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.instOrderedRing

/--
info: 'Strata.Util.Real.exists_rat_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.exists_rat_gt

/--
info: 'Strata.Util.Real.exists_rat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.exists_rat_lt

/--
info: 'Strata.Util.Real.exists_pos_rat_lt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.exists_pos_rat_lt

/--
info: 'Strata.Util.Real.lt_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.lt_trichotomy

/--
info: 'Strata.Util.Real.ofRat_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.ofRat_inj

/--
info: 'Strata.Util.Real.ofRat_lt_ofRat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.ofRat_lt_ofRat

/--
info: 'Strata.Util.Real.ofRat_le_ofRat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.ofRat_le_ofRat

/--
info: 'Strata.Util.Real.ofRat_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.ofRat_inv

/--
info: 'Strata.Util.Real.ofRat_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.ofRat_div

/--
info: 'Strata.Util.Real.instIsLinearOrder'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.instIsLinearOrder

/--
info: 'Strata.Util.Real.instOrderedAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.instOrderedAdd

/--
info: 'Strata.Util.Real.instLawfulOrderLT'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.instLawfulOrderLT

end Strata.Util.Real.Test

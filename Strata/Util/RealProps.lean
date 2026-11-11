/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.Real
import all Strata.Util.Real

/-! # Laws of the real numbers

The real numbers `Strata.Util.Real` form a complete linearly ordered field. Key results:

* `Real.instField`: the field laws, as an instance of `Lean.Grind.Field`;
* `Real.instIsLinearOrder`, `Real.instLawfulOrderLT`, `Real.instOrderedAdd`,
  `Real.instOrderedRing`: `≤` is a linear order compatible with `+` and `*`;
* `Real.exists_isLUB`: every nonempty set of reals with an upper bound has a least upper bound;
* `Real.lt_trichotomy`: any two reals satisfy at least one of `a < b`, `a = b`, `b < a`;
* `Real.exists_rat_gt`, `Real.exists_rat_lt`, `Real.exists_pos_rat_lt`: every real lies strictly
  between two rationals (the Archimedean property), and every positive real is above some
  positive rational;
* `Real.ofRat_add`, `Real.ofRat_neg`, `Real.ofRat_mul`, `Real.ofRat_sub`, `Real.ofRat_inv`,
  `Real.ofRat_div`, `Real.ofRat_natCast`, `Real.ofRat_intCast`, `Real.ofRat_inj`,
  `Real.ofRat_lt_ofRat`, `Real.ofRat_le_ofRat`: the rationals embed into the reals, preserving
  arithmetic and order;
* `Real.add_zero`, `Real.add_comm`, `Real.add_assoc`, `Real.neg_add_cancel`, `Real.mul_comm`,
  `Real.mul_assoc`, `Real.mul_one`, `Real.one_mul`, `Real.mul_zero`, `Real.zero_mul`,
  `Real.mul_add`, `Real.add_mul`, `Real.zero_ne_one`, `Real.inv_zero`, `Real.mul_inv_cancel`,
  `Real.zpow_neg`: the individual field laws, used to build `Real.instField`;
* `Real.exists_mk`, `Real.mk_eq_mk`, `Real.mk_add`, `Real.mk_neg`, `Real.mk_mul`, `Real.mk_lt_mk`:
  working with a real number through a Cauchy sequence that names it.

The remaining order and field laws are private; use them through the instances. With these
instances, `grind` proves linear arithmetic facts and ring identities about `Real`.
-/

public section

namespace Strata.Util

/-! ## Rational helpers -/

/-- `e ≤ |a|` exactly when `e ≤ a` or `a ≤ -e`. -/
private theorem rat_le_abs_iff {a e : Rat} : e ≤ a.abs ↔ e ≤ a ∨ a ≤ -e := by
  unfold Rat.abs; split <;> grind

/-- For positive rationals `a ≤ b`, the reciprocals satisfy `1 / b ≤ 1 / a`. -/
private theorem rat_inv_le_inv {a b : Rat} (ha : 0 < a) (hab : a ≤ b) : 1 / b ≤ 1 / a := by
  have hb : 0 < b := by grind
  have h0 : 0 ≤ 1 / b := Rat.le_of_lt (rat_div_pos (by decide) hb)
  have h1 : 1 / b * a ≤ 1 / b * b := Rat.mul_le_mul_of_nonneg_left hab h0
  have h2 : 1 / b * b = 1 := by grind
  have h3 : 0 ≤ 1 / a := Rat.le_of_lt (rat_div_pos (by decide) ha)
  have h4 : 1 / b * a * (1 / a) ≤ 1 * (1 / a) := Rat.mul_le_mul_of_nonneg_right (by grind) h3
  have h5 : 1 / b * a * (1 / a) = 1 / b := by grind
  grind

/-- If a rational `c` has `δ ≤ |c|` for some `δ > 0`, then `|c⁻¹| ≤ 1 / δ`. -/
private theorem rat_abs_inv_le {c δ : Rat} (hδ : 0 < δ) (h : δ ≤ c.abs) :
    c⁻¹.abs ≤ 1 / δ := by
  have hc : c ≠ 0 := fun e => by subst e; rw [Rat.abs_zero] at h; grind
  have h1 : c⁻¹.abs * c.abs = 1 := by
    rw [← rat_abs_mul, Rat.inv_mul_cancel c hc]; rfl
  have h2 : c⁻¹.abs = 1 / c.abs := by
    have hc0 : c.abs ≠ 0 := by grind
    grind
  rw [h2]
  exact rat_inv_le_inv hδ h

/-- Every rational is below some natural number. -/
private theorem rat_exists_nat_gt (x : Rat) : ∃ n : Nat, x < n := by
  refine ⟨x.ceil.toNat + 1, ?_⟩
  have h1 := Rat.le_ceil (x := x)
  have h2 : ((x.ceil.toNat : Int) : Rat) = (x.ceil.toNat : Rat) := Rat.intCast_natCast _
  have h3 := Rat.intCast_le_intCast.mpr (Int.self_le_toNat x.ceil)
  rw [Rat.natCast_add]
  grind

/-- For every positive rational `ε` there is a natural number `N` with `1 / (N + 1) < ε`. -/
private theorem rat_exists_inv_succ_lt {ε : Rat} (hε : 0 < ε) :
    ∃ N : Nat, 1 / ((N : Rat) + 1) < ε := by
  obtain ⟨n, hn⟩ := rat_exists_nat_gt (1 / ε)
  have h1 : 1 < (n : Rat) * ε := (Rat.div_lt_iff hε).mp hn
  have hn0 : (0 : Rat) ≤ n := Rat.natCast_nonneg
  refine ⟨n, (Rat.div_lt_iff (by grind)).mpr ?_⟩
  grind

/-- Two rationals whose distance is below every positive rational are equal. -/
private theorem rat_eq_of_abs_lt {a b : Rat} (h : ∀ ε : Rat, 0 < ε → (a - b).abs < ε) :
    a = b := by
  apply Decidable.byContradiction
  intro hne
  have hpos : 0 < (a - b).abs := Rat.abs_pos_iff.mpr (by grind)
  exact Rat.lt_irrefl (h _ hpos)

/-- If some natural number satisfies `P`, then a least one does: it satisfies `P` and no
smaller number does. -/
private theorem nat_exists_min {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ n m, m < n → ¬ P m := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm hPm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h' | h'
      · exact ih m h' hPm
      · subst h'; exact hno ⟨m, hPm, ih⟩
  obtain ⟨n, hn⟩ := h
  exact key (n + 1) n (Nat.lt_succ_self n) hn

/-! ## Cauchy sequences -/

namespace CauchySeq

/-- Two Cauchy sequences whose terms agree from index `N` on are equivalent. -/
private theorem equiv_of_eventually_eq {x y : CauchySeq} (N : Nat)
    (h : ∀ n, N ≤ n → x.seq n = y.seq n) : Equiv x y := by
  intro ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [h n hn, rat_abs_lt_iff]
  grind

/-- If the terms of `y` are at least those of `x` from index `N` on and `x` is positive,
then `y` is positive. -/
private theorem pos_of_eventually_le {x y : CauchySeq} (N : Nat)
    (h : ∀ n, N ≤ n → x.seq n ≤ y.seq n) (hx : Pos x) : Pos y := by
  obtain ⟨δ, hδ, M, hM⟩ := hx
  exact ⟨δ, hδ, max N M, fun n hn => Rat.le_trans (hM n (by omega)) (h n (by omega))⟩

/-- A Cauchy sequence is positive, equivalent to `0`, or negative. -/
private theorem trichotomy (x : CauchySeq) : Pos x ∨ Equiv x (const 0) ∨ Pos (-x) := by
  by_cases h0 : Equiv x (const 0)
  · exact Or.inr (Or.inl h0)
  have hfar : ∃ ε, 0 < ε ∧ ∀ N, ∃ n, N ≤ n ∧ ε ≤ (x.seq n).abs := by
    apply Classical.byContradiction
    intro hno
    apply h0
    intro ε hε
    apply Classical.byContradiction
    intro hN
    apply hno
    refine ⟨ε, hε, fun N => ?_⟩
    apply Classical.byContradiction
    intro hn
    apply hN
    refine ⟨N, fun n hn' => ?_⟩
    show (x.seq n - 0).abs < ε
    have e : x.seq n - 0 = x.seq n := by grind
    rw [e]
    exact Rat.not_le.mp (fun hle => hn ⟨n, hn', hle⟩)
  obtain ⟨ε, hε, hfar⟩ := hfar
  obtain ⟨N, hN⟩ := x.cauchy (ε / 2) (by grind)
  obtain ⟨n, hn, hle⟩ := hfar N
  rcases rat_le_abs_iff.mp hle with h | h
  · refine Or.inl ⟨ε / 2, by grind, N, fun m hm => ?_⟩
    have hmn := hN m n hm hn
    rw [rat_abs_lt_iff] at hmn
    grind
  · refine Or.inr (Or.inr ⟨ε / 2, by grind, N, fun m hm => ?_⟩)
    have hmn := hN m n hm hn
    rw [rat_abs_lt_iff] at hmn
    show ε / 2 ≤ -x.seq m
    grind

end CauchySeq

/-! ## Representatives -/

namespace Real

open CauchySeq

/-- Every real number is named by some Cauchy sequence. -/
theorem exists_mk (a : Real) : ∃ x, mk x = a := Quotient.exists_rep a

/-- Two sequences name the same real number exactly when they are equivalent. -/
theorem mk_eq_mk {x y : CauchySeq} : mk x = mk y ↔ Equiv x y :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- Addition is termwise on representatives. -/
theorem mk_add (x y : CauchySeq) : mk x + mk y = mk (x + y) := rfl

/-- Negation is termwise on representatives. -/
theorem mk_neg (x : CauchySeq) : -mk x = mk (-x) := rfl

/-- Multiplication is termwise on representatives. -/
theorem mk_mul (x y : CauchySeq) : mk x * mk y = mk (x * y) := rfl

/-- `mk x < mk y` exactly when the sequence `y - x` is positive. -/
theorem mk_lt_mk {x y : CauchySeq} : mk x < mk y ↔ Pos (y + -x) := Iff.rfl

/-- Two Cauchy sequences with equal terms at every index name the same real number. -/
private theorem mk_eq_of_seq {x y : CauchySeq} (h : ∀ n, x.seq n = y.seq n) : mk x = mk y :=
  Quotient.sound (equiv_of_eventually_eq 0 (fun n _ => h n))

/-! ## Ring laws -/

/-- `0` is a right identity for addition. -/
protected theorem add_zero (a : Real) : a + 0 = a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  exact mk_eq_of_seq fun _ => Rat.add_zero _

/-- Addition is commutative. -/
protected theorem add_comm (a b : Real) : a + b = b + a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  exact mk_eq_of_seq fun _ => Rat.add_comm _ _

/-- Addition is associative. -/
protected theorem add_assoc (a b c : Real) : a + b + c = a + (b + c) := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨z, rfl⟩ := exists_mk c
  exact mk_eq_of_seq fun _ => Rat.add_assoc _ _ _

/-- `-a` is a left inverse of `a` for addition. -/
protected theorem neg_add_cancel (a : Real) : -a + a = 0 := by
  obtain ⟨x, rfl⟩ := exists_mk a
  exact mk_eq_of_seq fun _ => Rat.neg_add_cancel _

/-- Multiplication is commutative. -/
protected theorem mul_comm (a b : Real) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  exact mk_eq_of_seq fun _ => Rat.mul_comm _ _

/-- Multiplication is associative. -/
protected theorem mul_assoc (a b c : Real) : a * b * c = a * (b * c) := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨z, rfl⟩ := exists_mk c
  exact mk_eq_of_seq fun _ => Rat.mul_assoc _ _ _

/-- `1` is a right identity for multiplication. -/
protected theorem mul_one (a : Real) : a * 1 = a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  exact mk_eq_of_seq fun _ => Rat.mul_one _

/-- `1` is a left identity for multiplication. -/
protected theorem one_mul (a : Real) : 1 * a = a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  exact mk_eq_of_seq fun _ => Rat.one_mul _

/-- `0` is right absorbing for multiplication. -/
protected theorem mul_zero (a : Real) : a * 0 = 0 := by
  obtain ⟨x, rfl⟩ := exists_mk a
  exact mk_eq_of_seq fun _ => Rat.mul_zero _

/-- `0` is left absorbing for multiplication. -/
protected theorem zero_mul (a : Real) : 0 * a = 0 := by
  obtain ⟨x, rfl⟩ := exists_mk a
  exact mk_eq_of_seq fun _ => Rat.zero_mul _

/-- Multiplication distributes over addition on the left. -/
protected theorem mul_add (a b c : Real) : a * (b + c) = a * b + a * c := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨z, rfl⟩ := exists_mk c
  exact mk_eq_of_seq fun _ => Rat.mul_add _ _ _

/-- Multiplication distributes over addition on the right. -/
protected theorem add_mul (a b c : Real) : (a + b) * c = a * c + b * c := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨z, rfl⟩ := exists_mk c
  exact mk_eq_of_seq fun _ => Rat.add_mul _ _ _

/-- Negation commutes with multiplication on the left. -/
private theorem neg_mul (a b : Real) : -a * b = -(a * b) := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  exact mk_eq_of_seq fun _ => Rat.neg_mul _ _

/-! ## The embedding of the rationals -/

/-- `ofRat` preserves addition. -/
theorem ofRat_add (a b : Rat) : ofRat (a + b) = ofRat a + ofRat b := rfl

/-- `ofRat` preserves negation. -/
theorem ofRat_neg (a : Rat) : ofRat (-a) = -ofRat a := rfl

/-- `ofRat` preserves multiplication. -/
theorem ofRat_mul (a b : Rat) : ofRat (a * b) = ofRat a * ofRat b := rfl

/-- `ofRat` preserves subtraction. -/
theorem ofRat_sub (a b : Rat) : ofRat (a - b) = ofRat a - ofRat b :=
  mk_eq_of_seq fun _ => Rat.sub_eq_add_neg _ _

/-- A natural number cast to `Real` is `ofRat` of its cast to `Rat`. -/
theorem ofRat_natCast (n : Nat) : ofRat (n : Rat) = (n : Real) := rfl

/-- An integer cast to `Real` is `ofRat` of its cast to `Rat`. -/
theorem ofRat_intCast (i : Int) : ofRat (i : Rat) = (i : Real) := rfl

/-- `ofRat` is injective. -/
theorem ofRat_inj {a b : Rat} : ofRat a = ofRat b ↔ a = b := by
  refine ⟨fun h => rat_eq_of_abs_lt fun ε hε => ?_, fun h => h ▸ rfl⟩
  obtain ⟨N, hN⟩ := mk_eq_mk.mp h ε hε
  exact hN N (Nat.le_refl N)

/-- `0` and `1` are different real numbers. -/
protected theorem zero_ne_one : (0 : Real) ≠ 1 := fun h => by
  have h01 := ofRat_inj.mp h
  contradiction

/-- `Real` is a commutative ring. -/
instance instCommRing : Lean.Grind.CommRing Real where
  add_zero := Real.add_zero
  add_comm := Real.add_comm
  add_assoc := Real.add_assoc
  mul_assoc := Real.mul_assoc
  mul_one := Real.mul_one
  one_mul := Real.one_mul
  left_distrib := Real.mul_add
  right_distrib := Real.add_mul
  zero_mul := Real.zero_mul
  mul_zero := Real.mul_zero
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    show ofRat _ = ofRat _ + ofRat _
    rw [← ofRat_add, Lean.Grind.Semiring.ofNat_succ (α := Rat)]
  ofNat_eq_natCast n := by
    show ofRat _ = ofRat _
    rw [Lean.Grind.Semiring.ofNat_eq_natCast (α := Rat)]
  nsmul_eq_natCast_mul _ _ := rfl
  neg_add_cancel := Real.neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := by
    show ofRat _ * a = -(ofRat _ * a)
    rw [Lean.Grind.Ring.intCast_neg (α := Rat), ofRat_neg, Real.neg_mul]
  zsmul_natCast_eq_nsmul n a := by
    show ofRat _ * a = ofRat _ * a
    rw [Rat.intCast_natCast]
  intCast_ofNat n := by
    show ofRat _ = ofRat _
    rw [Lean.Grind.Ring.intCast_ofNat (α := Rat)]
  intCast_neg i := by
    show ofRat _ = -ofRat _
    rw [Lean.Grind.Ring.intCast_neg (α := Rat), ofRat_neg]
  mul_comm := Real.mul_comm

/-! ## Order -/

/-- `<` is irreflexive. -/
private theorem lt_irrefl (a : Real) : ¬ a < a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  intro ⟨δ, hδ, N, hN⟩
  have hδ0 : δ ≤ x.seq N + -x.seq N := hN N (Nat.le_refl N)
  grind

/-- `<` is transitive. -/
private theorem lt_trans {a b c : Real} (hab : a < b) (hbc : b < c) : a < c := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨z, rfl⟩ := exists_mk c
  obtain ⟨δ₁, h₁, N₁, k₁⟩ := hab
  obtain ⟨δ₂, h₂, N₂, k₂⟩ := hbc
  refine ⟨δ₁ + δ₂, by grind, max N₁ N₂, fun n hn => ?_⟩
  have a : δ₁ ≤ y.seq n + -x.seq n := k₁ n (by omega)
  have b : δ₂ ≤ z.seq n + -y.seq n := k₂ n (by omega)
  show δ₁ + δ₂ ≤ z.seq n + -x.seq n
  grind

/-- Any two real numbers satisfy at least one of `a < b`, `a = b`, `b < a`. -/
theorem lt_trichotomy (a b : Real) : a < b ∨ a = b ∨ b < a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  rcases trichotomy (y + -x) with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl (mk_eq_mk.mpr fun ε hε => ?_))
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    have k : (y.seq n + -x.seq n - 0).abs < ε := hN n hn
    rw [rat_abs_lt_iff] at k ⊢
    grind
  · refine Or.inr (Or.inr (pos_of_eventually_le 0 (fun n _ => ?_) h))
    show -(y.seq n + -x.seq n) ≤ x.seq n + -y.seq n
    grind

/-- `a ≤ b` when `b < a` fails. -/
private theorem le_of_not_lt {a b : Real} (h : ¬ b < a) : a ≤ b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · exact absurd h' h

/-- Adding the same number on the right preserves `<`. -/
private theorem add_lt_add_right {a b : Real} (h : a < b) (c : Real) : a + c < b + c := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨z, rfl⟩ := exists_mk c
  refine pos_of_eventually_le 0 (fun n _ => ?_) h
  show y.seq n + -x.seq n ≤ y.seq n + z.seq n + -(x.seq n + z.seq n)
  grind

/-- `0 < b - a` exactly when `a < b`. -/
private theorem sub_pos {a b : Real} : 0 < b - a ↔ a < b := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  constructor
  · refine pos_of_eventually_le 0 (fun n _ => ?_)
    show y.seq n + -x.seq n + -0 ≤ y.seq n + -x.seq n
    grind
  · refine pos_of_eventually_le 0 (fun n _ => ?_)
    show y.seq n + -x.seq n ≤ y.seq n + -x.seq n + -0
    grind

/-- The product of two positive numbers is positive. -/
private theorem mul_pos {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨y, rfl⟩ := exists_mk b
  obtain ⟨δ₁, h₁, N₁, k₁⟩ := ha
  obtain ⟨δ₂, h₂, N₂, k₂⟩ := hb
  refine ⟨δ₁ * δ₂, Rat.mul_pos h₁ h₂, max N₁ N₂, fun n hn => ?_⟩
  have a : δ₁ ≤ x.seq n + -0 := k₁ n (by omega)
  have b : δ₂ ≤ y.seq n + -0 := k₂ n (by omega)
  have c : δ₁ * δ₂ ≤ x.seq n * δ₂ := Rat.mul_le_mul_of_nonneg_right (by grind) (by grind)
  have d : x.seq n * δ₂ ≤ x.seq n * y.seq n := Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
  show δ₁ * δ₂ ≤ x.seq n * y.seq n + -0
  grind

/-- Multiplying on the left by a positive number preserves `<`. -/
private theorem mul_lt_mul_of_pos_left {a b c : Real} (h : a < b) (hc : 0 < c) :
    c * a < c * b := by
  rw [← Real.sub_pos] at h ⊢
  have e : c * b - c * a = c * (b - a) := by grind
  rw [e]
  exact Real.mul_pos hc h

/-- Multiplying on the right by a positive number preserves `<`. -/
private theorem mul_lt_mul_of_pos_right {a b c : Real} (h : a < b) (hc : 0 < c) :
    a * c < b * c := by
  rw [Real.mul_comm a, Real.mul_comm b]
  exact Real.mul_lt_mul_of_pos_left h hc

/-- `≤` is a linear order. -/
instance instIsLinearOrder : Std.IsLinearOrder Real where
  le_refl _ := Or.inr rfl
  le_trans _ _ _ hab hbc := by
    rcases hab with h | rfl <;> rcases hbc with h' | rfl
    · exact Or.inl (Real.lt_trans h h')
    · exact Or.inl h
    · exact Or.inl h'
    · exact Or.inr rfl
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · rcases hba with h' | h'
      · exact absurd (Real.lt_trans h h') (Real.lt_irrefl a)
      · exact h'.symm
    · exact h
  le_total a b := by
    rcases lt_trichotomy a b with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- `<` is the strict version of `≤`. -/
instance instLawfulOrderLT : Std.LawfulOrderLT Real where
  lt_iff a b := by
    refine ⟨fun h => ⟨Or.inl h, fun h' => ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
    · rcases h' with h' | h'
      · exact Real.lt_irrefl a (Real.lt_trans h h')
      · subst h'; exact Real.lt_irrefl _ h
    · rcases h₁ with h₁ | h₁
      · exact h₁
      · exact absurd (Or.inr h₁.symm) h₂

/-- Adding the same number preserves `≤`, in both directions. -/
instance instOrderedAdd : Lean.Grind.OrderedAdd Real where
  add_le_left_iff {a b} c := by
    constructor
    · rintro (h | rfl)
      · exact Or.inl (Real.add_lt_add_right h c)
      · exact Or.inr rfl
    · rintro (h | h)
      · have k := Real.add_lt_add_right h (-c)
        have e₁ : a + c + -c = a := by grind
        have e₂ : b + c + -c = b := by grind
        rw [e₁, e₂] at k
        exact Or.inl k
      · have k := congrArg (· + -c) h
        have e₁ : a + c + -c = a := by grind
        have e₂ : b + c + -c = b := by grind
        simp only [e₁, e₂] at k
        exact Or.inr k

/-- `Real` is an ordered ring. -/
instance instOrderedRing : Lean.Grind.OrderedRing Real where
  zero_lt_one := ⟨1, by decide, 0, fun _ _ => by
    show (1 : Rat) ≤ 1 + -0
    grind⟩
  mul_lt_mul_of_pos_left := Real.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := Real.mul_lt_mul_of_pos_right

/-! ## Inverses -/

/-- Every nonzero real number has a multiplicative inverse. -/
private theorem exists_mul_eq_one {a : Real} (ha : a ≠ 0) : ∃ b, a * b = 1 := by
  obtain ⟨x, rfl⟩ := exists_mk a
  have hfar : ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ (x.seq n).abs := by
    rcases trichotomy x with ⟨δ, hδ, N, h⟩ | h | ⟨δ, hδ, N, h⟩
    · exact ⟨δ, hδ, N, fun n hn => rat_le_abs_iff.mpr (Or.inl (h n hn))⟩
    · exact absurd (mk_eq_mk.mpr h) ha
    · refine ⟨δ, hδ, N, fun n hn => rat_le_abs_iff.mpr (Or.inr ?_)⟩
      have hneg : δ ≤ -x.seq n := h n hn
      grind
  obtain ⟨δ, hδ, N, hN⟩ := hfar
  have hne : ∀ n, N ≤ n → x.seq n ≠ 0 := fun n hn e => by
    have hδ0 := hN n hn
    rw [e, Rat.abs_zero] at hδ0
    grind
  have hc : IsCauchy (fun n => (x.seq n)⁻¹) := by
    intro ε hε
    have hD : 0 < 1 / δ := rat_div_pos (by decide) hδ
    obtain ⟨N', hN'⟩ := x.cauchy (ε * δ * δ) (Rat.mul_pos (Rat.mul_pos hε hδ) hδ)
    refine ⟨max N N', fun m n hm hn => ?_⟩
    have hm0 := hne m (by omega)
    have hn0 := hne n (by omega)
    have e : (x.seq m)⁻¹ - (x.seq n)⁻¹ =
        (x.seq n - x.seq m) * ((x.seq m)⁻¹ * (x.seq n)⁻¹) := by grind
    rw [e, rat_abs_mul, rat_abs_mul]
    have h1 : (x.seq n - x.seq m).abs < ε * δ * δ := hN' n m (by omega) (by omega)
    have h2 := rat_abs_inv_le hδ (hN m (by omega))
    have h3 := rat_abs_inv_le hδ (hN n (by omega))
    have hQ : (x.seq m)⁻¹.abs * (x.seq n)⁻¹.abs ≤ 1 / δ * (1 / δ) :=
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h2 Rat.abs_nonneg)
        (Rat.mul_le_mul_of_nonneg_left h3 (Rat.le_of_lt hD))
    have k1 : (x.seq n - x.seq m).abs * ((x.seq m)⁻¹.abs * (x.seq n)⁻¹.abs) ≤
        (x.seq n - x.seq m).abs * (1 / δ * (1 / δ)) :=
      Rat.mul_le_mul_of_nonneg_left hQ Rat.abs_nonneg
    have k2 : (x.seq n - x.seq m).abs * (1 / δ * (1 / δ)) < ε * δ * δ * (1 / δ * (1 / δ)) :=
      Rat.mul_lt_mul_of_pos_right h1 (Rat.mul_pos hD hD)
    have k3 : ε * δ * δ * (1 / δ * (1 / δ)) = ε := by grind
    grind
  exact ⟨mk ⟨_, hc⟩,
    Quotient.sound (equiv_of_eventually_eq N fun n hn => Rat.mul_inv_cancel _ (hne n hn))⟩

/-- `0⁻¹ = 0`. -/
protected theorem inv_zero : (0 : Real)⁻¹ = 0 := by
  show inv 0 = 0
  unfold inv
  rw [ite_eq_left rfl]

/-- A nonzero number times its inverse is `1`. -/
protected theorem mul_inv_cancel {a : Real} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  show a * inv a = 1
  unfold inv
  rw [ite_eq_right ha]
  exact Classical.epsilon_spec (exists_mul_eq_one ha)

/-- Inverting twice gives back the original number. -/
private theorem inv_inv (a : Real) : a⁻¹⁻¹ = a := by
  by_cases ha : a = 0
  · subst ha
    rw [Real.inv_zero, Real.inv_zero]
  · have h₁ := Real.mul_inv_cancel ha
    have ha' : a⁻¹ ≠ 0 := fun e => by
      rw [e, Real.mul_zero] at h₁
      exact Real.zero_ne_one h₁
    have h₂ := Real.mul_inv_cancel ha'
    grind

/-- `1⁻¹ = 1`. -/
private theorem inv_one : (1 : Real)⁻¹ = 1 := by
  have h := Real.mul_inv_cancel (Real.zero_ne_one.symm)
  rw [Real.one_mul] at h
  exact h

/-- Raising to a negated integer power is the inverse of the power. -/
protected theorem zpow_neg (a : Real) (n : Int) : a ^ (-n) = (a ^ n)⁻¹ := by
  match n with
  | .ofNat 0 => exact Real.inv_one.symm
  | .ofNat (k + 1) => rfl
  | .negSucc k =>
    show a ^ (k + 1) = ((a ^ (k + 1))⁻¹)⁻¹
    rw [Real.inv_inv]

/-- `Real` is a field. -/
noncomputable instance instField : Lean.Grind.Field Real where
  toCommRing := instCommRing
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := Real.zero_ne_one
  inv_zero := Real.inv_zero
  mul_inv_cancel := Real.mul_inv_cancel
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg := Real.zpow_neg

/-- `ofRat` preserves inverses (both `Rat` and `Real` use `0⁻¹ = 0`). -/
theorem ofRat_inv (a : Rat) : ofRat a⁻¹ = (ofRat a)⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    rw [Rat.inv_zero]
    exact Real.inv_zero.symm
  · have hne : ofRat a ≠ 0 := fun e => ha (ofRat_inj.mp e)
    have h₁ : ofRat a * ofRat a⁻¹ = 1 := by
      rw [← ofRat_mul, Rat.mul_inv_cancel a ha]
      rfl
    have h₂ := Real.mul_inv_cancel hne
    grind

/-- `ofRat` preserves division. -/
theorem ofRat_div (a b : Rat) : ofRat (a / b) = ofRat a / ofRat b := by
  rw [Rat.div_def, ofRat_mul, ofRat_inv]
  rfl

/-! ## Comparing with rationals -/

/-- `ofRat` preserves and reflects `<`. -/
theorem ofRat_lt_ofRat {a b : Rat} : ofRat a < ofRat b ↔ a < b := by
  constructor
  · rintro ⟨δ, hδ, N, hN⟩
    have hδba : δ ≤ b + -a := hN N (Nat.le_refl N)
    grind
  · intro h
    exact ⟨b - a, by grind, 0, fun _ _ => by show b - a ≤ b + -a; grind⟩

/-- `ofRat` preserves and reflects `≤`. -/
theorem ofRat_le_ofRat {a b : Rat} : ofRat a ≤ ofRat b ↔ a ≤ b := by
  constructor
  · rintro (h | h)
    · exact Rat.le_of_lt (ofRat_lt_ofRat.mp h)
    · have hab := ofRat_inj.mp h
      grind
  · intro h
    by_cases e : a = b
    · subst e
      exact Or.inr rfl
    · exact Or.inl (ofRat_lt_ofRat.mpr (by grind))

/-- If the terms of `x` are at most those of `y` from index `N` on, then `mk x ≤ mk y`. -/
private theorem mk_le_of_eventually_le {x y : CauchySeq} (N : Nat)
    (h : ∀ n, N ≤ n → x.seq n ≤ y.seq n) : mk x ≤ mk y := by
  apply le_of_not_lt
  rintro ⟨δ, hδ, M, hM⟩
  have a : δ ≤ x.seq (max N M) + -y.seq (max N M) := hM _ (by omega)
  have b := h (max N M) (by omega)
  grind

/-- The real number named by `c` lies within `ε` of the terms of `c` from some index on. -/
private theorem mk_near (c : CauchySeq) {ε : Rat} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → ofRat (c.seq n - ε) ≤ mk c ∧ mk c ≤ ofRat (c.seq n + ε) := by
  obtain ⟨N, hN⟩ := c.cauchy ε hε
  refine ⟨N, fun n hn => ⟨mk_le_of_eventually_le N fun m hm => ?_,
    mk_le_of_eventually_le N fun m hm => ?_⟩⟩
  · have hmn := hN m n hm hn
    rw [rat_abs_lt_iff] at hmn
    show c.seq n - ε ≤ c.seq m
    grind
  · have hmn := hN m n hm hn
    rw [rat_abs_lt_iff] at hmn
    show c.seq m ≤ c.seq n + ε
    grind

/-- Archimedean property: every real number is below some rational. -/
theorem exists_rat_gt (a : Real) : ∃ r : Rat, a < ofRat r := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨B, -, hB⟩ := x.cauchy.bounded
  refine ⟨B + 1, ?_⟩
  have h1 : mk x ≤ ofRat B := mk_le_of_eventually_le 0 fun n _ => (rat_abs_le_iff.mp (hB n)).2
  have h2 : ofRat B < ofRat (B + 1) := ofRat_lt_ofRat.mpr (by grind)
  grind

/-- Every real number is above some rational. -/
theorem exists_rat_lt (a : Real) : ∃ r : Rat, ofRat r < a := by
  obtain ⟨r, hr⟩ := exists_rat_gt (-a)
  refine ⟨-r, ?_⟩
  rw [ofRat_neg]
  grind

/-- Every positive real number is above some positive rational. -/
theorem exists_pos_rat_lt {a : Real} (h : 0 < a) : ∃ r : Rat, 0 < r ∧ ofRat r < a := by
  obtain ⟨x, rfl⟩ := exists_mk a
  obtain ⟨δ, hδ, N, hN⟩ := h
  refine ⟨δ / 2, by grind, δ / 2, by grind, N, fun n hn => ?_⟩
  have hδx : δ ≤ x.seq n + -0 := hN n hn
  show δ / 2 ≤ x.seq n + -(δ / 2)
  grind

/-! ## Completeness -/

/-- Any real number at or above an upper bound of `S` is also an upper bound of `S`. -/
private theorem isUpperBound_mono {S : Real → Prop} {u v : Real} (hu : IsUpperBound S u)
    (huv : u ≤ v) : IsUpperBound S v := fun x hx => by
  have hxu := hu x hx
  grind

/-- If `u` is an upper bound of `S` and `v` is not, then `v < u`. -/
private theorem lt_of_ub_of_not_ub {S : Real → Prop} {u v : Real} (hu : IsUpperBound S u)
    (hv : ¬ IsUpperBound S v) : v < u := by
  rcases lt_trichotomy v u with h | h | h
  · exact h
  · subst h
    exact absurd hu hv
  · exact absurd (isUpperBound_mono hu (Or.inl h)) hv

/-- For every step size `1 / (k + 1)`, some rational is an upper bound of `S` while the
rational one step below it is not. -/
private theorem exists_ub_step {S : Real → Prop} {a b : Real} (ha : S a)
    (hb : IsUpperBound S b) (k : Nat) :
    ∃ q : Rat, IsUpperBound S (ofRat q) ∧
      ¬ IsUpperBound S (ofRat (q - 1 / ((k : Rat) + 1))) := by
  obtain ⟨L, hL⟩ := exists_rat_lt a
  obtain ⟨M, hM⟩ := exists_rat_gt b
  have hk0 : (0 : Rat) ≤ k := Rat.natCast_nonneg
  have hh : (0 : Rat) < 1 / ((k : Rat) + 1) := rat_div_pos (by decide) (by grind)
  obtain ⟨j, hj⟩ := rat_exists_nat_gt ((M - L) / (1 / ((k : Rat) + 1)))
  have hjM : M < L + j * (1 / ((k : Rat) + 1)) := by
    have hMLj := (Rat.div_lt_iff hh).mp hj
    grind
  have hP : ∃ j : Nat, IsUpperBound S (ofRat (L + j * (1 / ((k : Rat) + 1)))) :=
    ⟨j, isUpperBound_mono hb (Or.inl (Real.lt_trans hM (ofRat_lt_ofRat.mpr hjM)))⟩
  obtain ⟨j₀, hj₀, hmin⟩ := nat_exists_min hP
  cases j₀ with
  | zero =>
    exfalso
    have e : L + ((0 : Nat) : Rat) * (1 / ((k : Rat) + 1)) = L := by grind
    rw [e] at hj₀
    have haL := hj₀ a ha
    grind
  | succ j =>
    refine ⟨_, hj₀, ?_⟩
    have e : L + ((j + 1 : Nat) : Rat) * (1 / ((k : Rat) + 1)) - 1 / ((k : Rat) + 1) =
        L + (j : Rat) * (1 / ((k : Rat) + 1)) := by
      rw [Rat.natCast_add]
      grind
    rw [e]
    exact hmin j (Nat.lt_succ_self j)

/-- For natural numbers `N ≤ m`, `1 / (m + 1) ≤ 1 / (N + 1)`. -/
private theorem inv_succ_le {N m : Nat} (h : N ≤ m) :
    1 / ((m : Rat) + 1) ≤ 1 / ((N : Rat) + 1) := by
  have h1 : (N : Rat) ≤ m := Rat.natCast_le_natCast.mpr h
  have h2 : (0 : Rat) ≤ N := Rat.natCast_nonneg
  exact rat_inv_le_inv (by grind) (by grind)

/-- Completeness: every nonempty set of real numbers with an upper bound has a least upper
bound. -/
theorem exists_isLUB (S : Real → Prop) (hne : ∃ x, S x) (hbdd : ∃ b, IsUpperBound S b) :
    ∃ s, IsLUB S s := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ := hbdd
  obtain ⟨q, hq⟩ : ∃ q : Nat → Rat, ∀ k, IsUpperBound S (ofRat (q k)) ∧
      ¬ IsUpperBound S (ofRat (q k - 1 / ((k : Rat) + 1))) :=
    ⟨fun k => Classical.choose (exists_ub_step ha hb k),
      fun k => Classical.choose_spec (exists_ub_step ha hb k)⟩
  have hcmp : ∀ k l, q l - 1 / ((l : Rat) + 1) < q k := fun k l =>
    ofRat_lt_ofRat.mp (lt_of_ub_of_not_ub (hq k).1 (hq l).2)
  have hcauchy : IsCauchy q := by
    intro ε hε
    obtain ⟨N, hN⟩ := rat_exists_inv_succ_lt hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have h1 := hcmp m n
    have h2 := hcmp n m
    have h3 := inv_succ_le hm
    have h4 := inv_succ_le hn
    rw [rat_abs_lt_iff]
    grind
  refine ⟨mk ⟨q, hcauchy⟩, fun x hx => ?_, fun b' hb' => ?_⟩
  · apply le_of_not_lt
    intro hsx
    obtain ⟨r, hr, hrx⟩ := exists_pos_rat_lt (Real.sub_pos.mpr hsx)
    obtain ⟨N, hN⟩ := mk_near ⟨q, hcauchy⟩ hr
    have h1 := (hN N (Nat.le_refl N)).1
    have h2 := (hq N).1 x hx
    rw [ofRat_sub] at h1
    grind
  · apply le_of_not_lt
    intro hbs
    obtain ⟨r, hr, hrs⟩ := exists_pos_rat_lt (Real.sub_pos.mpr hbs)
    obtain ⟨N₁, hN₁⟩ := mk_near ⟨q, hcauchy⟩ (show 0 < r / 2 by grind)
    obtain ⟨N₂, hN₂⟩ := rat_exists_inv_succ_lt (show 0 < r / 2 by grind)
    have h1 := (hN₁ (max N₁ N₂) (by omega)).2
    have h2 := lt_of_ub_of_not_ub hb' (hq (max N₁ N₂)).2
    have h3 := inv_succ_le (show N₂ ≤ max N₁ N₂ by omega)
    have h4 : ofRat (1 / (((max N₁ N₂ : Nat) : Rat) + 1)) < ofRat (r / 2) :=
      ofRat_lt_ofRat.mpr (by grind)
    have h5 : ofRat r = ofRat (r / 2) + ofRat (r / 2) := by
      rw [← ofRat_add]
      congr 1
      grind
    rw [ofRat_add] at h1
    rw [ofRat_sub] at h2
    grind

end Real

end Strata.Util

end

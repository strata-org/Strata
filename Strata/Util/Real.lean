/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Real numbers

`Real` is the type of real numbers, built from the rationals (`Rat`, from Lean core) without
Mathlib. A real number is an equivalence class of Cauchy sequences of rationals: sequences whose
terms eventually stay arbitrarily close to each other. Two such sequences name the same real
number when their difference tends to `0`.

This file holds the definitions: `CauchySeq`, the type `Real`, the embedding `Real.ofRat`, the
arithmetic operations, the order, and least upper bounds (`Real.IsLUB`). Lifting an operation
to equivalence classes needs a proof that it respects equivalence, so the proofs that sums,
negations, and products of Cauchy sequences are Cauchy, and respect equivalence, are here too.

The laws (`Real` is a complete linearly ordered field) are in `Strata.Util.RealProps`.

Equality and order of real numbers are not decidable, so there are no `Decidable` instances for
them, and the inverse (defined by choice) is noncomputable.
-/

@[expose] public section

namespace Strata.Util

/-! ## Rational helpers -/

/-- The absolute value of `x` is at most `e` exactly when `-e ≤ x ≤ e`. -/
private theorem rat_abs_le_iff {x e : Rat} : x.abs ≤ e ↔ -e ≤ x ∧ x ≤ e := by
  unfold Rat.abs; split <;> grind

/-- The absolute value of `x` is below `e` exactly when `-e < x < e`. -/
private theorem rat_abs_lt_iff {x e : Rat} : x.abs < e ↔ -e < x ∧ x < e := by
  unfold Rat.abs; split <;> grind

/-- Triangle inequality: `|a + b| ≤ |a| + |b|` for rationals. -/
private theorem rat_abs_add_le (a b : Rat) : (a + b).abs ≤ a.abs + b.abs := by
  unfold Rat.abs; split <;> split <;> split <;> grind

/-- The absolute value of a product of rationals is the product of the absolute values. -/
private theorem rat_abs_mul (a b : Rat) : (a * b).abs = a.abs * b.abs := by
  rcases (Rat.le_total : (0 : Rat) ≤ a ∨ a ≤ 0) with ha | ha <;>
    rcases (Rat.le_total : (0 : Rat) ≤ b ∨ b ≤ 0) with hb | hb
  · rw [Rat.abs_of_nonneg ha, Rat.abs_of_nonneg hb, Rat.abs_of_nonneg (Rat.mul_nonneg ha hb)]
  · have hnb := Rat.mul_nonneg ha (show 0 ≤ -b by grind)
    rw [Rat.abs_of_nonneg ha, Rat.abs_of_nonpos hb, Rat.abs_of_nonpos (by grind), Rat.mul_neg]
  · have hna := Rat.mul_nonneg (show 0 ≤ -a by grind) hb
    rw [Rat.abs_of_nonpos ha, Rat.abs_of_nonneg hb, Rat.abs_of_nonpos (by grind), Rat.neg_mul]
  · have hnab := Rat.mul_nonneg (show 0 ≤ -a by grind) (show 0 ≤ -b by grind)
    rw [Rat.abs_of_nonpos ha, Rat.abs_of_nonpos hb, Rat.abs_of_nonneg (by grind)]
    grind

/-- The quotient of two positive rationals is positive. -/
private theorem rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  (Rat.lt_div_iff hb).mpr (by grind)

/-- If `a` is close to `a'` and `b` is close to `b'`, relative to bounds `A` on `a` and `B` on
`b'`, then `a * b` is within `ε` of `a' * b'`. -/
private theorem rat_mul_close {a a' b b' A B ε : Rat} (hA : 0 < A) (hB : 0 < B)
    (ha : a.abs ≤ A) (hb' : b'.abs ≤ B)
    (hb : (b - b').abs < ε / (2 * A)) (haa : (a - a').abs < ε / (2 * B)) :
    (a * b - a' * b').abs < ε := by
  have e : a * b - a' * b' = a * (b - b') + b' * (a - a') := by grind
  rw [e]
  have h1 := rat_abs_add_le (a * (b - b')) (b' * (a - a'))
  rw [rat_abs_mul, rat_abs_mul] at h1
  have h2 : a.abs * (b - b').abs ≤ A * (b - b').abs :=
    Rat.mul_le_mul_of_nonneg_right ha Rat.abs_nonneg
  have h3 : A * (b - b').abs < A * (ε / (2 * A)) := Rat.mul_lt_mul_of_pos_left hb hA
  have h4 : b'.abs * (a - a').abs ≤ B * (a - a').abs :=
    Rat.mul_le_mul_of_nonneg_right hb' Rat.abs_nonneg
  have h5 : B * (a - a').abs < B * (ε / (2 * B)) := Rat.mul_lt_mul_of_pos_left haa hB
  have h6 : A * (ε / (2 * A)) = ε / 2 := by grind
  have h7 : B * (ε / (2 * B)) = ε / 2 := by grind
  grind

/-! ## Cauchy sequences -/

/-- A sequence `f` of rationals is Cauchy when, for every positive rational `ε`, its terms from
some index on are all within `ε` of each other. -/
def IsCauchy (f : Nat → Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ m n, N ≤ m → N ≤ n → (f m - f n).abs < ε

namespace IsCauchy

/-- Every Cauchy sequence of rationals is bounded: some positive rational `B` bounds the
absolute value of every term. -/
private theorem bounded {f : Nat → Rat} (hf : IsCauchy f) :
    ∃ B : Rat, 0 < B ∧ ∀ n, (f n).abs ≤ B := by
  obtain ⟨N, hN⟩ := hf 1 (by decide)
  have fin : ∀ K, ∃ B : Rat, 0 ≤ B ∧ ∀ n, n < K → (f n).abs ≤ B := by
    intro K
    induction K with
    | zero => exact ⟨0, Rat.le_refl, fun n h => absurd h (Nat.not_lt_zero n)⟩
    | succ K ih =>
      obtain ⟨B, hB0, hB⟩ := ih
      have hK := Rat.abs_nonneg (x := f K)
      refine ⟨B + (f K).abs, by grind, fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · have hBn := hB n h; grind
      · subst h; grind
  obtain ⟨B, hB0, hB⟩ := fin N
  have hN0 := Rat.abs_nonneg (x := f N)
  refine ⟨B + (f N).abs + 1, by grind, fun n => ?_⟩
  by_cases h : n < N
  · have hBn := hB n h; grind
  · have h1 := hN n N (by omega) (Nat.le_refl N)
    have h2 := rat_abs_add_le (f n - f N) (f N)
    have e : f n - f N + f N = f n := by grind
    rw [e] at h2
    grind

/-- The termwise sum of two Cauchy sequences is Cauchy. -/
theorem add {f g : Nat → Rat} (hf : IsCauchy f) (hg : IsCauchy g) :
    IsCauchy (fun n => f n + g n) := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := hf (ε / 2) (by grind)
  obtain ⟨N₂, h₂⟩ := hg (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
  have a := h₁ m n (by omega) (by omega)
  have b := h₂ m n (by omega) (by omega)
  rw [rat_abs_lt_iff] at a b ⊢
  grind

/-- The termwise negation of a Cauchy sequence is Cauchy. -/
theorem neg {f : Nat → Rat} (hf : IsCauchy f) : IsCauchy (fun n => -f n) := by
  intro ε hε
  obtain ⟨N, h⟩ := hf ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have a := h m n hm hn
  rw [rat_abs_lt_iff] at a ⊢
  grind

/-- The termwise product of two Cauchy sequences is Cauchy. -/
theorem mul {f g : Nat → Rat} (hf : IsCauchy f) (hg : IsCauchy g) :
    IsCauchy (fun n => f n * g n) := by
  intro ε hε
  obtain ⟨A, hA, hfA⟩ := hf.bounded
  obtain ⟨B, hB, hgB⟩ := hg.bounded
  obtain ⟨N₁, h₁⟩ := hg (ε / (2 * A)) (rat_div_pos hε (by grind))
  obtain ⟨N₂, h₂⟩ := hf (ε / (2 * B)) (rat_div_pos hε (by grind))
  refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
  exact rat_mul_close hA hB (hfA m) (hgB n) (h₁ m n (by omega) (by omega))
    (h₂ m n (by omega) (by omega))

/-- A constant sequence is Cauchy. -/
theorem const (r : Rat) : IsCauchy (fun _ => r) := by
  intro ε hε
  refine ⟨0, fun _ _ _ _ => ?_⟩
  rw [rat_abs_lt_iff]
  grind

end IsCauchy

/-- A Cauchy sequence of rationals. -/
structure CauchySeq where
  /-- The `n`-th term of the sequence. -/
  seq : Nat → Rat
  /-- Proof that `seq` satisfies `IsCauchy`. -/
  cauchy : IsCauchy seq

namespace CauchySeq

/-- Two Cauchy sequences are equivalent when their termwise difference tends to `0`. They then
name the same real number. -/
def Equiv (x y : CauchySeq) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → (x.seq n - y.seq n).abs < ε

/-- A Cauchy sequence is positive when, from some index on, its terms are at least some fixed
positive rational `δ`. -/
def Pos (x : CauchySeq) : Prop :=
  ∃ δ : Rat, 0 < δ ∧ ∃ N : Nat, ∀ n, N ≤ n → δ ≤ x.seq n

/-- The constant sequence with value `r`. -/
def const (r : Rat) : CauchySeq := ⟨fun _ => r, IsCauchy.const r⟩

instance : Add CauchySeq :=
  ⟨fun x y => ⟨fun n => x.seq n + y.seq n, IsCauchy.add x.cauchy y.cauchy⟩⟩

instance : Neg CauchySeq := ⟨fun x => ⟨fun n => -x.seq n, IsCauchy.neg x.cauchy⟩⟩

instance : Mul CauchySeq :=
  ⟨fun x y => ⟨fun n => x.seq n * y.seq n, IsCauchy.mul x.cauchy y.cauchy⟩⟩

/-- Every Cauchy sequence is equivalent to itself. -/
theorem Equiv.refl (x : CauchySeq) : Equiv x x := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  rw [rat_abs_lt_iff]
  grind

/-- Equivalence of Cauchy sequences is symmetric. -/
theorem Equiv.symm {x y : CauchySeq} (h : Equiv x y) : Equiv y x := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have a := hN n hn
  rw [rat_abs_lt_iff] at a ⊢
  grind

/-- Equivalence of Cauchy sequences is transitive. -/
theorem Equiv.trans {x y z : CauchySeq} (h₁ : Equiv x y) (h₂ : Equiv y z) :
    Equiv x z := by
  intro ε hε
  obtain ⟨N₁, k₁⟩ := h₁ (ε / 2) (by grind)
  obtain ⟨N₂, k₂⟩ := h₂ (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have a := k₁ n (by omega)
  have b := k₂ n (by omega)
  rw [rat_abs_lt_iff] at a b ⊢
  grind

/-- Equivalence of Cauchy sequences, used to form the quotient `Real`. -/
instance setoid : Setoid CauchySeq :=
  ⟨Equiv, ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩⟩

/-- Adding equivalent sequences gives equivalent sums. -/
theorem add_equiv {x x' y y' : CauchySeq} (hx : Equiv x x') (hy : Equiv y y') :
    Equiv (x + y) (x' + y') := by
  intro ε hε
  obtain ⟨N₁, k₁⟩ := hx (ε / 2) (by grind)
  obtain ⟨N₂, k₂⟩ := hy (ε / 2) (by grind)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have a := k₁ n (by omega)
  have b := k₂ n (by omega)
  show (x.seq n + y.seq n - (x'.seq n + y'.seq n)).abs < ε
  rw [rat_abs_lt_iff] at a b ⊢
  grind

/-- Negating equivalent sequences gives equivalent results. -/
theorem neg_equiv {x x' : CauchySeq} (hx : Equiv x x') : Equiv (-x) (-x') := by
  intro ε hε
  obtain ⟨N, k⟩ := hx ε hε
  refine ⟨N, fun n hn => ?_⟩
  have a := k n hn
  show (-x.seq n - -x'.seq n).abs < ε
  rw [rat_abs_lt_iff] at a ⊢
  grind

/-- Multiplying equivalent sequences gives equivalent products. -/
theorem mul_equiv {x x' y y' : CauchySeq} (hx : Equiv x x') (hy : Equiv y y') :
    Equiv (x * y) (x' * y') := by
  intro ε hε
  obtain ⟨A, hA, hxA⟩ := x.cauchy.bounded
  obtain ⟨B, hB, hyB⟩ := y'.cauchy.bounded
  obtain ⟨N₁, k₁⟩ := hy (ε / (2 * A)) (rat_div_pos hε (by grind))
  obtain ⟨N₂, k₂⟩ := hx (ε / (2 * B)) (rat_div_pos hε (by grind))
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  exact rat_mul_close hA hB (hxA n) (hyB n) (k₁ n (by omega)) (k₂ n (by omega))

/-- A sequence equivalent to a positive sequence is positive. -/
theorem pos_of_equiv {x y : CauchySeq} (h : Equiv x y) (hx : Pos x) : Pos y := by
  obtain ⟨δ, hδ, N₁, k₁⟩ := hx
  obtain ⟨N₂, k₂⟩ := h (δ / 2) (by grind)
  refine ⟨δ / 2, by grind, max N₁ N₂, fun n hn => ?_⟩
  have a := k₁ n (by omega)
  have b := k₂ n (by omega)
  rw [rat_abs_lt_iff] at b
  grind

end CauchySeq

/-! ## The real numbers -/

/-- The real numbers: Cauchy sequences of rationals, identified when their difference tends
to `0`. -/
def Real : Type := Quotient CauchySeq.setoid

namespace Real

/-- The real number named by a Cauchy sequence. -/
def mk (x : CauchySeq) : Real := Quotient.mk _ x

/-- The rational `r` as a real number. -/
def ofRat (r : Rat) : Real := mk (CauchySeq.const r)

instance : OfNat Real n := ⟨ofRat (OfNat.ofNat n)⟩

instance : Inhabited Real := ⟨0⟩

instance : NatCast Real := ⟨fun n => ofRat n⟩

instance : IntCast Real := ⟨fun i => ofRat i⟩

/-- Addition of real numbers, computed termwise on Cauchy sequences. -/
def add : Real → Real → Real :=
  Quotient.lift₂ (fun x y => mk (x + y))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (CauchySeq.add_equiv h₁ h₂))

/-- Negation of real numbers, computed termwise on Cauchy sequences. -/
def neg : Real → Real :=
  Quotient.lift (fun x => mk (-x)) (fun _ _ h => Quotient.sound (CauchySeq.neg_equiv h))

/-- Multiplication of real numbers, computed termwise on Cauchy sequences. -/
def mul : Real → Real → Real :=
  Quotient.lift₂ (fun x y => mk (x * y))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (CauchySeq.mul_equiv h₁ h₂))

instance : Add Real := ⟨add⟩

instance : Neg Real := ⟨neg⟩

instance : Sub Real := ⟨fun a b => a + -b⟩

instance : Mul Real := ⟨mul⟩

/-- `a < b` when the sequences for `b - a` are positive. -/
def lt : Real → Real → Prop :=
  Quotient.lift₂ (fun x y => CauchySeq.Pos (y + -x)) (fun _ _ _ _ ha hb =>
    propext ⟨CauchySeq.pos_of_equiv (CauchySeq.add_equiv hb (CauchySeq.neg_equiv ha)),
      CauchySeq.pos_of_equiv
        (CauchySeq.add_equiv (CauchySeq.Equiv.symm hb)
          (CauchySeq.neg_equiv (CauchySeq.Equiv.symm ha)))⟩)

instance : LT Real := ⟨lt⟩

instance : LE Real := ⟨fun a b => a < b ∨ a = b⟩

instance : Nonempty Real := ⟨0⟩

/-- The multiplicative inverse. Follows the convention `0⁻¹ = 0`; for `x ≠ 0` it is some `y`
with `x * y = 1` (see `Real.mul_inv_cancel`). -/
noncomputable def inv (x : Real) : Real :=
  haveI := Classical.propDecidable (x = 0)
  if x = 0 then 0 else Classical.epsilon (fun y => x * y = 1)

noncomputable instance : Inv Real := ⟨inv⟩

noncomputable instance : Div Real := ⟨fun a b => a * b⁻¹⟩

/-- `x ^ n` for a natural number `n`. -/
def npow (x : Real) : Nat → Real
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow Real Nat Real := ⟨npow⟩

/-- `x ^ i` for an integer `i`; negative powers are inverses of positive powers. -/
noncomputable def zpow (x : Real) : Int → Real
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

noncomputable instance : HPow Real Int Real := ⟨zpow⟩

instance : SMul Nat Real := ⟨fun n x => (n : Real) * x⟩

instance : SMul Int Real := ⟨fun i x => (i : Real) * x⟩

/-- `b` is an upper bound of the set `S` (given as a predicate). -/
def IsUpperBound (S : Real → Prop) (b : Real) : Prop := ∀ x, S x → x ≤ b

/-- `s` is the least upper bound (supremum) of the set `S`. -/
def IsLUB (S : Real → Prop) (s : Real) : Prop :=
  IsUpperBound S s ∧ ∀ b, IsUpperBound S b → s ≤ b

end Real

end Strata.Util

end

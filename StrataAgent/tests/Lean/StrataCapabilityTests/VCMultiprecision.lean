/-! # Verification conditions (Tier: multiprecision limb arithmetic)

Inspired by the NTP4VC (github.com/xqyww123/NTP4VC) `multiprecision/add_vcg` and
`sub_vcg` VCs (GMP-style `wmpn_add`/`wmpn_sub`). The benchmark states these over
machine `BitVec 64` limbs with a `Why3.mach` support library; here the essential
carry/borrow proof obligations are ported to core Lean 4 (no Mathlib) over `Nat`
with an explicit base `B = 2^64`, so they are self-contained.

The recurring VC in limb-by-limb addition/subtraction is: the carry (resp. borrow)
out of a single limb operation is at most 1, and the base-`B` split reconstructs
the exact value. These need `Nat` division/modulus reasoning, not just linear
arithmetic. Proofs are left as `sorry`. -/

-- One machine word; a multiprecision number is a sequence of base-`B` limbs.
abbrev B : Nat := 2 ^ 64

-- add_vcg (wmpn_add_1 / add_n): the carry OUT of adding two limbs plus a carry-in
-- is at most 1 — the invariant that keeps the propagated carry a single bit.
theorem add_carry_out_le_one_vc (a b cin : Nat)
    (ha : a < B) (hb : b < B) (hc : cin ≤ 1) : (a + b + cin) / B ≤ 1 := by
  sorry

-- add_vcg: the base-`B` split — high limb (carry) times B plus the low limb
-- equals the full sum. This is the correctness spec of a single add step.
theorem add_split_vc (a b cin : Nat) :
    B * ((a + b + cin) / B) + (a + b + cin) % B = a + b + cin := by
  sorry

-- sub_vcg (wmpn_sub_1 / sub_n): the borrow OUT of subtracting one limb from
-- another (computed as `B + a - b` to stay in `Nat`) is at most 1.
theorem sub_borrow_le_one_vc (a b : Nat)
    (ha : a < B) (hb : b < B) : (B + a - b) / B ≤ 1 := by
  sorry

/-! # Verification-condition warm-ups (Tier 1: easy arithmetic)

NTP4VC-inspired VCs (github.com/xqyww123/NTP4VC), ported to core Lean 4 (no
Mathlib) over `Nat` instead of the benchmark's `ℤ`/`Why3.Base` prelude. Each is
a self-contained proof obligation stated in the benchmark's style: hypotheses as
arguments, one goal, proof left as `sorry`.

These are the simplest VCs — dischargeable by `omega`/`decide`/`simp`. They exist
to sanity-check the end-to-end pipeline quickly. -/

-- division_vcg: the remainder is smaller than a positive divisor.
theorem mod_lt_vc (a b : Nat) (h : 0 < b) : a % b < b := by
  sorry

-- division_vcg: Euclidean division identity `b * (a / b) + a % b = a`.
theorem div_mod_vc (a b : Nat) : b * (a / b) + a % b = a := by
  sorry

-- bitcount_vcg-style: monotonicity of subtraction.
theorem sub_le_vc (a b : Nat) : a - b ≤ a := by
  sorry
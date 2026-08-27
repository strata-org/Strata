/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# `frac{num, den}` literal encoding for non-terminating reals

A `realConst` whose value has no terminating decimal representation (e.g.
`1/3`) cannot be printed as a `realLit`. It is instead emitted as the exact
rational literal `frac{num, den}`, whose operands are non-negative `Num`
tokens, with the sign carried by a wrapping `neg_expr`.

The printer (`FormatCore`) and the parser transform (`Translate`) sit on
opposite sides of that surface syntax and must agree on the encoding:

* `FormatCore` calls `fracEncode` to obtain `(neg, num, den)`, emits
  `fracLit num den`, and wraps it in `neg_expr` iff `neg`.
* `Translate`'s `fracLit` arm calls `fracDecode` to turn `num`/`den` back into
  a `Rat`; the wrapping `neg_expr` is negated by the generic negation arm.

Routing both sides through these helpers means a refactor that lets them drift
apart breaks `fracDecode_fracEncode` below, and hence the build. The theorem
models the full round-trip: the `if neg` mirrors how `FormatCore`'s `neg_expr`
wrap composes with `Translate`'s negation of it.
-/

namespace Core.FracLit

public section

/-- Split a rational into the `frac{num, den}` operands the printer emits: a
sign flag plus the non-negative numerator/denominator. The sign is carried
separately because the `Num` tokens in `frac{...}` cannot be negative, so a
negative value is wrapped in `neg_expr` at the call site. -/
def fracEncode (r : Rat) : Bool × Nat × Nat :=
  (r.num < 0, r.num.natAbs, r.den)

/-- The rational value the parser assigns to the (non-negated) `frac{num, den}`
operands. The sign is reapplied by the wrapping `neg_expr`, so this is the
non-negative half of the decode. -/
def fracDecode (num den : Nat) : Rat :=
  mkRat (Int.ofNat num) den

/-- The `frac{...}` encoding round-trips at the value level: decoding the
operands `fracEncode` produces for `r` — and reapplying the sign the way the
`neg_expr` wrap does — recovers `r` exactly. Pins the sign/abs handling shared
by `FormatCore` and `Translate`. -/
theorem fracDecode_fracEncode (r : Rat) :
    (let (neg, num, den) := fracEncode r
     if neg then -(fracDecode num den) else fracDecode num den) = r := by
  simp only [fracEncode, fracDecode, Int.ofNat_eq_natCast]
  split
  · next h =>
    rw [decide_eq_true_eq] at h
    rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h), Rat.neg_mkRat, Int.neg_neg,
        Rat.mkRat_self]
  · next h =>
    rw [decide_eq_true_eq] at h
    rw [Int.natAbs_of_nonneg (Int.not_lt.mp h), Rat.mkRat_self]

end

end Core.FracLit

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchor:
- Source: dalek-lite `curve25519-dalek/src/montgomery.rs`
  `MontgomeryPoint::mul_bits_be` (line 519) implements the Montgomery ladder
  (Algorithm 8 of Costello-Smith 2017). It maintains two co-evolving projective
  points `x0` and `x1` across ~255 iterations, with the relational invariant:
    x0 == scalar_mul(base, bits_above(n, 254 - i))
    x1 == scalar_mul(base, bits_above(n, 254 - i) + 1)
  where `bits_above(n, k)` is the integer formed by the top k bits of n.
- Gap 1 (verification): `gen_smt_vcs` / `smtVCsCorrect` has a known type-mismatch
  bug for while-loop programs with local `var` declarations. While-loop programs
  must be verified via `#eval Strata.Boole.verify "cvc5"`.
- Gap 2 (axioms): cvc5 cannot discharge the group-law invariant from scratch.
  The fix is "manual induction": supply the ladder-step lemma explicitly as a
  Boole axiom so that cvc5 only needs quantifier instantiation, not induction.
  The remaining open question is whether cvc5's E-matching saturates on the
  quantified ladder-step axiom within the solver's resource limits.
-/

-- Baseline: single-variable for-loop invariant — works in Boole.
private def simpleInvariantSeed : Strata.Program :=
#strata
program Boole;

procedure sum_to_n(n: int) returns (r: int)
spec {
  requires n >= 0;
  ensures r == (n * (n - 1)) div 2;
}
{
  var sum : int := 0;
  for i : int := 0 to (n - 1) by 1
    invariant i <= n
    invariant (i * (i - 1)) div 2 == sum
  {
    sum := sum + i;
  }
  r := sum;
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: sum_to_n_ensures_1_1444
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" simpleInvariantSeed (options := .quiet)

example : Strata.smtVCsCorrect simpleInvariantSeed := by
  gen_smt_vcs
  all_goals (try grind)

-- Relational while-loop invariant — works in Boole.
-- Models the structural pattern of the Montgomery ladder using linear arithmetic:
-- x0 tracks i * step, x1 tracks (i + 1) * step.
-- The relational invariant `x1 == x0 + step` mirrors the elliptic-curve identity
-- [q+1]P = [q]P + P (i.e. x1 - x0 = P = base in the scalar-multiplication loop).
--
-- Note: `smtVCsCorrect` / `gen_smt_vcs` has a known type-mismatch bug for
-- while-loop programs with local `var` declarations. Verification uses cvc5 directly.
private def relationalInvariantSeed : Strata.Program :=
#strata
program Boole;

procedure linear_ladder(step: int, n: int) returns (r: int)
spec {
  requires n >= 0;
  ensures r == n * step;
}
{
  var x0 : int := 0;
  var x1 : int := step;
  var i  : int := 0;
  while (i < n)
    invariant i <= n
    invariant x1 == x0 + step
    invariant x0 == i * step
  {
    x0 := x1;
    x1 := x1 + step;
    i  := i + 1;
  }
  r := x0;
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: linear_ladder_ensures_1_2905
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" relationalInvariantSeed (options := .quiet)

example : Strata.smtVCsCorrect relationalInvariantSeed := by
  gen_smt_vcs
  all_goals (try grind)

-- Target shape — verbatim dalek-lite structure.
--
-- Source: `curve25519-dalek/src/montgomery.rs`, `MontgomeryPoint::mul_bits_be`
-- (Algorithm 8 of Costello-Smith 2017, the Montgomery ladder).
--
-- The Rust/Verus spec is:
--   ensures ({
--     let P = canonical_montgomery_lift(montgomery_point_as_nat(self));
--     let clamped_bytes = spec_clamp_integer(bytes);
--     let n = u8_32_as_nat(&clamped_bytes);
--     let R = montgomery_scalar_mul(P, n);
--     montgomery_point_as_nat(result) == u_coordinate(R)
--   })
--
-- The algorithm maintains two co-evolving projective points across 255 iterations:
--   x0 = [bits_above(n, k)]P   (the "current" scalar multiple)
--   x1 = [bits_above(n, k)+1]P (always one step ahead)
-- where bits_above(n, k) is the integer formed by the top k bits of n.
--
-- Each iteration reads one bit of the scalar (MSB first) and performs either:
--   bit = 0: x1 = differential_add(x0, x1, P); x0 = double(x0)
--   bit = 1: x0 = differential_add(x0, x1, P); x1 = double(x1)
-- preserving the invariant that x1 - x0 = P (projective differential relation).
--
-- Gap: cvc5 cannot discharge the group-law invariant from scratch.
-- The fix is "manual induction": supply the ladder-step lemma as a Boole axiom
-- so cvc5 only needs quantifier instantiation. The remaining open question is
-- whether cvc5's E-matching saturates on the quantified axiom within resource limits.
--
-- program Boole;
--
-- function montgomery_add(u0: int, u1: int, base: int) : int;
-- function double_pt(u: int, base: int) : int;
-- function scalar_mul(base: int, n: int) : int;
-- function bits_above(n: int, k: int) : int;
-- function bit(n: int, k: int) : int;
-- function canonical_lift(u: int) : int;
-- function u_coordinate(P: int) : int;
--
-- axiom (∀ n: int . bits_above(n, 0) == 0);
-- axiom (∀ n: int, k: int . bits_above(n, k+1) == 2 * bits_above(n, k) + bit(n, k));
-- axiom (∀ n: int, k: int . bit(n, k) == 0 || bit(n, k) == 1);
-- axiom (∀ base: int . scalar_mul(base, 0) == 0);
-- axiom (∀ base: int . scalar_mul(base, 1) == base);
-- axiom (∀ n: int . bits_above(n, 255) == n);
--
-- procedure mul_bits_be(base: int, n: int) returns (r: int)
-- spec {
--   requires is_valid_montgomery_point(base);
--   ensures r == u_coordinate(scalar_mul(canonical_lift(base), n));
-- }
-- {
--   var x0 : int := 0;
--   var x1 : int := base;
--   for i : int := 254 downto 0 by 1
--     invariant x0 == scalar_mul(canonical_lift(base), bits_above(n, 254 - i))
--     invariant x1 == scalar_mul(canonical_lift(base), bits_above(n, 254 - i) + 1)
--   {
--     if (bit(n, i) == 1) {
--       x0 := montgomery_add(x0, x1, base);
--       x1 := double_pt(x1, base);
--     } else {
--       x1 := montgomery_add(x0, x1, base);
--       x0 := double_pt(x0, base);
--     }
--   }
--   r := x0;
-- };

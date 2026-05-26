/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchor: dalek-lite `bytes_seq_as_nat` / `seq_as_nat_52` (B2).

Exercises `e as_int` in contexts beyond the flat `x as_int` covered by
`cast_expr.lean`:

- Cast inside a ∀-quantifier body over a sequence
- Cast of a compound BV expression (bitwise &)
- Cast in an arithmetic sum bound
- Cast inside a `let_in_expr` binding
- Cast inside a ∃-quantifier body
- Cast inside a `rec function` body with `decreases`, plus axiom-backed
  properties (single-byte decode and empty-sequence base case)
-/

private def castNestedSeed : Strata.Program :=
#strata
program Boole;

procedure cast_in_forall(s: Sequence bv8, n: int) returns ()
spec {
  requires 0 <= n && n <= Sequence.length(s);
  ensures ∀ i: int . 0 <= i && i < n ==> (Sequence.select(s, i) as_int) < 256;
}
{
  assert ∀ i: int . 0 <= i && i < n ==> (Sequence.select(s, i) as_int) < 256;
};

procedure cast_compound_bv(a: bv8, b: bv8) returns ()
spec {
  ensures 0 <= ((a & b) as_int);
  ensures ((a & b) as_int) < 256;
}
{
  assert 0 <= ((a & b) as_int);
  assert ((a & b) as_int) < 256;
};

procedure cast_sum_bound(a: bv8, b: bv8) returns ()
spec {
  ensures (a as_int) + (b as_int) < 512;
}
{
  assert (a as_int) + (b as_int) < 512;
};

procedure cast_in_let(x: bv8) returns ()
spec {
  ensures let n : int := (x as_int) in n >= 0 && n < 256;
}
{
  assert let n : int := (x as_int) in n >= 0 && n < 256;
};

procedure cast_in_exists(s: Sequence bv64) returns ()
spec {
  requires Sequence.length(s) > 0;
  ensures ∃ i: int . 0 <= i && i < Sequence.length(s) && (Sequence.select(s, i) as_int) >= 0;
}
{
  assert ∃ i: int . 0 <= i && i < Sequence.length(s) && (Sequence.select(s, i) as_int) >= 0;
};

rec function bytes_to_nat(s: Sequence bv8) : int
  decreases Sequence.length(s)
{
  if Sequence.length(s) == 0 then 0
  else (Sequence.select(s, 0) as_int) + 256 * bytes_to_nat(Sequence.skip(s, 1))
}
;

axiom bytes_to_nat(Sequence.empty_bv8) == 0;
axiom (∀ h: bv8 . ∀ t: Sequence bv8 .
  bytes_to_nat(Sequence.build(t, h)) == (h as_int) + 256 * bytes_to_nat(t));

procedure test_rec_empty() returns ()
spec {
  ensures bytes_to_nat(Sequence.empty_bv8) == 0;
} { exit test_rec_empty; };

procedure test_rec_single_byte(x: bv8) returns ()
spec {
  ensures bytes_to_nat(Sequence.build(Sequence.empty_bv8, x)) == (x as_int);
} { exit test_rec_single_byte; };
#end

/-- info:
Obligation: cast_in_forall_post_cast_in_forall_ensures_1_829_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_assert_2_915_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_2_915
Property: assert
Result: ✅ pass

Obligation: cast_in_forall_ensures_1_829
Property: assert
Result: ✅ pass

Obligation: assert_5_1132
Property: assert
Result: ✅ pass

Obligation: assert_6_1164
Property: assert
Result: ✅ pass

Obligation: cast_compound_bv_ensures_3_1061
Property: assert
Result: ✅ pass

Obligation: cast_compound_bv_ensures_4_1094
Property: assert
Result: ✅ pass

Obligation: assert_8_1305
Property: assert
Result: ✅ pass

Obligation: cast_sum_bound_ensures_7_1260
Property: assert
Result: ✅ pass

Obligation: assert_10_1459
Property: assert
Result: ✅ pass

Obligation: cast_in_let_ensures_9_1397
Property: assert
Result: ✅ pass

Obligation: cast_in_exists_post_cast_in_exists_ensures_12_1616_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: assert_assert_13_1717_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: assert_13_1717
Property: assert
Result: ✅ pass

Obligation: cast_in_exists_ensures_12_1616
Property: assert
Result: ✅ pass

Obligation: bytes_to_nat_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_to_nat_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_to_nat_terminates_0
Property: assert
Result: ✅ pass

Obligation: bytes_to_nat_terminates_1
Property: assert
Result: ✅ pass

Obligation: test_rec_empty_ensures_16_2232
Property: assert
Result: ✅ pass

Obligation: test_rec_single_byte_ensures_17_2367
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castNestedSeed (options := .quiet)

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchor:
- Source: dalek-lite `curve25519-dalek/src/scalar.rs`
  (`from_bytes_mod_order_wide`, B2) and `from_bytes_mod_order` (B2/B5).
  Rust `u8 as usize`, `u64 as u128`, etc. are widening casts; this seed
  exercises the Boole `e as_int` surface syntax for all supported widths
  (bv1, bv8, bv16, bv32, bv64, bv128).

Feature: `e as_int` — widening cast from any bitvector type to `int`.

Lowers to a native `Bv{n}.ToNat : bvN → int` Core op; the SMT encoder maps
it to the standard SMT-LIB `bv2nat` function. No axioms injected.
-/

private def castExprSeed : Strata.Program :=
#strata
program Boole;

procedure cast_bv8_nonneg(x: bv8) returns ()
spec {
  ensures 0 <= (x as_int);
}
{
  assert 0 <= (x as_int);
};

procedure cast_bv64_nonneg(x: bv64) returns ()
spec {
  ensures 0 <= (x as_int);
}
{
  assert 0 <= (x as_int);
};

procedure cast_bv32_bounded(x: bv32) returns ()
spec {
  ensures 0 <= (x as_int) && (x as_int) < 4294967296;
}
{
  assert 0 <= (x as_int) && (x as_int) < 4294967296;
};

procedure cast_bv1_nonneg(x: bv1) returns ()
spec {
  ensures 0 <= (x as_int);
}
{
  assert 0 <= (x as_int);
};

procedure cast_bv16_nonneg(x: bv16) returns ()
spec {
  ensures 0 <= (x as_int);
}
{
  assert 0 <= (x as_int);
};

procedure cast_bv128_nonneg(x: bv128) returns ()
spec {
  ensures 0 <= (x as_int);
}
{
  assert 0 <= (x as_int);
};
#end

/-- info:
Obligation: assert_1_836
Property: assert
Result: ✅ pass

Obligation: cast_bv8_nonneg_ensures_0_805
Property: assert
Result: ✅ pass

Obligation: assert_3_951
Property: assert
Result: ✅ pass

Obligation: cast_bv64_nonneg_ensures_2_920
Property: assert
Result: ✅ pass

Obligation: assert_5_1094
Property: assert
Result: ✅ pass

Obligation: cast_bv32_bounded_ensures_4_1036
Property: assert
Result: ✅ pass

Obligation: assert_7_1234
Property: assert
Result: ✅ pass

Obligation: cast_bv1_nonneg_ensures_6_1203
Property: assert
Result: ✅ pass

Obligation: assert_9_1349
Property: assert
Result: ✅ pass

Obligation: cast_bv16_nonneg_ensures_8_1318
Property: assert
Result: ✅ pass

Obligation: assert_11_1466
Property: assert
Result: ✅ pass

Obligation: cast_bv128_nonneg_ensures_10_1435
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castExprSeed (options := .quiet)

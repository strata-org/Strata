/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: dalek-lite `curve25519-dalek/src/specs/scalar_specs.rs`
  `spec_clamp_integer`, `is_clamped_integer` — X25519 scalar clamping uses
  bitwise `&` and `|` on `u8` bytes:
    bytes[0] & 0b1111_1000
    (bytes[31] & 0b0111_1111) | 0b0100_0000
- Source: dalek-lite scalar multiplication — bit extraction uses `>>` to read
  individual scalar bits; conditional swap uses `^` and `~` for constant-time
  branching; nibble reconstruction uses `<<` and `|`.
- Implemented: bitwise operators (`&`, `|`, `^`, `>>`, `>>s`, `<<`, `~`) on `bvN`
  types are now supported in the Boole grammar and lower to the corresponding
  `Bv{N}.And`, `Bv{N}.Or`, `Bv{N}.Xor`, `Bv{N}.UShr`, `Bv{N}.SShr`, `Bv{N}.Shl`,
  `Bv{N}.Not` Core operations. `>>` is unsigned (UShr); `>>s` is signed (SShr).
-/

-- Exercises & and | (X25519 scalar clamping).
private def bitvectorOpsSeed : Strata.Program :=
#strata
program Boole;

procedure clamp_seed(b0: bv8, b31: bv8) returns (r0: bv8, r31: bv8)
spec {
  ensures r0  == b0  & bv{8}(0b11111000);
  ensures r31 == (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
  ensures r0  & bv{8}(0b00000111) == bv{8}(0);
  ensures r31 & bv{8}(0b10000000) == bv{8}(0);
  ensures r31 & bv{8}(0b01000000) == bv{8}(0b01000000);
}
{
  r0  := b0  & bv{8}(0b11111000);
  r31 := (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
};
#end

/--
info:
Obligation: clamp_seed_ensures_0_1142
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_1_1184
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_2_1248
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_3_1295
Property: assert
Result: ✅ pass

Obligation: clamp_seed_ensures_4_1342
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorOpsSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole bitvectorOpsSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

-- Exercises ~, ^, >>, << (bit extraction, conditional swap, nibble ops).
private def bitvectorShiftXorSeed : Strata.Program :=
#strata
program Boole;

procedure bv_shift_xor(b: bv8, k: bv8) returns (r_not: bv8, r_xor: bv8, r_hi: bv8, r_lo: bv8)
spec {
  ensures r_not == ~b;
  ensures r_xor == b ^ k;
  ensures r_hi  == b >> bv{8}(4);
  ensures r_lo  == b << bv{8}(4);
  // b AND its complement is always zero
  ensures b & ~b == bv{8}(0);
  // b XOR itself is always zero
  ensures b ^ b == bv{8}(0);
  // logical right shift fills upper bits with 0
  ensures (b >> bv{8}(4)) & bv{8}(0b11110000) == bv{8}(0);
  // left shift clears lower bits
  ensures (b << bv{8}(4)) & bv{8}(0b00001111) == bv{8}(0);
}
{
  r_not := ~b;
  r_xor := b ^ k;
  r_hi  := b >> bv{8}(4);
  r_lo  := b << bv{8}(4);
};
#end

/--
info:
Obligation: bv_shift_xor_ensures_0_2334
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_1_2357
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_2_2383
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_3_2417
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_4_2492
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_5_2555
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_6_2633
Property: assert
Result: ✅ pass

Obligation: bv_shift_xor_ensures_7_2726
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorShiftXorSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole bitvectorShiftXorSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

-- Exercises >>s (arithmetic/signed right shift): vacated bits are filled with
-- the sign bit, unlike >> which fills with 0.
private def bitvectorSShrSeed : Strata.Program :=
#strata
program Boole;

procedure bv_sshr(b: bv8) returns (r: bv8)
spec {
  ensures r == b >>s bv{8}(1);
  // negative value: sign bit propagates into vacated position
  ensures bv{8}(0b10000000) >>s bv{8}(1) == bv{8}(0b11000000);
  // positive value: behaves like unsigned shift
  ensures bv{8}(0b01000000) >>s bv{8}(1) == bv{8}(0b00100000);
}
{
  r := b >>s bv{8}(1);
};
#end

/--
info:
Obligation: bv_sshr_ensures_0_3958
Property: assert
Result: ✅ pass

Obligation: bv_sshr_ensures_1_4052
Property: assert
Result: ✅ pass

Obligation: bv_sshr_ensures_2_4164
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorSShrSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole bitvectorSShrSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

-- Exercises signed bitvector comparisons (<s, <=s, >s, >=s).
-- In bv8 signed interpretation: 0xFF = -1, 0x7F = 127.
private def bitvectorSignedCmpSeed : Strata.Program :=
#strata
program Boole;

procedure bv_signed_cmp(a: bv8, b: bv8) returns ()
spec {
  ensures bv{8}(255) <s  bv{8}(0);
  ensures bv{8}(127) >s  bv{8}(0);
  ensures bv{8}(255) <=s bv{8}(0);
  ensures bv{8}(127) >=s bv{8}(0);
  ensures bv{8}(0)   <=s bv{8}(0);
  ensures bv{8}(0)   >=s bv{8}(0);
  ensures bv{8}(255) <s  bv{8}(1);
}
{ };
#end

/--
info:
Obligation: bv_signed_cmp_ensures_0_4945
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_1_4980
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_2_5015
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_3_5050
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_4_5085
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_5_5120
Property: assert
Result: ✅ pass

Obligation: bv_signed_cmp_ensures_6_5155
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bitvectorSignedCmpSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole bitvectorSignedCmpSeed := by
  gen_smt_vcs_boole
  all_goals (first | grind | decide)

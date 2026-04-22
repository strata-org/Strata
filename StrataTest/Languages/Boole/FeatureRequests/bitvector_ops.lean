/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: dalek-lite `curve25519-dalek/src/specs/scalar_specs.rs`
  `spec_clamp_integer`, `is_clamped_integer` — X25519 scalar clamping uses
  bitwise `&` and `|` on `u8` bytes:
    bytes[0] & 0b1111_1000
    (bytes[31] & 0b0111_1111) | 0b0100_0000
- Implemented: bitwise operators (`&`, `|`, `^`, `>>`, `<<`, `~`) on `bvN` types
  are now supported in the Boole grammar and lower to the corresponding
  `Bv{N}.And`, `Bv{N}.Or`, `Bv{N}.Xor`, `Bv{N}.Shl`, `Bv{N}.UShr`, `Bv{N}.SShr`,
  `Bv{N}.Not` Core operations.
-/

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

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" bitvectorOpsSeed (options := .quiet)

example : Strata.smtVCsCorrect bitvectorOpsSeed := by
  gen_smt_vcs
  all_goals (first | grind | decide)

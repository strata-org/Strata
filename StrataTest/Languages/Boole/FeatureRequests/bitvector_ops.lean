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
- Gap: bitwise operators (`&`, `|`, `^`, `>>`, `<<`) on `bvN` types are absent
  from the Boole grammar. `bv8`/`bv32`/`bv64` types exist and lower to Core
  bitvectors, but there is no surface syntax for bitwise expressions.
- Remaining gap: native `&`, `|`, `>>`, `<<` operators on `bvN` types in Boole,
  matching the Verus `u8`/`u64` bitvector arithmetic model.
-/

private def bitvectorOpsSeed : Strata.Program :=
#strata
program Boole;

// procedure clamp_seed(b0: bv8, b31: bv8) returns (r0: bv8, r31: bv8)
// spec {
//   ensures r0  == b0  & bv{8}(0b11111000);
//   ensures r31 == (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
//   ensures r0  & bv{8}(0b00000111) == bv{8}(0);
//   ensures r31 & bv{8}(0b10000000) == bv{8}(0);
//   ensures r31 & bv{8}(0b01000000) == bv{8}(0b01000000);
// }
// {
//   r0  := b0  & bv{8}(0b11111000);
//   r31 := (b31 & bv{8}(0b01111111)) | bv{8}(0b01000000);
// };
#end

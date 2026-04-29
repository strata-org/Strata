/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: VeruSAGE-Bench Vest
  `regular__leb128__impl2__lemma_spec_parse_low_7_bits.rs`
- Verus context: LEB128 encodes integers as a sequence of bytes where bit 7
  is a continuation flag and bits [6:0] carry data. The proof of
  `lemma_spec_parse_low_7_bits` discharges two bitvector identities
  via `by (bit_vector)`:
    assert(take_low_7_bits!(take_low_7_bits!(s0)) == take_low_7_bits!(s0))
      by (bit_vector);
    assert(take_low_7_bits!(rest << 7 | take_low_7_bits!(s0) as UInt)
      == take_low_7_bits!(s0)) by (bit_vector);
- Gap: Boole has no `by (bit_vector)` proof block. Both identities must be
  stated as explicit axioms rather than discharged automatically.
- Remaining gap: a proof-mode block that routes pure bitvector sub-goals to
  a bitvector decision procedure without explicit axioms.
-/

private def bitvectorProofModeSeed : Strata.Program :=
#strata
program Boole;

// function low7(b: bv8) : bv8;
// axiom (∀ b: bv8 . low7(b) == b & bv{8}(127));
//
// procedure leb128_low7_seed(s: Map int bv8, len: int) returns ()
// spec {
//   requires 0 < len;
//   ensures leb128_parse_low7(s, len) == low7(s[0]);
// }
// {
//   if s[0] & bv{8}(128) != bv{8}(0) {
//     // continuation byte
//     assert low7(rest << 7 | low7(s[0])) == low7(s[0]) by (bit_vector);
//   } else {
//     // terminal byte
//     assert low7(low7(s[0])) == low7(s[0]) by (bit_vector);
//   };
// };
#end

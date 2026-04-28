/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: dalek-lite `curve25519-dalek/src/specs/scalar_specs.rs`
  `reconstruct(naf: Seq<i8>) -> int` decodes a Non-Adjacent Form scalar;
  the recursive case passes `naf.skip(1)` — the tail from index 1:
    if naf.len() == 0 { 0 }
    else { (naf[0] as int) + 2 * reconstruct(naf.skip(1)) }
  `product_of_scalars` uses `scalars.subrange(0, last)`.
- Gap: Boole `Sequence T` types do not lower end to end, and the grammar
  has no surface syntax for `subrange(lo, hi)`, `skip(n)`, `take(n)`,
  or `drop_first()`.
- Remaining gap: native `Sequence T` in Boole with slicing operations
  matching the Verus `vstd::prelude::Seq` interface.
-/

private def seqSlicingSeed : Strata.Program :=
#strata
program Boole;

// function reconstruct(naf: Sequence int) : int;
//   decreases naf.len();
// {
//   if naf.len() == 0 { 0 }
//   else { naf[0] + 2 * reconstruct(naf.skip(1)) }
// }
//
// procedure naf_reconstruct_seed(naf: Sequence int) returns ()
// spec {
//   requires 0 < naf.len();
//   ensures reconstruct(naf) == naf[0] + 2 * reconstruct(naf.skip(1));
// }
// { assert reconstruct(naf) == naf[0] + 2 * reconstruct(naf.skip(1)); };
#end

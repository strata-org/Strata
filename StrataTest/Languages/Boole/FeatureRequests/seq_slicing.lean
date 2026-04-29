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

Implemented:
- `Sequence T` type translates to Core's `Sequence` type constructor.
- Core Grammar ops (inherited): `Sequence.length(s)`, `Sequence.select(s,i)`,
  `Sequence.take(s,n)`, `Sequence.drop(s,n)`, `Sequence.append`, etc.
- Boole-specific additions: `Sequence.skip(s,n)`, `Sequence.dropFirst(s)`,
  `Sequence.subrange(s,lo,hi)`.
- Dot-method syntax (s.len()) is NOT used: the DDM init dialect parses
  `id.id` as a qualified identifier before Expr-level trailing rules apply.
  Using "Sequence.xxx" as a single string keyword token avoids this.

Remaining gap:
- Recursive spec functions over sequences require int-based termination
  proofs; the `reconstruct` example remains commented out until that closes.
-/

private def seqSlicingSeed : Strata.Program :=
#strata
program Boole;

function seq_sum_first_two(s: Sequence int) : int;
axiom ∀ s: Sequence int .
  Sequence.length(s) >= 2 ==>
    seq_sum_first_two(s) == Sequence.select(s, 0) + Sequence.select(s, 1);

procedure seq_slicing_seed(s: Sequence int) returns (head: int, tail: Sequence int, mid: Sequence int)
spec {
  requires Sequence.length(s) >= 4;
  ensures head == Sequence.select(s, 0);
  ensures Sequence.length(tail) == Sequence.length(s) - 1;
  ensures Sequence.length(mid) == 2;
  ensures Sequence.select(mid, 0) == Sequence.select(s, 1);
  ensures Sequence.select(mid, 1) == Sequence.select(s, 2);
}
{
  head := Sequence.select(s, 0);
  tail := Sequence.skip(s, 1);
  mid  := Sequence.subrange(s, 1, 3);
};

// Recursive reconstruct — target shape, not yet verifiable:
// requires int-based termination proofs (open gap).
//
// function reconstruct(naf: Sequence int) : int
//   decreases Sequence.length(naf);
// {
//   if Sequence.length(naf) == 0 { 0 }
//   else { Sequence.select(naf, 0) + 2 * reconstruct(Sequence.skip(naf, 1)) }
// }
#end

/-- info:
Obligation: seq_slicing_seed_ensures_2_1634
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_3_1675
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_4_1734
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_5_1771
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_6_1831
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" seqSlicingSeed (options := .quiet)

example : Strata.smtVCsCorrect seqSlicingSeed := by
  gen_smt_vcs
  all_goals (try grind)

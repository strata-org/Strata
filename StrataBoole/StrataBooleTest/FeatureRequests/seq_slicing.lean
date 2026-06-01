/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

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

-/

private def seqSlicingSeed : StrataDDM.Program :=
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

procedure seq_empty_bv64_seed() returns (s: Sequence bv64)
spec {
  ensures Sequence.length(s) == 1;
  ensures Sequence.select(s, 0) == bv{64}(0);
}
{
  s := Sequence.build(Sequence.empty_bv64, bv{64}(0));
};

rec function reconstruct(naf: Sequence int) : int
  decreases Sequence.length(naf)
{
  if Sequence.length(naf) == 0 then
    0
  else
    Sequence.select(naf, 0) + 2 * reconstruct(Sequence.skip(naf, 1))
}
;
#end

/--
info:
Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_2_1478_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_5_1615_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_5_1615_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_6_1675_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_post_seq_slicing_seed_ensures_6_1675_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_head_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_tail_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_mid_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_mid_calls_Sequence.take_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_2_1478
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_3_1519
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_4_1578
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_5_1615
Property: assert
Result: ✅ pass

Obligation: seq_slicing_seed_ensures_6_1675
Property: assert
Result: ✅ pass

Obligation: seq_empty_bv64_seed_post_seq_empty_bv64_seed_ensures_8_1946_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_empty_bv64_seed_ensures_7_1911
Property: assert
Result: ✅ pass

Obligation: seq_empty_bv64_seed_ensures_8_1946
Property: assert
Result: ✅ pass

Obligation: reconstruct_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: reconstruct_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: reconstruct_terminates_0
Property: assert
Result: ✅ pass

Obligation: reconstruct_terminates_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" seqSlicingSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole seqSlicingSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)

-- Shape test: Sequence.select on an empty sequence currently produces no
-- out-of-bounds precondition VC (that guard is tracked separately).
-- The ensures clause passes because the result is unconstrained.
private def seqOutOfBoundsSeed : StrataDDM.Program :=
#strata
program Boole;

procedure seq_oob_seed() returns (v: int)
spec {
  ensures v == 0;
}
{
  v := Sequence.select(Sequence.empty_int, 0);
};
#end

/-- info:
Obligation: set_v_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: seq_oob_seed_ensures_0_4986
Property: assert
Result: ❓ unknown-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" seqOutOfBoundsSeed (options := .quiet)

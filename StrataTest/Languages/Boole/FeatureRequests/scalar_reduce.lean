/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchor:
- Source: dalek-lite `curve25519-dalek/src/scalar.rs`
  `Scalar::from_bytes_mod_order` (line 273–291) — reduces a 32-byte input
  modulo the group order ℓ and returns a canonical scalar:
    pub fn from_bytes_mod_order(bytes: [u8; 32]) -> (result: Scalar)
        ensures
            scalar_as_canonical(&result) == u8_32_as_group_canonical(bytes),
            is_canonical_scalar(&result),
    {
        let s_unreduced = Scalar { bytes };
        s_unreduced.reduce()
    }

Implemented:
- `ByteArray32` and `Scalar` are kept abstract — no byte-array indexing or
  struct-field access is needed for this seed.
- `u8_32_as_group_canonical` stays abstract (an uninterpreted spec function);
  its recursive byte-accumulation definition is the remaining open gap for
  Benchmark 2 (requires int-based termination over sequences).
- Two axioms capture exactly what `reduce` guarantees:
    scalar_as_canonical(reduce(b)) == u8_32_as_group_canonical(b)
    is_canonical_scalar(reduce(b))
- The 3-statement procedure body verifies by axiom instantiation alone.

Remaining gap:
- `[u8; 32]` byte arrays modeled as `Map int bv8` so `u8_32_as_group_canonical`
  can be spelled out recursively (sequence slicing + int termination needed).
- Struct field access (`Scalar { bytes }`) not yet modeled; kept abstract here.
-/

private def scalarReduceSeed : Strata.Program :=
#strata
program Boole;

type ByteArray32;
type Scalar;

function reduce(b: ByteArray32) : Scalar;
function scalar_as_canonical(s: Scalar) : int;
function u8_32_as_group_canonical(b: ByteArray32) : int;
function is_canonical_scalar(s: Scalar) : bool;

axiom (∀ b: ByteArray32 . scalar_as_canonical(reduce(b)) == u8_32_as_group_canonical(b));
axiom (∀ b: ByteArray32 . is_canonical_scalar(reduce(b)));

procedure from_bytes_mod_order(bytes: ByteArray32) returns (result: Scalar)
spec {
  ensures scalar_as_canonical(result) == u8_32_as_group_canonical(bytes);
  ensures is_canonical_scalar(result);
}
{
  result := reduce(bytes);
};
#end

/-- info:
Obligation: from_bytes_mod_order_ensures_2_2014
Property: assert
Result: ✅ pass

Obligation: from_bytes_mod_order_ensures_3_2088
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" scalarReduceSeed (options := .quiet)

example : Strata.smtVCsCorrect scalarReduceSeed := by
  gen_smt_vcs
  all_goals (try grind)

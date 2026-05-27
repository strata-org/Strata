/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: VeruSAGE-Bench Vest
  `properties__SecureSpecCombinator__corollary_parse_surjective.rs`
  `regular__leb128__impl2__lemma_spec_parse_low_7_bits.rs`
- Verus features:
  (P) `Option<(int, T)>` as spec function return type:
      `spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>`
  (Q) `matches` destructuring in `ensures` and `exists` clauses:
      `ensures self.spec_parse(s) matches Some((_, x)) ==> low7(x) == low7(s[0])`
      `ensures exists|b| self.spec_parse(b) matches Some((_, v_)) && v_ == v`
  (R) `#[verifier::external_body]` on `theorem_serialize_parse_roundtrip`:
      the roundtrip lemma is trusted; `corollary_parse_surjective` calls it.
- Gap: Boole has no `Option<T>` type and no `matches` destructuring in spec
  clauses. A spec function that may fail must be encoded as a boolean
  `is_some` flag paired with separate component functions.
  The natural postcondition `f(x) matches Some((n, v)) ==> P(v)` must be
  rewritten as `f_is_some(x) ==> P(f_val(x))`.
- Remaining gap: native `Option<T>` in Boole spec functions and `matches`
  destructuring in `ensures` and `exists` clauses.
-/

private def optionMatchesSeed : Strata.Program :=
#strata
program Boole;

// type Value;
//
// function spec_parse(b: Map int bv8, n: int) : Option (int, Value);
// function spec_serialize(v: Value) : Map int bv8;
// function serialize_len(v: Value) : int;
//
// // trusted roundtrip (#[verifier::external_body] equivalent)
// axiom (∀ v: Value .
//   spec_parse(spec_serialize(v), serialize_len(v))
//     matches Some((_, v')) ==> v' == v);
//
// // corollary_parse_surjective
// procedure parse_surjective_seed(v: Value) returns ()
// spec {
//   ensures ∃ b: Map int bv8, n: int .
//     spec_parse(b, n) matches Some((_, v_)) && v_ == v;
// }
// {
//   assert spec_parse(spec_serialize(v), serialize_len(v))
//            matches Some((_, v)) by { theorem_serialize_parse_roundtrip(v); };
// };
#end

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
- Verus features:
  (J) Traits with `spec fn` and `proof fn` methods:
      `pub trait SpecCombinator { spec fn spec_parse(...); spec fn spec_serialize(...); }`
      `pub trait SecureSpecCombinator: SpecCombinator { proof fn theorem_serialize_parse_roundtrip(...); }`
  (K) `matches` pattern in `ensures` clauses:
      `ensures exists|b| self.spec_parse(b) matches Some((_, v_)) && v_ == v`
  (L) `#[verifier::external_body]` — marks a proof fn body as trusted/opaque.
- Gap: Boole has no trait or interface construct. Spec methods must be
  expressed as top-level abstract functions. Pattern matching in `ensures`
  (the `matches` form) is absent. There is no equivalent of
  `#[verifier::external_body]` for selectively trusting a procedure body.
- Remaining gap: trait/interface declarations with spec and proof methods,
  `matches` pattern syntax in ensures, and `external_body` for individual
  procedures.
-/

private def traitSpecMethodsSeed : Strata.Program :=
#strata
program Boole;

// interface SpecCombinator (V: Type) {
//   spec function spec_parse(s: Sequence bv8) : Option (int, V);
//   spec function spec_serialize(v: V) : Sequence bv8;
// }
//
// interface SecureSpecCombinator (V: Type) extends SpecCombinator V {
//   // trusted roundtrip (external_body equivalent)
//   lemma theorem_serialize_parse_roundtrip(v: V)
//   spec {
//     ensures spec_parse(spec_serialize(v))
//               matches Some((_, v')) ==> v' == v;
//   };
//
//   lemma corollary_parse_surjective(v: V)
//   spec {
//     ensures ∃ b: Sequence bv8 . spec_parse(b) matches Some((_, v_)) && v_ == v;
//   }
//   {
//     theorem_serialize_parse_roundtrip(v);
//   };
// }
#end

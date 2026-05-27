/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchor:
- Source: dalek-lite `curve25519-dalek/src/montgomery.rs`
  `MontgomeryPoint::mul_clamped` (line 408) and `mul_bits_be` (line 519) both
  use inline let-binding blocks inside their `ensures` clauses:
    ensures ({
      let P = canonical_montgomery_lift(montgomery_point_as_nat(self));
      let clamped_bytes = spec_clamp_integer(bytes);
      let n = u8_32_as_nat(&clamped_bytes);
      let R = montgomery_scalar_mul(P, n);
      montgomery_point_as_nat(result) == u_coordinate(R)
    }),
  Each let binding names a subexpression used only within the postcondition,
  keeping complex multi-step specs readable without auxiliary definitions.
- Gap: Boole `spec { ensures ... }` clauses previously accepted boolean
  expressions only — no inline `let` binding syntax.
- Implementation: `let v := value in body` is now a first-class Boole
  expression form (Grammar.lean) that lowers by substituting the converted
  value expression for the bound variable in the converted body (Verify.lean
  `toCoreExpr`).
-/

private def embeddedPostconditionSeed : Strata.Program :=
#strata
program Boole;

function shifted(n: int, k: int) : int;
axiom (∀ n: int, k: int . shifted(n, k) == n + k);

function negated(x: int) : int;
axiom (∀ x: int . negated(x) == -x);

procedure shift_negate(n: int, k: int) returns (r: int)
spec {
  ensures let s : int := shifted(n, k) in
          let d : int := negated(s) in
          r == d;
}
{ r := -(n + k); };
#end

/-- info:
Obligation: shift_negate_ensures_2_1480
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" embeddedPostconditionSeed (options := .quiet)

example : Strata.smtVCsCorrect embeddedPostconditionSeed := by
  gen_smt_vcs
  all_goals (try grind)

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from dalek-lite `curve25519-dalek/src/specs/field_specs.rs`:
  pub struct FieldElement51 { pub(crate) limbs: [u64; 5] }
  pub open spec fn u64_5_bounded(limbs: [u64; 5], bit_limit: u64) -> bool {
      forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << bit_limit)
  }

The `[u64; 5]` array-typed field is modelled here with unrolled `bv64` limbs
(remaining gap: fixed-size array fields). The unsigned comparison `<u` is used
for the bit-limit bound check, matching `u64 < threshold` semantics. The
forall-quantified bound check is unrolled across the 5 limbs.

Dot notation `val.field` works for both `var`-declared record locals and for
function/procedure parameters whose type is a record declared in the same
program. In both cases `val.field` desugars to `T..field(val)` during Boole→Core
translation; the elaborator resolves `T` from the binding's stored TypeExpr.

Remaining gap:
- Fixed-size array fields (`[u64; 5]`).
-/

private def structFieldAccessSeed : Strata.Program :=
#strata
program Boole;

// Near dalek's FieldElement51 { limbs: [u64; 5] } — unrolled as bv64 limbs.
type FieldElement51 := { limb0: bv64, limb1: bv64, limb2: bv64, limb3: bv64, limb4: bv64 };

// Models u64_5_bounded with bit_limit=51: each limb below 2^51.
// Uses dot notation on the `fe` parameter (same desugaring as var-locals).
// Uses <u (unsigned less-than) matching u64 comparison semantics.
// bv64 literals: 2^51 = 2251799813685248, 2^52 = 4503599627370496.
// (Integer << is now supported for int types; bv64 literal syntax uses bv{64}(n).)
function fe51_bounded(fe: FieldElement51) : bool
{
  fe.limb0 <u bv{64}(2251799813685248) &&
  fe.limb1 <u bv{64}(2251799813685248) &&
  fe.limb2 <u bv{64}(2251799813685248) &&
  fe.limb3 <u bv{64}(2251799813685248) &&
  fe.limb4 <u bv{64}(2251799813685248)
}

// If a and b are 51-bit bounded, each sum limb is less than 2^52 = 4503599627370496.
// Uses dot notation on `var`-declared locals (a, b, r).
// bv64 addition does not wrap since both operands are < 2^51, so sum < 2^52 < 2^64.
procedure add_bounded(
  l0: bv64, l1: bv64, l2: bv64, l3: bv64, l4: bv64,
  r0: bv64, r1: bv64, r2: bv64, r3: bv64, r4: bv64
) returns (ok: bool)
spec {
  requires l0 <u bv{64}(2251799813685248);
  requires l1 <u bv{64}(2251799813685248);
  requires l2 <u bv{64}(2251799813685248);
  requires l3 <u bv{64}(2251799813685248);
  requires l4 <u bv{64}(2251799813685248);
  requires r0 <u bv{64}(2251799813685248);
  requires r1 <u bv{64}(2251799813685248);
  requires r2 <u bv{64}(2251799813685248);
  requires r3 <u bv{64}(2251799813685248);
  requires r4 <u bv{64}(2251799813685248);
  ensures ok;
}
{
  var a : FieldElement51;
  var b : FieldElement51;
  var r : FieldElement51;

  a := FieldElement51_mk(l0, l1, l2, l3, l4);
  b := FieldElement51_mk(r0, r1, r2, r3, r4);
  r := FieldElement51_mk(a.limb0 + b.limb0,
                         a.limb1 + b.limb1,
                         a.limb2 + b.limb2,
                         a.limb3 + b.limb3,
                         a.limb4 + b.limb4);

  // Dot notation on var-locals: r.limb0 == a.limb0 + b.limb0
  assert r.limb0 == a.limb0 + b.limb0;
  assert r.limb0 <u bv{64}(4503599627370496);
  ok := r.limb0 <u bv{64}(4503599627370496) && r.limb1 <u bv{64}(4503599627370496) &&
        r.limb2 <u bv{64}(4503599627370496) && r.limb3 <u bv{64}(4503599627370496) &&
        r.limb4 <u bv{64}(4503599627370496);
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" structFieldAccessSeed (options := .quiet)

-- Exercises integer << with a constant shift amount (encoded as x * 2^n).
-- `1 << 51` is translated to `1 * 2251799813685248` by Boole→Core; the SMT
-- solver sees plain linear-integer arithmetic with no bit-vector theory.
private def intShlSeed : Strata.Program :=
#strata
program Boole;

procedure fe51_limb_bounded(x: int) returns (ok: bool)
spec {
  requires 0 <= x;
  requires x < (1 << 51);
  ensures ok;
}
{
  ok := x < (1 << 51);
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" intShlSeed (options := .quiet)

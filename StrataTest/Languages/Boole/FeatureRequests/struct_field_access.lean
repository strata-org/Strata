/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors:
- Source: dalek-lite `curve25519-dalek/src/specs/field_specs.rs`
  `FieldElement51` is a 5-limb 255-bit field element:
    pub struct FieldElement51 { pub(crate) limbs: [u64; 5] }
  Every dalek spec function accesses struct fields directly:
    pub open spec fn u64_5_bounded(limbs: [u64; 5], bit_limit: u64) -> bool {
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << bit_limit)
    }
    pub open spec fn spec_add_fe51_limbs(a: &FieldElement51, b: &FieldElement51)
        -> FieldElement51 {
        FieldElement51 { limbs: [a.limbs[0] + b.limbs[0], ..., a.limbs[4] + b.limbs[4]] }
    }
  `edwards_specs.rs` uses `.X`, `.Y`, `.Z`, `.T` fields on `EdwardsPoint`.
- Gap: Boole has no record/struct type with named field access. Structs with
  fields like `fe.limbs[i]` or `p.X` must be flattened into separate scalar
  parameters or encoded as `Map int T`. There is no struct literal syntax and
  no `.field` accessor in Boole expressions.
- Remaining gap: record/struct type declarations in Boole with named fields,
  field accessor expressions (`p.field`), struct literal construction
  (`T { f1: v1, f2: v2 }`), and quantification over fixed-size field arrays.
-/

private def structFieldAccessSeed : Strata.Program :=
#strata
program Boole;

// type FieldElement51 := { limb0: int, limb1: int, limb2: int, limb3: int, limb4: int };
//
// function fe_bounded(fe: FieldElement51, bit_limit: int) : bool;
// axiom (∀ fe: FieldElement51, bit_limit: int .
//   fe_bounded(fe, bit_limit) <==>
//     fe.limb0 < bit_limit && fe.limb1 < bit_limit &&
//     fe.limb2 < bit_limit && fe.limb3 < bit_limit && fe.limb4 < bit_limit);
//
// procedure fe_add_seed(a: FieldElement51, b: FieldElement51) returns (r: FieldElement51)
// spec {
//   requires fe_bounded(a, 2251799813685248);   // 2^51
//   requires fe_bounded(b, 2251799813685248);
//   ensures  r.limb0 == a.limb0 + b.limb0;
//   ensures  r.limb1 == a.limb1 + b.limb1;
//   ensures  r.limb2 == a.limb2 + b.limb2;
//   ensures  r.limb3 == a.limb3 + b.limb3;
//   ensures  r.limb4 == a.limb4 + b.limb4;
// }
// {
//   r := FieldElement51 {
//     limb0: a.limb0 + b.limb0,
//     limb1: a.limb1 + b.limb1,
//     limb2: a.limb2 + b.limb2,
//     limb3: a.limb3 + b.limb3,
//     limb4: a.limb4 + b.limb4,
//   };
// };
#end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Tests all three SMT-LIB 2.7 cast directions:
  1. `e as_int`   — unsigned bv → Int  (ubv_to_int)
  2. `e as_sint`  — signed bv → Int    (sbv_to_int)
  3. `e as_bv{n}` — Int → bv           ((_ int_to_bv n))
-/

private def castAllDirectionsSeed : StrataDDM.Program :=
#strata
program Boole;

// (1) ubv_to_int: unsigned interpretation, always in [0, 255]
procedure test_ubv_to_int(x: bv8) returns ()
spec {
  ensures x as_int >= 0;
  ensures x as_int <= 255;
} {
  exit test_ubv_to_int;
};

// (2) sbv_to_int: signed interpretation, range [-128, 127]
procedure test_sbv_to_int(x: bv8) returns ()
spec {
  ensures x as_sint >= -128;
  ensures x as_sint <= 127;
} {
  exit test_sbv_to_int;
};

// (3) int_to_bv: truncating cast, result as_int == n for n in [0, 255]
procedure test_int_to_bv(n: int) returns (result: bv8)
spec {
  requires 0 <= n && n < 256;
  ensures result as_int == n;
} {
  result := n as_bv8;
  exit test_int_to_bv;
};

// Round-trip: (n as_bv8) as_int == n for n in [0, 255]
procedure test_roundtrip(n: int) returns ()
spec {
  requires 0 <= n && n < 256;
  ensures (n as_bv8) as_int == n;
} {
  exit test_roundtrip;
};

// Signed and unsigned agree when value is non-negative
procedure test_sign_agreement(x: bv8) returns ()
spec {
  requires x as_sint >= 0;
  ensures x as_int == x as_sint;
} {
  exit test_sign_agreement;
};
#end

/-- info:
Obligation: test_ubv_to_int_ensures_0_554
Property: assert
Result: ✅ pass

Obligation: test_ubv_to_int_ensures_1_579
Property: assert
Result: ✅ pass

Obligation: test_sbv_to_int_ensures_2_750
Property: assert
Result: ✅ pass

Obligation: test_sbv_to_int_ensures_3_779
Property: assert
Result: ✅ pass

Obligation: test_int_to_bv_ensures_5_1003
Property: assert
Result: ✅ pass

Obligation: test_roundtrip_ensures_7_1223
Property: assert
Result: ✅ pass

Obligation: test_sign_agreement_ensures_9_1427
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" castAllDirectionsSeed (options := .quiet)

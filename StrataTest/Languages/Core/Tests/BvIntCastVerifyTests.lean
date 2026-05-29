/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
End-to-end verification tests for the three Bv↔Int cast built-in functions,
exercised all the way through the SMT pipeline via `Strata.Boole.verify`.

- `as_uint(e)` ≙ SMT-LIB 2.7 `ubv_to_int`  — unsigned bv → Int
- `as_sint(e)` ≙ SMT-LIB 2.7 `sbv_to_int`  — signed bv → Int
- `as_bv8(e)`  ≙ SMT-LIB 2.7 `(_ int_to_bv 8)` — Int → bv8
-/

open Strata

private def bvIntCastProgram : Strata.Program :=
#strata
program Core;

procedure test_ubv_nonneg(x : bv8)
spec {
  ensures as_uint(x) >= 0;
}
{
  assume true;
};

procedure test_ubv_concrete()
spec {
  ensures as_uint(bv{8}(255)) == 255;
}
{
  assume true;
};

procedure test_ubv_roundtrip(x : bv8)
spec {
  ensures as_bv8(as_uint(x)) == x;
}
{
  assume true;
};

procedure test_sbv_concrete()
spec {
  ensures as_sint(bv{8}(255)) == -1;
}
{
  assume true;
};

procedure test_ubv_impossible(x : bv8)
spec {
  ensures as_uint(x) >= 256;
}
{
  assume true;
};

#end

/--
info:
Obligation: test_ubv_nonneg_ensures_0_604
Property: assert
Result: ✅ pass

Obligation: test_ubv_concrete_ensures_2_691
Property: assert
Result: ✅ pass

Obligation: test_ubv_roundtrip_ensures_4_797
Property: assert
Result: ✅ pass

Obligation: test_sbv_concrete_ensures_6_892
Property: assert
Result: ✅ pass

Obligation: test_ubv_impossible_ensures_8_998
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bvIntCastProgram (options := .quiet)

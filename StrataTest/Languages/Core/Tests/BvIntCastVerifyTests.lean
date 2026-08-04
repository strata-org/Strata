/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-!
End-to-end verification tests for the three Bv↔Int cast built-in functions,
exercised all the way through the SMT pipeline via `Core.verify`.

- `as_uint(e)` ≙ SMT-LIB 2.7 `ubv_to_int`  — unsigned bv → Int
- `as_sint(e)` ≙ SMT-LIB 2.7 `sbv_to_int`  — signed bv → Int
- `as_bv8(e)`  ≙ SMT-LIB 2.7 `(_ int_to_bv 8)` — Int → bv W8
-/

meta section
open Strata
open StrataDDM (Program)

private def bvIntCastProgram : Program :=
#strata
program Core;

procedure test_ubv_nonneg(x : bv W8)
spec {
  ensures int.ge(bv8.toUInt(x), 0);
}
{
  assume true;
};

procedure test_ubv_concrete()
spec {
  ensures bv8.toUInt(bv{8}(255)) == 255;
}
{
  assume true;
};

procedure test_ubv_roundtrip(x : bv W8)
spec {
  ensures as_bv8(bv8.toUInt(x)) == x;
}
{
  assume true;
};

procedure test_sbv_concrete()
spec {
  ensures bv8.toInt(bv{8}(255)) == int.neg(1);
}
{
  assume true;
};

procedure test_ubv_impossible(x : bv W8)
spec {
  ensures int.ge(bv8.toUInt(x), 256);
}
{
  assume true;
};

procedure test_bv128_ubv_nonneg(x : bv W128)
spec {
  ensures int.ge(bv128.toUInt(x), 0);
}
{
  assume true;
};

procedure test_bv128_sbv_range(x : bv W128)
spec {
  ensures int.le(bv128.toInt(x), bv128.toUInt(x));
}
{
  assume true;
};

procedure test_bv128_concrete()
spec {
  ensures bv128.toUInt(bv{128}(255)) == 255;
}
{
  assume true;
};

#end

private def mkProc (name : String) (postcond : Core.Expression.Expr) : Core.Decl :=
  .proc {
    header := {
      name     := ⟨name, ()⟩
      typeArgs := []
      inputs   := [(⟨"x", ()⟩, .bitvec 8)]
      outputs  := []
    }
    spec := {
      preconditions  := []
      postconditions := [(s!"{name}_ensures_0", { expr := postcond })]
    }
    body := .structured [.assume "body" (.true ()) #[]]
  } #[]

/--
info:
Obligation: test_ubv_nonneg_ensures_0
Property: assert
Result: ✅ pass

Obligation: test_ubv_concrete_ensures_0
Property: assert
Result: ✅ pass

Obligation: test_ubv_roundtrip_ensures_0
Property: assert
Result: ✅ pass

Obligation: test_sbv_concrete_ensures_0
Property: assert
Result: ✅ pass

Obligation: test_ubv_impossible_ensures_0
Property: assert
Result: ❌ fail

Obligation: test_bv128_ubv_nonneg_ensures_0
Property: assert
Result: ✅ pass

Obligation: test_bv128_sbv_range_ensures_0
Property: assert
Result: ✅ pass

Obligation: test_bv128_concrete_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify bvIntCastProgram (options := .quiet)

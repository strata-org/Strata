/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Factory
import Strata.SimpleAPI

/-!
End-to-end verification tests for the three Bv↔Int cast operators,
exercised all the way through the SMT pipeline via `Strata.Core.verifyProgram`.

Factory ops (`Bv{n}.ToUInt`, `Bv{n}.ToInt`, `Int.ToBv{n}`) cannot be called
from `#strata program Core;` text, so programs are constructed programmatically
using the Lean API.

- `Bv{n}.ToUInt` ≙ SMT-LIB 2.7 `ubv_to_int`  — unsigned bv → Int
- `Bv{n}.ToInt`  ≙ SMT-LIB 2.7 `sbv_to_int`  — signed bv → Int
- `Int.ToBv{n}`  ≙ SMT-LIB 2.7 `(_ int_to_bv n)` — Int → bv
-/

namespace Core.BvIntCastVerify

open Lambda Core

private abbrev m := ExprSourceLoc.synthesized "test"

private def xBv8   : Expression.Expr := .fvar m ⟨"x", ()⟩ (.some (.bitvec 8))
private def bv8255 : Expression.Expr := .bitvecConst m 8 (255 : BitVec 8)

private def zero   : Expression.Expr := .intConst m 0
private def i255   : Expression.Expr := .intConst m 255
private def i256   : Expression.Expr := .intConst m 256
private def negOne : Expression.Expr := .intConst m (-1)

private def applyGe (l r : Expression.Expr) : Expression.Expr :=
  .app m (.app m intGeOp l) r

private def mkProc (name : String) (postcond : Expression.Expr) : Decl :=
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
    body := .structured [.assume "body" (.true m) #[]]
  } #[]

private def castVerifyProg : Core.Program :=
  { decls := [
      -- Provable: Bv8.ToUInt is always nonneg
      mkProc "test_ubv_nonneg"
        (applyGe (.app m bv8ToUIntFunc.opExpr xBv8) zero),
      -- Provable: concrete value bv{8}(255) as unsigned == 255
      mkProc "test_ubv_concrete"
        (.eq m (.app m bv8ToUIntFunc.opExpr bv8255) i255),
      -- Provable: unsigned round-trip Int.ToBv8(Bv8.ToUInt(x)) == x
      mkProc "test_ubv_roundtrip"
        (.eq m (.app m int8ToBvFunc.opExpr (.app m bv8ToUIntFunc.opExpr xBv8)) xBv8),
      -- Provable: signed semantics bv{8}(255) as signed == -1
      mkProc "test_sbv_concrete"
        (.eq m (.app m bv8ToIntFunc.opExpr bv8255) negOne),
      -- Failing: Bv8.ToUInt(x) >= 256 is impossible for 8-bit
      mkProc "test_ubv_impossible"
        (applyGe (.app m bv8ToUIntFunc.opExpr xBv8) i256),
    ] }

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
-/
#guard_msgs in
#eval show IO Unit from do
  let results ← EIO.toIO (fun e => IO.Error.userError e)
    (Strata.Core.verifyProgram castVerifyProg Core.VerifyOptions.quiet)
  IO.println (toString results)

end Core.BvIntCastVerify

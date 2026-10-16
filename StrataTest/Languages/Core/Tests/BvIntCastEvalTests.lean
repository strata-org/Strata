/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LExpr
meta import Strata.DL.Lambda.LState
meta import Strata.Languages.Core.Factory

/-!
# Bitvector/Integer Cast Evaluation Tests

Direct evaluation tests for the three Bv↔Int cast operators.

These checks exercise the same factory path used by `CoreBodyExec`; they do
not invoke the SMT encoder or solver.
-/

meta section

namespace Core

open Lambda

/-- Evaluates a unary cast through the Core factory. -/
private def evalCast (name : String) (ty : LMonoTy)
    (arg : LExpr CoreLParams.mono) :
    Except String (LExpr CoreLParams.mono) := do
  let state ← (LState.init.addFactory Core.Factory).mapError (·.message)
  return (LExpr.evalWithLState state.config.fuel state
    (LExpr.mkApp () (.op () name (some ty)) [arg])).fst

/-- info: Except.ok (LExpr.const () Lambda.LConst.intConst 255) -/
#guard_msgs in
#eval evalCast "Bv8.ToUInt" (.arrow (.bitvec 8) .int)
  (.bitvecConst () 8 (BitVec.ofInt 8 255))

/-- info: Except.ok (LExpr.const () Lambda.LConst.intConst (-1)) -/
#guard_msgs in
#eval evalCast "Bv8.ToInt" (.arrow (.bitvec 8) .int)
  (.bitvecConst () 8 (BitVec.ofInt 8 255))

/-- info: Except.ok (LExpr.const () Lambda.LConst.bitvecConst 8 0xff#8) -/
#guard_msgs in
#eval evalCast "Int.ToBv8" (.arrow .int (.bitvec 8)) (.intConst () (-1))

/-- info: Except.ok (LExpr.const () Lambda.LConst.bitvecConst 8 0x00#8) -/
#guard_msgs in
#eval evalCast "Int.ToBv8" (.arrow .int (.bitvec 8)) (.intConst () 256)

end Core

end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the liftHoles pass correctly lifts `.Hole` nodes out of expression
positions, replacing them with fresh `$hole_N` variables.
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.LaurelFormat

open Strata.Laurel

namespace Strata.Laurel

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩
private def bareType (v : HighType) : HighTypeMd := ⟨v, emptyMd⟩

private def mkProc (name : String) (body : StmtExprMd) : Procedure := {
  name := name
  inputs := []
  outputs := []
  preconditions := []
  determinism := .deterministic none
  decreases := none
  isFunctional := false
  body := .Transparent body
  md := emptyMd
}

/-- Hole in a PrimitiveOp argument should be lifted to a fresh variable. -/
def holeInPrimitiveOp : Procedure :=
  mkProc "holeInPrimitiveOp" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Add [bare (.LiteralInt 1), bare .Hole]))))
  ] none))

/-- Bare Hole as LocalVariable initializer should be preserved (translator handles as havoc). -/
def holeAsInitializer : Procedure :=
  mkProc "holeAsInitializer" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt) (some (bare .Hole)))
  ] none))

/-- Hole in assert condition should be lifted. -/
def holeInAssert : Procedure :=
  mkProc "holeInAssert" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .Gt [bare .Hole, bare (.LiteralInt 0)])))
  ] none))

def testProgram : Program := {
  staticProcedures := [holeInPrimitiveOp, holeAsInitializer, holeInAssert]
  staticFields := []
  types := []
}

private def printProgram (p : Program) : IO Unit := do
  for proc in p.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/--
info: procedure holeInPrimitiveOp() returns ⏎
()
deterministic
{ var $hole_0: Core(Any); var x: int := 1 + $hole_0 }
procedure holeAsInitializer() returns ⏎
()
deterministic
{ var x: int := <?> }
procedure holeInAssert() returns ⏎
()
deterministic
{ var $hole_0: Core(Any); assert $hole_0 > 0 }
-/
#guard_msgs in
#eval! printProgram (liftHoles testProgram)

end Laurel

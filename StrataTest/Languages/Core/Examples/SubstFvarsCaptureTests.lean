/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.DL.Lambda.Preconditions
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.StatementEval
-- Test fixtures build Core expressions directly with synthesized provenance

meta section
open StrataDDM (Program)
/-! # Simultaneous substitution tests (Issue 653)

Tests verifying that simultaneous substitution (`substFvars` /
`substFvarsLifting`) avoids variable capture that occurs with the
iterated `substFvar`.
-/

---------------------------------------------------------------------
/-! ## LExprEval: factory function inlining -/

namespace Strata

def issue653Pgm : Program :=
#strata
program Core;

inline function foo(x : int, $__y0 : int) : int { x + $__y0 }

procedure TestFoo()
{
  var y : int;
  assert [fooEq]: (foo(y, 2) == 4);
};

#end

-- foo(y, 2): iterated [x↦$__y0][$__y0↦2] produces 2+2=4 (pass). Correct: y+2≠4 (fail).
/--
info:
Obligation: fooEq
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify issue653Pgm (options := .quiet)

---------------------------------------------------------------------
/-! ## callConditions: procedure call precondition substitution -/

def callCondBugPgm : Program :=
#strata
program Core;

procedure P(x : int, $__y3 : int)
spec {
  requires x == $__y3;
}
{
};

procedure Test()
{
  var y : int;
  havoc y;
  call P(y, 0);
};

#end

-- P(y,0): iterated [x↦$__y3][$__y3↦0] on `x==$__y3` produces 0==0 (pass). Correct: y==0 (fail).
/--
info:
Obligation: callElimAssert_P_requires_0_2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify callCondBugPgm (options := .quiet)

end Strata

---------------------------------------------------------------------
/-! ## substitutePrecondition: iterated capture -/

namespace Core
open Lambda

private def precond : LExpr CoreLParams.mono :=
  .eq (ExprSourceLoc.synthesized "test") (.fvar (ExprSourceLoc.synthesized "test") ⟨"x", ()⟩ (some .int)) (.fvar (ExprSourceLoc.synthesized "test") ⟨"y", ()⟩ (some .int))

private def formals : List (Identifier Unit × LMonoTy) :=
  [(⟨"x", ()⟩, .int), (⟨"y", ()⟩, .int)]

private def actuals : List (LExpr CoreLParams.mono) :=
  [.fvar (ExprSourceLoc.synthesized "test") ⟨"y", ()⟩ (some .int), .intConst (ExprSourceLoc.synthesized "test") 0]

-- f(y,0): iterated [x↦y][y↦0] on `x==y` produces `0==0`. Correct: `y==0`.
/-- info: y == 0 -/
#guard_msgs in
#eval Std.ToFormat.format (substitutePrecondition precond formals actuals)

---------------------------------------------------------------------
/-! ## substitutePrecondition: bvar capture under quantifier -/

private def precondBvar : LExpr CoreLParams.mono :=
  .quant (ExprSourceLoc.synthesized "test") .all "z" (some .int) (.bvar (ExprSourceLoc.synthesized "test") 0)
    (.app (ExprSourceLoc.synthesized "test") (.app (ExprSourceLoc.synthesized "test") (.op (ExprSourceLoc.synthesized "test") ⟨"Int.Gt", ()⟩ (some (.arrow .int (.arrow .int .bool))))
      (.fvar (ExprSourceLoc.synthesized "test") ⟨"x", ()⟩ (some .int))) (.bvar (ExprSourceLoc.synthesized "test") 0))

private def formalsBvar : List (Identifier Unit × LMonoTy) := [(⟨"x", ()⟩, .int)]
private def actualsBvar : List (LExpr CoreLParams.mono) := [.bvar (ExprSourceLoc.synthesized "test") 0]

-- bvar!1 refers to an outer binder not present in this subexpression
-- (collectWFObligations wraps it in a quantifier).
-- Iterated (no lifting): `forall z :: bvar 0 > bvar 0` (x captured by z).
-- Correct (with lifting): `forall z :: bvar 1 > bvar 0` (bvar 1 = outer y).
-- The "out of bounds" error is expected: bvar!1 is only in-bounds when the iterated version incorrectly captures it.
/--
info: forall z : int :: bvar!1 > z
-- Errors: Unsupported construct in lexprToExpr: bvar index out of bounds: 1
Context: Global scope:
Scope 1:
  boundVars: [z]
-/
#guard_msgs in
#eval Std.ToFormat.format (substitutePrecondition precondBvar formalsBvar actualsBvar)

end Core

---------------------------------------------------------------------
/-! ## captureFreevars: value corruption via iterated substitution -/

namespace Core.Statement
open Lambda

private def mkId (s : String) : Identifier Unit := ⟨s, ()⟩
private def mkFv (s : String) : LExpr CoreLParams.mono := .fvar (ExprSourceLoc.synthesized "test") (mkId s) (some .int)
private def mkInt (n : Int) : LExpr CoreLParams.mono := .intConst (ExprSourceLoc.synthesized "test") n
private def mkAdd (a b : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  .app (ExprSourceLoc.synthesized "test") (.app (ExprSourceLoc.synthesized "test") (.op (ExprSourceLoc.synthesized "test") (mkId "Int.Add") (some (.arrow .int (.arrow .int .int)))) a) b

private def testEnv : Env :=
  let e := Env.init
  let e := e.insertInContext (mkId "x", some .int) (mkAdd (mkFv "y") (mkInt 1))
  let e := e.insertInContext (mkId "y", some .int) (mkInt 0)
  e

-- body: x + y, store: x → y+1, y → 0
-- Iterated [x→(y+1)][y→0]: `(0+1) + 0`. Correct: `(y+1) + 0`.
/-- info: y + 1 + 0 -/
#guard_msgs in
#eval Std.ToFormat.format (captureFreevars testEnv [] (mkAdd (mkFv "x") (mkFv "y")))

end Core.Statement
end

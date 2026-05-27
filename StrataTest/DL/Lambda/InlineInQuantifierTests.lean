/-
  Reproducer + verification: inline functions inside quantifier bodies.

  - Confirms the original bug: `LExpr.eval` does not expand an `inline` call
    inside a `forall` body.
  - Confirms the fix: `LExpr.expandInlineCalls` correctly expands the call
    under the binder, and then `LExpr.eval` produces the fully reduced form.
-/
module

meta import all Strata.DL.Lambda.LExprEval

meta section

namespace Lambda
open LExpr LTy.Syntax LExpr.SyntaxMono

private abbrev TP : LExprParams := ⟨Unit, Unit⟩
private instance : Coe String TP.Identifier where coe s := Identifier.mk s ()

-- inline polyEq<a>(x, y) := ∀ (z : a), z == z
private def polyEqFns : Array (LFunc TP) :=
  #[{ name := "polyEq",
      typeArgs := ["a"],
      attr := #[.inline],
      inputs := [("x", mty[%a]), ("y", mty[%a])],
      output := mty[bool],
      body := some esM[∀ (%a): (%0 == %0)] }]

private def polyState : LState TP :=
  { (LState.init : LState TP) with
    config := { (LState.init : LState TP).config with factory := .ofArray polyEqFns } }

-- Top-level call expands as expected.
private def topCall    : LExpr TP.mono := esM[(((~polyEq : int → int → bool) #1) #2)]
private def topExpect  : LExpr TP.mono := esM[∀ (int): (%0 == %0)]
/-- info: true -/
#guard_msgs in
#eval (LExpr.eval 100 polyState topCall) == topExpect

-- Same call wrapped inside a forall: original bug — eval leaves it untouched.
private def quantCall   : LExpr TP.mono :=
  esM[∀ (int): (((~polyEq : int → int → bool) %0) %0)]
private def quantExpect : LExpr TP.mono :=
  esM[∀ (int): (∀ (int): (%0 == %0))]

/-- info: true -/
#guard_msgs in
#eval (LExpr.eval 100 polyState quantCall) == quantCall

/-- info: false -/
#guard_msgs in
#eval (LExpr.eval 100 polyState quantCall) == quantExpect

-- Fix: expandInlineCalls descends through the forall and rewrites the call.
/-- info: true -/
#guard_msgs in
#eval (LExpr.expandInlineCalls polyState.config.factory 100 quantCall) == quantExpect

-- And piping the pre-pass before eval also yields the expected form.
/-- info: true -/
#guard_msgs in
#eval
  (LExpr.eval 100 polyState
    (LExpr.expandInlineCalls polyState.config.factory 100 quantCall)) == quantExpect

end Lambda
end

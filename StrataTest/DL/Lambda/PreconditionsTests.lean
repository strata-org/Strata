/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DL.Lambda.IntBoolFactory
import Strata.DL.Lambda.Preconditions

/-! # Preconditions Tests -/

namespace Lambda

open Std (ToFormat Format format)

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

-- A function with a precondition: safeDiv(x, y) requires y != 0
private def safeDivFunc : LFunc TestParams :=
  { name := "safeDiv"
    inputs := [("x", .int), ("y", .int)]
    output := .int
    preconditions := [.app () (.app () (.op () "!=" .none) (.fvar () "y" .none)) (.intConst () 0)]
  }

private def testFactory : Factory TestParams := #[safeDivFunc]

-- Test: No obligations for expression without function calls
-- Expression: 42
/-- info: [] -/
#guard_msgs in
#eval collectWFObligations testFactory (.intConst () 42)

-- Test: No obligations for call to function without preconditions
private def noPrecondFunc : LFunc TestParams :=
  { name := "add", inputs := [("x", .int), ("y", .int)], output := .int }

private def factoryNoPrecond : Factory TestParams := #[noPrecondFunc]

-- Expression: add(1, 2)
/-- info: [] -/
#guard_msgs in
#eval collectWFObligations factoryNoPrecond
  (.app () (.app () (.op () "add" .none) (.intConst () 1)) (.intConst () 2))

-- safeDiv(a, y)
/-- info: [WFObligation(safeDiv, ((~!= y) #0), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  (.app () (.app () (.op () "safeDiv" .none) (.fvar () "a" .none)) (.fvar () "y" .none))

-- safeDiv(safeDiv(x, y), b)
/-- info: [WFObligation(safeDiv, ((~!= b) #0), ()), WFObligation(safeDiv, ((~!= y) #0), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  (.app () (.app () (.op () "safeDiv" .none)
    (.app () (.app () (.op () "safeDiv" .none) (.fvar () "x" .none)) (.fvar () "y" .none)))
    (.fvar () "b" .none))

-- safeDiv(z, add(x, y))
-- Precondition should become: add(x, y) != 0
private def addFunc : LFunc TestParams :=
  { name := "add", inputs := [("x", .int), ("y", .int)], output := .int }

private def factoryWithAdd : Factory TestParams := #[safeDivFunc, addFunc]

/-- info: [WFObligation(safeDiv, ((~!= ((~add x) y)) #0), ())] -/
#guard_msgs in
#eval collectWFObligations factoryWithAdd
  (.app () (.app () (.op () "safeDiv" .none) (.fvar () "z" .none))
    (.app () (.app () (.op () "add" .none) (.fvar () "x" .none)) (.fvar () "y" .none)))

-- Test: Function call inside a lambda abstraction
-- Expression: \x : int. safeDiv(x, x)
-- The obligation should be: forall x :: x != 0
/-- info: [WFObligation(safeDiv, (∀ ((~!= %0) #0)), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  (.abs () LMonoTy.int
    (.app () (.app () (.op () "safeDiv" .none) (.bvar () 0)) (.bvar () 0)))

-- Test: Function call inside a quantifier with implication guard
-- Expression: forall x :: x > 0 ==> safeDiv(y, x) > 0
-- The obligation should be: forall x :: x > 0 ==> x != 0
-- A hack
private def factoryWithImplies : Factory TestParams :=
  match (@IntBoolFactory TestParams _).addFactoryFunc safeDivFunc with
  | .ok f => f
  | _ => (@IntBoolFactory TestParams _)


-- forall x :: (x > 0) ==> (safeDiv(y, x) > 0)
-- The WF obligation should be: forall x :: (x > 0) ==> (x != 0)
/-- info: [WFObligation(safeDiv, (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) ((~Int.Gt %0) #0)) ((~!= %0) #0))), ())] -/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  (.quant () .all LMonoTy.int (.true ())
    (.app () (.app () (.op () "Bool.Implies" .none)
      (.app () (.app () (.op () "Int.Gt" .none) (.bvar () 0)) (.intConst () 0)))
      (.app () (.app () (.op () "Int.Gt" .none)
        (.app () (.app () (.op () "safeDiv" .none) (.fvar () "y" .none)) (.bvar () 0)))
        (.intConst () 0))))

end Lambda

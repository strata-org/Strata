/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Preconditions

/-! # Preconditions Tests -/

namespace Lambda

open Std (ToFormat Format format)

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
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

end Lambda

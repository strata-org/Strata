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

open LExpr.SyntaxMono LTy.Syntax

-- A function with a precondition: safeDiv(x, y) requires y != 0
private def safeDivFunc : LFunc TestParams :=
  { name := "safeDiv"
    inputs := [("x", .int), ("y", .int)]
    output := .int
    preconditions := [⟨.app () (.app () (.op () "!=" .none) (.fvar () "y" .none)) (.intConst () 0), ()⟩]
  }

private def testFactory : Factory TestParams := .ofArray #[safeDivFunc]

-- Test: No obligations for call to function without preconditions
private def noPrecondFunc : LFunc TestParams :=
  { name := "add", inputs := [("x", .int), ("y", .int)], output := .int }

-- Expression: add(1, 2)
/-- info: [] -/
#guard_msgs in
#eval collectWFObligations (.ofArray #[noPrecondFunc]) esM[((~add #1) #2)]

-- safeDiv(a, y) produces y != 0
/-- info: [WFObligation(safeDiv, (~!= y #0), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory esM[((~safeDiv a) y)]

-- safeDiv(safeDiv(x, y), b) produces b != 0, y != 0
/-- info: [WFObligation(safeDiv, (~!= y #0), ()), WFObligation(safeDiv, (~!= b #0), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[((~safeDiv ((~safeDiv x) y)) b)]

private def addFunc : LFunc TestParams :=
  { name := "add", inputs := [("x", .int), ("y", .int)], output := .int }

private def factoryWithAdd : Factory TestParams := .ofArray #[safeDivFunc, addFunc]

-- safeDiv(z, add(x, y)) produces add(x, y) != 0
/-- info: [WFObligation(safeDiv, (~!= (~add x y) #0), ())] -/
#guard_msgs in
#eval collectWFObligations factoryWithAdd
  esM[((~safeDiv z) ((~add x) y))]

-- Test: Function call inside a lambda abstraction
-- Expression: \x : int. safeDiv(x, x)
-- The obligation should be: forall x :: x != 0
/-- info: [WFObligation(safeDiv, (∀ (bvar:int) (~!= %0 #0)), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[λ (int): ((~safeDiv %0) %0)]

-- Test: Function call inside a quantifier with implication guard
-- Expression: forall x :: x > 0 ==> safeDiv(y, x) > 0
-- The obligation should be: forall x :: x > 0 ==> x != 0

private def factoryWithImplies : Factory TestParams :=
  match (@IntBoolFactory TestParams _).tryPush safeDivFunc with
  | .ok f => f
  | _ => (@IntBoolFactory TestParams _ _)


-- forall x :: (x > 0) ==> (safeDiv(y, x) > 0)
-- The WF obligation is: forall x :: (x > 0) ==> (x != 0)
/--
info: [WFObligation(safeDiv, (∀ (bvar:int) ((~Bool.Implies : (arrow bool (arrow bool bool))) (~Int.Gt %0 #0) (~!= %0 #0))), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[∀ (int):{#true}
    ((~Bool.Implies ((~Int.Gt %0) #0))
      ((~Int.Gt ((~safeDiv y) %0)) #0))]

-- Test: p || safeDiv(y, x) > 0
-- The WF obligation for the RHS should assume ¬p: Bool.Not(p) ==> x != 0
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool)))
 ((~Bool.Not : (arrow bool bool)) p)
 (~!= x #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.Or p) ((~Int.Gt ((~safeDiv y) x)) #0))]

-- Test: p && safeDiv(y, x) > 0
-- The WF obligation for the RHS should assume p: p ==> x != 0
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool))) p (~!= x #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.And p) ((~Int.Gt ((~safeDiv y) x)) #0))]

-- Test: let x := a in safeDiv(2, x)
-- Encoded as (λ (int): ((~safeDiv #2) %0)) a
-- The obligation should be: let x := a in (x != 0)
/-- info: [WFObligation(safeDiv, ((λ (bvar:int) (~!= %0 #0)) a), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[((λ (int): ((~safeDiv #2) %0)) a)]

-- Test: let x := safeDiv(a, b) in x
-- Encoded as (λ (int): %0) (safeDiv(a, b))
-- The obligation comes from the arg: b != 0, emitted at usage site of x
/-- info: [WFObligation(safeDiv, (~!= b #0), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[((λ (int): %0) ((~safeDiv a) b))]

-- Test: let x := safeDiv(a, b) in (p ==> x > 0)
-- The arg obligation b != 0 should inherit the implication context: p ==> b != 0
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool))) p (~!= b #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((λ (int): ((~Bool.Implies p) ((~Int.Gt %0) #0))) ((~safeDiv a) b))]

-- Test: let x := safeDiv(a, b) in (p || x > 0)
-- The arg obligation b != 0 should assume ¬p: ¬p ==> b != 0
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool)))
 ((~Bool.Not : (arrow bool bool)) p)
 (~!= b #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((λ (int): ((~Bool.Or p) ((~Int.Gt %0) #0))) ((~safeDiv a) b))]

-- Test: let x := safeDiv(a, b) in (p && x > 0)
-- The arg obligation b != 0 should assume p: p ==> b != 0
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool))) p (~!= b #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((λ (int): ((~Bool.And p) ((~Int.Gt %0) #0))) ((~safeDiv a) b))]

-- Test: let x := safeDiv(a, b) in 42 (variable not used)
-- No obligations: x is never used so arg preconditions are not needed
/-- info: [] -/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((λ (int): #42) ((~safeDiv a) b))]

-- Test: let x := safeDiv(a, b) in safeDiv(c, x)
-- Arg obligation b != 0 at usage site (unwrapped), plus body obligation x != 0 (wrapped in let)
/-- info: [WFObligation(safeDiv, (~!= b #0), ()), WFObligation(safeDiv, ((λ (bvar:int) (~!= %0 #0)) (~safeDiv a b)), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[((λ (int): ((~safeDiv c) %0)) ((~safeDiv a) b))]

-- Test: true || safeDiv(a, 0) > 0
-- The obligation ¬true ==> 0 != 0 is trivially provable (false premise)
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool)))
 ((~Bool.Not : (arrow bool bool)) #true)
 (~!= #0 #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.Or #true) ((~Int.Gt ((~safeDiv a) #0)) #0))]

-- Test: false && safeDiv(a, 0) > 0
-- The obligation false ==> 0 != 0 is trivially provable (false premise)
/--
info: [WFObligation(safeDiv, ((~Bool.Implies : (arrow bool (arrow bool bool))) #false (~!= #0 #0)), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.And #false) ((~Int.Gt ((~safeDiv a) #0)) #0))]

-- Test for bvars: forall y :: let x := safeDiv(a, y) in safeDiv(b, x) > 0
/-- info: [WFObligation(safeDiv, (∀ (bvar:int) (~!= %0 #0)), ()), WFObligation(safeDiv, (∀ (bvar:int) ((λ (bvar:int) (~!= %0 #0)) (~safeDiv a %0))), ())]-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[∀ (int):{#true} ((λ (int): ((~Int.Gt ((~safeDiv b) %0)) #0)) ((~safeDiv a) %0))]

end Lambda

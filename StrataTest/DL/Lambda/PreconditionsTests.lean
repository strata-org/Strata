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

-- Test: let x := a in safeDiv(2, x)
-- Encoded as (λ (int): ((~safeDiv #2) %0)) a
-- The obligation should be: let x := a in (x != 0)
/-- info: [WFObligation(safeDiv, ((λ (bvar:int) (~!= %0 #0)) a), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[((λ (int): ((~safeDiv #2) %0)) a)]

-- Test: let x := safeDiv(a, b) in x
-- Encoded as (λ (int): %0) (safeDiv(a, b))
-- The obligation comes from the arg: b != 0
/-- info: [WFObligation(safeDiv, (~!= b #0), ())] -/
#guard_msgs in
#eval collectWFObligations testFactory
  esM[((λ (int): %0) ((~safeDiv a) b))]

/-! ### Polymorphic preconditions: type substitution at call site

A polymorphic function whose precondition mentions the type variable `%a`
must have that variable substituted with the call site's instantiated type.
Without this, downstream SMT encoding fails on unresolved type vars (issue #1201).
-/

-- A polymorphic function `polySel<a>(s : Sequence a) : a` whose precondition
-- contains an operator annotated with the type variable `%a`. This mirrors
-- `Sequence.select`'s `0 <= i && i < Sequence.length(s : Sequence %a)`
-- bound check, which uses an annotated `Sequence.length` op.
private def polySelFunc : LFunc TestParams :=
  { name := "polySel"
    typeArgs := ["a"]
    inputs := [("s", mty[Sequence %a])]
    output := mty[%a]
    -- precondition: 0 < lenOf(s), i.e.
    -- (((~Int.Lt : int → int → bool) #0) ((~lenOf : (Sequence %a) → int) s))
    -- The inner `lenOf` op carries a `%a` annotation that must be substituted
    -- at the call site. The outer `Int.Lt` makes the precondition `bool`-typed.
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) #0) ((~lenOf : (Sequence %a) → int) s))], ()⟩]
  }

private def polyFactory : Factory TestParams := .ofArray #[polySelFunc]

-- Call site annotates the operator with the instantiated arrow type
-- `Sequence int → int`. After value substitution alone, the inner op annotation
-- `(~lenOf : (Sequence %a) → int)` would still carry `%a`; the fix must also
-- apply the call-site type substitution `[%a → int]`.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool))) #0 ((~lenOf : (arrow (Sequence int) int)) myseq)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[((~polySel : (Sequence int) → int) myseq)]

-- Same expectation when the operator is unannotated: the argument-types
-- fallback unifies `Sequence int` against `Sequence %a` to derive `[%a → int]`.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence int) int)) (myseq : (Sequence int)))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[(~polySel (myseq : (Sequence int)))]

-- Subst.empty arm: neither `.op` annotation nor typed arguments. The
-- `callSiteTypeSubst` documentation (lines 63–66) promises this case returns
-- `Subst.empty` and defers handling to the SMT encoder. The unsubstituted
-- `%a` should remain in the inner `lenOf` op annotation.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool))) #0 ((~lenOf : (arrow (Sequence a) int)) myseq)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[(~polySel myseq)]

end Lambda

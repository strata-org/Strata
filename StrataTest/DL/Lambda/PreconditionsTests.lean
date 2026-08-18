/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import Strata.DL.Lambda.IntBoolFactory
meta import Strata.DL.Lambda.Preconditions

/-! # Preconditions Tests -/

meta section
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

-- Regression: a hypothesis captured OUTSIDE a binder must have
-- its de Bruijn indices shifted when the binder's body generates an obligation.
-- Without the shift the hypothesis silently rebinds to the inner variable. In
-- both tests the hypothesis `Int.Gt %0` (%0 = an enclosing binder's variable)
-- must lift to `Int.Gt %1` inside the binder, while the binder's own variable
-- fed to safeDiv is `%0`.

-- `.abs` branch: (v > 0) ==> (\x. safeDiv(v, x)).
/-- info: [WFObligation(safeDiv, (∀ (bvar:int) ((~Bool.Implies : (arrow bool (arrow bool bool))) (~Int.Gt %1 #0) (~!= %0 #0))), ())] -/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.Implies ((~Int.Gt %0) #0))
      (λ (int): ((~safeDiv %1) %0)))]

-- `.app (.abs …)` let-encoding branch: (v > 0) ==> (let x := a in safeDiv(2, x)).
/--
info: [WFObligation(safeDiv, ((λ (bvar:int) ((~Bool.Implies : (arrow bool (arrow bool bool))) (~Int.Gt %1 #0) (~!= %0 #0)))
 a), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.Implies ((~Int.Gt %0) #0))
      ((λ (int): ((~safeDiv #2) %0)) a))]

-- `.quant` branch: (v > 0) ==> (∀ x. safeDiv(v, x)).
/-- info: [WFObligation(safeDiv, (∀ (bvar:int) ((~Bool.Implies : (arrow bool (arrow bool bool))) (~Int.Gt %1 #0) (~!= %0 #0))), ())] -/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.Implies ((~Int.Gt %0) #0))
      (∀ (int): ((~safeDiv %1) %0)))]

-- Two nested `.quant` binders: the shift compounds, applied once per binder, so
-- the hypothesis `Int.Gt %0` (v) lifts to `Int.Gt %2` inside `∀ x. ∀ y`, while
-- `safeDiv(v, y)` reads v as `%2` and y as `%0`.
-- (v > 0) ==> (∀ x. ∀ y. safeDiv(v, y)).
/--
info: [WFObligation(safeDiv, (∀ (bvar:int) (∀ (bvar:int) ((~Bool.Implies : (arrow bool (arrow bool bool)))
   (~Int.Gt %2 #0)
   (~!= %0 #0)))), ())]
-/
#guard_msgs in
#eval collectWFObligations factoryWithImplies
  esM[((~Bool.Implies ((~Int.Gt %0) #0))
      (∀ (int): (∀ (int): ((~safeDiv %2) %0))))]

/-! ### Polymorphic preconditions: type substitution at call site -/

-- `polySel<a>(s : Sequence a) : a` with a precondition whose inner `lenOf` op
-- is annotated with `%a` (mirroring `Sequence.length`'s bound check).
private def polySelFunc : LFunc TestParams :=
  { name := "polySel"
    typeArgs := ["a"]
    inputs := [("s", mty[Sequence %a])]
    output := mty[%a]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) #0) ((~lenOf : (Sequence %a) → int) s))], ()⟩]
  }

private def polyFactory : Factory TestParams := .ofArray #[polySelFunc]

-- Annotated `.op`: `%a` resolves to `int` from the operator's arrow type.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool))) #0 ((~lenOf : (arrow (Sequence int) int)) myseq)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[((~polySel : (Sequence int) → int) myseq)]

-- Unannotated `.op`: `%a` resolves via the argument-type fallback.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence int) int)) (myseq : (Sequence int)))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[(~polySel (myseq : (Sequence int)))]

-- No type info: `%a` cannot be resolved and survives in the obligation.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool))) #0 ((~lenOf : (arrow (Sequence a) int)) myseq)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[(~polySel myseq)]

-- `polyPair<a>(x : a, y : a) : int` shares one type variable across both
-- inputs, so arguments of conflicting concrete types (`int`, `bool`) cannot
-- unify.
private def polyPairFunc : LFunc TestParams :=
  { name := "polyPair"
    typeArgs := ["a"]
    inputs := [("x", mty[%a]), ("y", mty[%a])]
    output := mty[int]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) #0) ((~lenOf : (Sequence %a) → int) x))], ()⟩]
  }

private def polyPairFactory : Factory TestParams := .ofArray #[polyPairFunc]

-- Unification failure: the arguments constrain `%a` to both `int` and
-- `bool`, so argument unification fails and `%a` resolves via the annotated
-- `.op` fallback.
/--
info: [WFObligation(polyPair, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence int) int)) (p : int))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyPairFactory
  esM[(((~polyPair : int → int → int) (p : int)) (q : bool))]

-- `polyTwo<a, b>(x : a, y : b) : int` with a precondition mentioning both type
-- variables. When only `x` carries a type, argument unification resolves `%a`
-- but leaves `%b` unconstrained; the annotated `.op` fills `%b`.
private def polyTwoFunc : LFunc TestParams :=
  { name := "polyTwo"
    typeArgs := ["a", "b"]
    inputs := [("x", mty[%a]), ("y", mty[%b])]
    output := mty[int]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) ((~lenOf : (Sequence %a) → int) x))
             ((~lenOf : (Sequence %b) → int) y))], ()⟩]
  }

private def polyTwoFactory : Factory TestParams := .ofArray #[polyTwoFunc]

-- Partial argument substitution: `x : int` resolves `%a`, `y` is untyped, and
-- the annotated `.op` supplies `%b`. Neither type variable survives.
/--
info: [WFObligation(polyTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence int) int)) (x : int))
 ((~lenOf : (arrow (Sequence int) int)) y)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyTwoFactory
  esM[(((~polyTwo : int → int → int) (x : int)) y)]

-- Nested polymorphic calls: the inner and outer call sites each resolve `%a`
-- independently (`Sequence int` for the inner, `int` for the outer).
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence (Sequence int)) int)) innerSeq)), ()), WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence int) int)) ((~polySel : (arrow (Sequence (Sequence int)) (Sequence int))) innerSeq))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[((~polySel : (Sequence int) → int)
       ((~polySel : (Sequence (Sequence int)) → (Sequence int)) innerSeq))]

-- `polyOut<a, b>(x : Sequence a) : b`: the argument binds `%a` to a type that
-- itself mentions `%b`, while `%b` is bound only by the `.op` annotation. The
-- merge must resolve `%b` inside `%a`'s binding or a bare `b` survives.
private def polyOutFunc : LFunc TestParams :=
  { name := "polyOut"
    typeArgs := ["a", "b"]
    inputs := [("x", mty[Sequence %a])]
    output := mty[%b]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) #0) ((~lenOf : (Sequence %a) → int) x))], ()⟩]
  }

private def polyOutFactory : Factory TestParams := .ofArray #[polyOutFunc]

-- The argument unifies `%a` to `Sequence %b`; the `.op` unifies `%b` to `int`.
-- Composing resolves `%a` to `Sequence int`, leaving no residual `%b`.
/--
info: [WFObligation(polyOut, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence (Sequence int)) int)) (myseq : (Sequence (Sequence int))))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyOutFactory
  esM[((~polyOut : (Sequence (Sequence int)) → int) (myseq : (Sequence (Sequence %b))))]

end Lambda
end

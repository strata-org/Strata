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

-- No type info: `%a`, the parameter at position 0, becomes the fresh `$__precond_0`.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence $__precond_0) int)) myseq)), ())]
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

-- Conflicting arguments: the annotated `.op` binds `%a` to `int`, and the
-- `bool` argument, which contradicts it, is ignored.
/--
info: [WFObligation(polyPair, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence int) int)) (p : int))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyPairFactory
  esM[(((~polyPair : int → int → int) (p : int)) (q : bool))]

-- `polyTwo<a, b>(x : a, y : b) : int` with a precondition mentioning both type
-- variables.
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

-- `x : int` and the annotated `.op` resolve `%a`, `y` is untyped, and the
-- `.op` supplies `%b`. Neither type variable survives.
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

-- `polyOut<a, b>(x : Sequence a) : b`: `%b` appears only in the output type.
private def polyOutFunc : LFunc TestParams :=
  { name := "polyOut"
    typeArgs := ["a", "b"]
    inputs := [("x", mty[Sequence %a])]
    output := mty[%b]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) #0) ((~lenOf : (Sequence %a) → int) x))], ()⟩]
  }

private def polyOutFactory : Factory TestParams := .ofArray #[polyOutFunc]

-- The `.op` binds `%a` to `Sequence int` and `%b` to `int`; the argument's
-- `b` is the caller's type variable and stays. The annotation and the argument
-- disagree on `%a` (`Sequence int` against `Sequence b`) on purpose: the
-- annotation decides the obligation.
/--
info: [WFObligation(polyOut, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence (Sequence int)) int)) (myseq : (Sequence (Sequence b))))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyOutFactory
  esM[((~polyOut : (Sequence (Sequence int)) → int) (myseq : (Sequence (Sequence %b))))]

-- Inside a caller with its own type variable `a`, `polyTwo(true, x : a)`
-- instantiates the callee's `a` at `bool` and its `b` at the caller's `a`; the
-- argument keeps type `a`.
/--
info: [WFObligation(polyTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence bool) int)) #true)
 ((~lenOf : (arrow (Sequence a) int)) (x : a))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyTwoFactory
  esM[((~polyTwo #true) (x : %a))]

-- The same call with the operator annotated at its instance `bool → a → int`.
/--
info: [WFObligation(polyTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence bool) int)) #true)
 ((~lenOf : (arrow (Sequence a) int)) (x : a))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyTwoFactory
  esM[(((~polyTwo : bool → %a → int) #true) (x : %a))]

-- Inside a caller with its own type variable `a`, `polySel(s)` with
-- `s : Sequence (Sequence a)` instantiates the callee's `a` at `Sequence a`.
/--
info: [WFObligation(polySel, ((~Int.Lt : (arrow int (arrow int bool)))
 #0
 ((~lenOf : (arrow (Sequence (Sequence a)) int)) (s : (Sequence (Sequence a))))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFactory
  esM[((~polySel : (Sequence (Sequence %a)) → (Sequence %a))
       (s : (Sequence (Sequence %a))))]

-- `polyTwo(x : b, y)` with `y` untyped, inside a caller with its own type
-- variable `b`: the callee's `a` is the caller's `b`, and the callee's `b`,
-- which the call does not determine, becomes the fresh `$__precond_1`.
/--
info: [WFObligation(polyTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence b) int)) (x : b))
 ((~lenOf : (arrow (Sequence $__precond_1) int)) y)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyTwoFactory
  esM[((~polyTwo (x : %b)) y)]

-- `polyPairTwo<a, b>(x : a, y : a, z : b) : int`, built as an AST.
private def polyPairTwoFunc : LFunc TestParams :=
  let tvA : LMonoTy := .ftvar "a"
  let tvB : LMonoTy := .ftvar "b"
  let lenOf (ty : LMonoTy) : LExpr TestParams.mono :=
    .op () "lenOf" (some (.arrow (.tcons "Sequence" [ty]) .int))
  { name := "polyPairTwo"
    typeArgs := ["a", "b"]
    inputs := [("x", tvA), ("y", tvA), ("z", tvB)]
    output := .int
    preconditions :=
      [⟨.app () (.app () (.op () "Int.Lt" (some (.arrow .int (.arrow .int .bool))))
          (.app () (lenOf tvA) (.fvar () "x" none))) (.app () (lenOf tvB) (.fvar () "z" none)),
        ()⟩] }

-- `polyPairTwo(p : int, q : bool, r)` unannotated: `q` contradicts the `a` that `p` fixes, so
-- the matching fails and both `a` and `b` become fresh. The conflict is deliberate.
/--
info: [WFObligation(polyPairTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence $__precond_0) int)) (p : int))
 ((~lenOf : (arrow (Sequence $__precond_1) int)) r)), ())]
-/
#guard_msgs in
#eval collectWFObligations (.ofArray #[polyPairTwoFunc])
  (.app () (.app () (.app () (.op () "polyPairTwo" none) (.fvar () "p" (some .int)))
    (.fvar () "q" (some .bool))) (.fvar () "r" none))

-- `polyTwo(x : b, y : a)` annotated `b → a → int`, inside a caller with type variables `b` and
-- `a`: the callee's `a` is the caller's `b` and the callee's `b` is the caller's `a`.
/--
info: [WFObligation(polyTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence b) int)) (x : b))
 ((~lenOf : (arrow (Sequence a) int)) (y : a))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyTwoFactory
  esM[(((~polyTwo : %b → %a → int) (x : %b)) (y : %a))]

-- The same call inside a caller whose type variables are `c` and `d`: the same obligation with
-- `b` renamed to `c` and `a` to `d`.
/--
info: [WFObligation(polyTwo, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence c) int)) (x : c))
 ((~lenOf : (arrow (Sequence d) int)) (y : d))), ())]
-/
#guard_msgs in
#eval collectWFObligations polyTwoFactory
  esM[(((~polyTwo : %c → %d → int) (x : %c)) (y : %d))]

-- `polyRes<a>(x : int) : a` with a precondition mentioning `%a` only through
-- an annotation.
private def polyResFunc : LFunc TestParams :=
  { name := "polyRes"
    typeArgs := ["a"]
    inputs := [("x", mty[int])]
    output := mty[%a]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) x) ((~lenOf : (Sequence %a) → int) ~nil))], ()⟩]
  }

private def polyResFactory : Factory TestParams := .ofArray #[polyResFunc]

-- `polyRes(0)` annotated with its declared type `int → a`, inside a caller with its own type
-- variable `a`: the callee's `a` is the caller's `a`.
/--
info: [WFObligation(polyRes, ((~Int.Lt : (arrow int (arrow int bool))) #0
((~lenOf : (arrow (Sequence a) int)) ~nil)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyResFactory esM[((~polyRes : int → %a) #0)]

-- The same call inside a caller whose type variable is `c`: the same
-- obligation with `a` renamed to `c`.
/--
info: [WFObligation(polyRes, ((~Int.Lt : (arrow int (arrow int bool))) #0
((~lenOf : (arrow (Sequence c) int)) ~nil)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyResFactory esM[((~polyRes : int → %c) #0)]

-- `polyFree<a, b>(x : Sequence a) : int`, whose `%b` occurs only in its
-- precondition, so no call determines it.
private def polyFreeFunc : LFunc TestParams :=
  { name := "polyFree"
    typeArgs := ["a", "b"]
    inputs := [("x", mty[Sequence %a])]
    output := mty[int]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) ((~lenOf : (Sequence %a) → int) x))
             ((~lenOf : (Sequence %b) → int) ~nil))], ()⟩]
  }

private def polyFreeFactory : Factory TestParams := .ofArray #[polyFreeFunc]

-- `polyFree(x)` inside a caller with its own type variable `b`: the callee's
-- `a` is the caller's `b`, and the callee's `b` becomes `$__precond_1`, distinct
-- from the caller's `b`.
/--
info: [WFObligation(polyFree, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence b) int)) (x : (Sequence b)))
 ((~lenOf : (arrow (Sequence $__precond_1) int)) ~nil)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFreeFactory
  esM[((~polyFree : (Sequence %b) → int) (x : (Sequence %b)))]

-- The same call inside a caller whose type variable is `c`: the same
-- obligation with `b` renamed to `c`.
/--
info: [WFObligation(polyFree, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence c) int)) (x : (Sequence c)))
 ((~lenOf : (arrow (Sequence $__precond_1) int)) ~nil)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFreeFactory
  esM[((~polyFree : (Sequence %c) → int) (x : (Sequence %c)))]

-- `polyFree` with its second type parameter named `d`.
private def polyFreeDFactory : Factory TestParams := .ofArray #[{ polyFreeFunc with
    typeArgs := ["a", "d"]
    preconditions :=
      [⟨esM[(((~Int.Lt : int → int → bool) ((~lenOf : (Sequence %a) → int) x))
             ((~lenOf : (Sequence %d) → int) ~nil))], ()⟩] }]

-- `polyFree(x : Sequence b)` with the callee's `b` renamed to `d`: the same obligation.
/--
info: [WFObligation(polyFree, ((~Int.Lt : (arrow int (arrow int bool)))
 ((~lenOf : (arrow (Sequence b) int)) (x : (Sequence b)))
 ((~lenOf : (arrow (Sequence $__precond_1) int)) ~nil)), ())]
-/
#guard_msgs in
#eval collectWFObligations polyFreeDFactory
  esM[((~polyFree : (Sequence %b) → int) (x : (Sequence %b)))]

end Lambda
end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module



meta import Strata.DL.Lambda
meta import Strata.DL.Lambda.IntBoolFactory

---------------------------------------------------------------------

meta section
namespace Lambda

open Std (ToFormat Format format)
open LExpr LTy

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

section Test
open LState LExpr LExpr.SyntaxMono LTy.Syntax

/--
info: error: A function of name Int.Add already exists! Redefinitions are not allowed.
Existing Function: func Int.Add :  ((x : int) (y : int)) → int;
New Function:func Int.Add :  () → int;
-/
#guard_msgs in
#eval do
  let F ← (IntBoolFactory : Factory TestParams).tryPush {
      name := "Int.Add",
      inputs := [],
      output := .tcons "int" [] }
  let ans ← typeCheckAndPartialEval TypeFactory.default F esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) #100)]
  return format ans

/--
info: Annotated expression:
((~Int.Le : (arrow int (arrow int bool)))
 ((~Int.Div : (arrow int (arrow int int))) #300 ((~Int.Add : (arrow int (arrow int int))) #2 #1))
 #100)

---
info: #true
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval TypeFactory.default  (IntBoolFactory : @Factory TestParams)
                esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) #100)]

/--
info: Annotated expression:
((~Int.Div : (arrow int (arrow int int))) ((~Int.Add : (arrow int (arrow int int))) #2 #1))

---
info: ((~Int.Div : (arrow int (arrow int int))) #3)
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval TypeFactory.default  (IntBoolFactory : @Factory TestParams)
               esM[((~Int.Div ((~Int.Add #2) #1)))]
/--
info: Annotated expression:
((λ (bvar:(arrow int int)) (%0 #2)) ((~Int.Div : (arrow int (arrow int int))) #300))

---
info: #150
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval TypeFactory.default  (IntBoolFactory : @Factory TestParams)
                esM[((λ (%0 #2)) (~Int.Div #300))]

/-! `Bool.And`, `Bool.Or` and `Bool.Implies` fold when only their first operand is known. -/

private def evalBool (e : LExpr TestParams.mono) : Except Strata.Message (LExpr TestParams.mono) := do
  let σ ← (LState.init : LState TestParams).addFactory (IntBoolFactory : @Factory TestParams)
  return (LExpr.evalWithLState σ.config.fuel σ e).fst

/-- info: #false -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.And #false) (y : bool))]

/-- info: (y : bool) -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.And #true) (y : bool))]

/-- info: #true -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.Or #true) (y : bool))]

/-- info: (y : bool) -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.Or #false) (y : bool))]

/-- info: #true -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.Implies #false) (y : bool))]

/-- info: (y : bool) -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.Implies #true) (y : bool))]

/-! Only the first operand decides: a known second operand alone does not fold. -/

/-- info: (~Bool.And (y : bool) #false) -/
#guard_msgs in
#eval format $ evalBool esM[((~Bool.And (y : bool)) #false)]

/-! A deep chain alternating a decided and a symbolic first operand,
`true && (z && (true && (z && …)))`, evaluates each node once, so depth 800
reduces to the chain of its symbolic conjuncts. -/

private def bAnd (x y : LExpr TestParams.mono) : LExpr TestParams.mono :=
  LExpr.mkApp () esM[~Bool.And] [x, y]

private def andChain : Nat → LExpr TestParams.mono
  | 0 => esM[(y : bool)]
  | n + 1 => bAnd esM[#true] (bAnd esM[(z : bool)] (andChain n))

private def symbolicChain : Nat → LExpr TestParams.mono
  | 0 => esM[(y : bool)]
  | n + 1 => bAnd esM[(z : bool)] (symbolicChain n)

/-- info: true -/
#guard_msgs in
#eval match (LState.init : LState TestParams).addFactory (IntBoolFactory : @Factory TestParams) with
  | .ok σ => (LExpr.evalWithLState 2000 σ (andChain 800)).fst.eraseMetadata ==
      (symbolicChain 800).eraseMetadata
  | .error _ => false

end Test

end Lambda
end
---------------------------------------------------------------------

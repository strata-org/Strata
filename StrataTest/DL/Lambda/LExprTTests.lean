/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprT

namespace Lambda
---------------------------------------------------------------------
open Std (ToFormat Format format)
open LTy

section Tests

open LTy.Syntax LExpr.Syntax LExpr LMonoTy

/-- info: ok: (if (#true : bool) then ((x : int) == (#5 : int)) else ((x : int) == (#6 : int))) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate { TEnv.default with context := { types := [[("x", t[∀x. %x])]] } }
                               es[if #true then (x == #5) else (x == #6)]
         return (format $ ans.fst)

/-- info: ok: (λ %0) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate TEnv.default es[λ(%0)]
         return format ans.fst

/-- info: ok: (∀ (%0 == (#5 : int))) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate TEnv.default es[∀ (%0 == #5)]
         return format ans.fst

/-- info: ok: (λ ((succ : (arrow int int)) %0)) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate { TEnv.default with context := { types := [[("succ", t[int → int])]] } }
                               es[λ(succ %0)]
         return (format $ ans.fst)

/-- info: ok: (∀(int) ((%0 : int) == (#5 : int)) : bool)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default es[∀ (%0 == #5)]
         return (format $ ans.fst)

private def testIntFns : (@Factory String) :=
  #[{ name := "unit",
      inputs := [],
      output := mty[unit]},
    { name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int]},
    { name := "Int.Div",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int]},
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int]}]

/--
info: ok: (((~Int.Add : (arrow int (arrow int int))) (x : int)) ((~Int.Neg : (arrow int int)) (#30 : int)))
-/
#guard_msgs in
#eval do let ans ← LExpr.annotate { (@TEnv.default String)
                                               with functions := testIntFns,
                                                      context := { types := [[("x", t[int])]] }}
                                   es[((~Int.Add x) (~Int.Neg #30))]
         return (format $ ans.fst)

/--
info: ok: ((λ ((%0 : (arrow bool $__ty3)) ((fn : (arrow bool bool)) (#true : bool)) : bool)) : $__ty3)) : (arrow (arrow bool $__ty3) $__ty3))
-/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String)
                                                with functions := testIntFns,
                                                        context := { types := [[("fn", t[∀a. %a → %a])]] }}
                             es[(λ (%0 (fn #true)))]
         return format ans.fst

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.inferType { (@TEnv.default String)
                                                with functions := testIntFns,
                                                       context := { types := [[("fn", t[∀a. %a → %a])]] }}
                             es[(fn #3)]
         return (format $ ans.fst)


end Tests

---------------------------------------------------------------------

end Lambda

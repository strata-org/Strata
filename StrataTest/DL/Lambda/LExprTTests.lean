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

open LTy.Syntax LExpr.SyntaxMono LExpr LMonoTy

/-- info: error: Cannot infer the type of this bvar: %2 -/
#guard_msgs in
-- Ill-formed terms, like those that contain dangling bound variables, do not
-- type check.
#eval do let ans ← LExprT.fromLExpr TEnv.default
                             esM[λλ %2]
         return (format $ ans)

/-- info: ok: (((λ (%0 : $__ty3)) : (arrow $__ty3 $__ty3)) (y : $__ty3)) : $__ty3) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with context := { types := [[("y", t[∀x. %x])]] }}
                            esM[((λ %0) y)]
         return (format $ ans.fst)

/-- info: error: Cannot unify differently named type constructors bool and int! -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with context := { types := [[("x", t[bool])]] }}
                         esM[if #true then (x == #5) else (x == #6)]
         return format ans

/-- info: ok: (if (#true : bool) then ((x : int) == (#5 : int)) else ((x : int) == (#6 : int))) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate { TEnv.default with context := { types := [[("x", t[∀x. %x])]] } }
                               esM[if #true then (x == #5) else (x == #6)]
         return (format $ ans.fst)

/-- info: ok: (λ %0) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate TEnv.default esM[λ(%0)]
         return format ans.fst

/-- info: ok: (∀ (%0 == (#5 : int))) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate TEnv.default esM[∀ (%0 == #5)]
         return format ans.fst

/-- info: ok: (λ ((succ : (arrow int int)) %0)) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate { TEnv.default with context := { types := [[("succ", t[int → int])]] } }
                               esM[λ(succ %0)]
         return (format $ ans.fst)

/-- info: ok: (∀(int) ((%0 : int) == (#5 : int)) : bool)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[∀ (%0 == #5)]
         return (format $ ans.fst)

/-- info: ok: ((λ (%0 : $__ty0)) : (arrow $__ty0 $__ty0)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[λ(%0)]
         return (format $ ans.fst)

/-- info: ok: (#5 : int) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[#5]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[((λ %0) #5)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow $__ty0 int) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[λ #5]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow (arrow int $__ty2) $__ty2) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[λ(%0 #5)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow $__ty0 (arrow (arrow $__ty0 $__ty4) $__ty4)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[λλ(%0 %1)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow (arrow int $__ty4) $__ty4) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default esM[((λλ (%0 %1)) #5)]
         return (format ans.fst.toLMonoTy)

/-- info: error: Ftvar $__ty0 is in the free variables of (arrow $__ty0 $__ty3)! -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default
                            esM[λ(%0 %0)]
         return (format $ ans.fst)

/-- info: ok: (arrow (arrow $__ty6 $__ty7) (arrow (arrow $__ty2 $__ty6) (arrow $__ty2 $__ty7))) -/
#guard_msgs in
-- Term: fun f -> (fun g -> (fun x -> (f (g x))))
-- Expected type: ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
#eval do let ans ← LExprT.fromLExpr TEnv.default
                            esM[λλλ(%2 (%1 %0))]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow (arrow $__ty6 $__ty6) (arrow $__ty6 $__ty6)) -/
#guard_msgs in
-- Term: fun f -> (fun x -> (f (f x)))
-- Expected type: ('a -> 'a) -> 'a -> 'a
#eval do let ans ← LExprT.fromLExpr TEnv.default
                            esM[λλ (%1 (%1 %0))]
         return (format $ ans.fst.toLMonoTy)

/--
info: ok: (arrow (arrow $__ty2 (arrow $__ty8 $__ty9)) (arrow (arrow $__ty2 $__ty8) (arrow $__ty2 $__ty9)))
-/
#guard_msgs in
-- Function: fun f -> (fun g -> (fun x -> ((f x) (g x))))
-- Expected type: ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
#eval do let ans ← LExprT.fromLExpr TEnv.default
                            esM[λλλ ((%2 %0) (%1 %0))]
         return (format $ ans.fst.toLMonoTy)

/-- info: error: Ftvar $__ty1 is in the free variables of (arrow $__ty1 $__ty5)! -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr TEnv.default
                            esM[λλ(%1 (%0 %0))]
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
      output := mty[int]},
    { name := "SynonymTest",
      inputs := [("x", mty[myInt]), ("y", mty[int])],
      output := mty[int]}
  ]

/--
info: error: Type unit is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with functions := testIntFns }
                             esM[~unit]
         return (format $ ans.fst)

/-- info: ok: (~unit : unit) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with functions := testIntFns,
                                                        knownTypes := [t[unit].toKnownType!] }
                             esM[~unit]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr
                    { (@TEnv.default String)
                    with functions := testIntFns,
                                          context :=
                                          { aliases := [{typeArgs := [],
                                                         name := "myInt",
                                                         type := mty[int]}]} }
                             esM[((~SynonymTest #20) #30)]
         return (format $ ans.fst.toLMonoTy)

/-- info: error: Cannot unify differently named type constructors int and bool! -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with functions := testIntFns }
                             esM[(~Int.Neg #true)]
         return (format $ ans)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with functions := testIntFns }
                             esM[(~Int.Neg #100)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { TEnv.default with functions := testIntFns }
                             esM[((λ %0) ((~Int.Add #20) #30))]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             esM[(λ (~Int.Add %0))]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             esM[λλ ((~Int.Add %0) %1)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             esM[(λλ ((~Int.Add %1) %0))]
         return (format $ ans.fst.toLMonoTy);

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             esM[((~Int.Add x) (~Int.Neg #30))]
         return (format $ ans.fst.toLMonoTy)

/--
info: ok: (((~Int.Add : (arrow int (arrow int int))) (x : int)) ((~Int.Neg : (arrow int int)) (#30 : int)))
-/
#guard_msgs in
#eval do let ans ← LExpr.annotate { (@TEnv.default String)
                                               with functions := testIntFns,
                                                      context := { types := [[("x", t[int])]] }}
                                   esM[((~Int.Add x) (~Int.Neg #30))]
         return (format $ ans.fst)

/--
info: ok: ((λ ((%0 : (arrow bool $__ty4)) ((fn : (arrow bool bool)) (#true : bool)) : bool)) : $__ty4)) : (arrow (arrow bool $__ty4) $__ty4))
-/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String)
                                                with functions := testIntFns,
                                                        context := { types := [[("fn", t[∀a. %a → %a])]] }}
                             esM[(λ (%0 (fn #true)))]
         return format ans.fst

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExprT.fromLExpr { (@TEnv.default String)
                                                with functions := testIntFns,
                                                       context := { types := [[("fn", t[∀a. %a → %a])]] }}
                             esM[(fn #3)]
         return (format $ ans.fst.toLMonoTy)


end Tests

---------------------------------------------------------------------

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeImpl

namespace Lambda
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open LTy.Syntax LExpr.Syntax LExpr LMonoTy

-- def HeapType : LTy := t[∀a. (Pair (Ref) (Field %a)) → %a]
-- def snapshot : LExpr := (.const "snapshot" none)
--
-- #eval do let ans ← inferType { TEnv.init with
--                                context := [[("r", t[Ref]),
--                                             ("heap", t[∀a. (Ref) → ((Field %a) → %a)]),
--                                             ("snapshot", t[∀a. (Field %a)])]] }
--                             es[((heap r) snapshot)]
--          return (format $ ans)

/-- info: error: Cannot infer the type of this bvar: %2 -/
#guard_msgs in
-- Ill-formed terms, like those that contain dangling bound variables, do not
-- type check.
#eval do let ans ← inferType TEnv.default
                             es[λλ %2]
         return (format $ ans)

/-- info: ok: $__ty2 -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with context := { types := [[("y", t[∀x. %x])]] }}
                            es[((λ %0) y)]
         return (format $ ans.fst)

/-- info: ok: bool -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with context := { types := [[("x", t[∀x. %x])]] }}
                         es[if #true then (x == #5) else (x == #6)]
         return (format $ ans.fst)

/-- info: error: Cannot unify differently named type constructors bool and int! -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with context := { types := [[("x", t[bool])]] }}
                         es[if #true then (x == #5) else (x == #6)]
         return format ans

/-- info: ok: (arrow int int) -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with context := { types := [[("succ", t[int → int])]] }}
                             es[λ(succ %0)]
         return (format $ ans.fst)

/-- info: ok: bool -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with context := { types := [[("x", t[int])]] }}
                        es[if #true then (x == #5) else (x == #6)]
         return (format $ ans.fst)

/-- info: ok: (arrow $__ty0 $__ty0) -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[λ(%0)]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[#5]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[((λ %0) #5)]
         return (format $ ans.fst)

/-- info: ok: (arrow $__ty0 int) -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[λ #5]
         return (format $ ans.fst)

/-- info: ok: (arrow (arrow int $__ty1) $__ty1) -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[λ(%0 #5)]
         return (format $ ans.fst)

/-- info: ok: (arrow $__ty0 (arrow (arrow $__ty0 $__ty2) $__ty2)) -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[λλ(%0 %1)]
         return (format $ ans.fst)

/-- info: ok: (arrow (arrow int $__ty2) $__ty2) -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default es[((λλ (%0 %1)) #5)]
         return (format ans.fst)

/-- info: error: Ftvar $__ty0 is in the free variables of (arrow $__ty0 $__ty1)! -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default
                            es[λ(%0 %0)]
         return (format $ ans.fst)

/-- info: ok: (arrow (arrow $__ty3 $__ty4) (arrow (arrow $__ty2 $__ty3) (arrow $__ty2 $__ty4))) -/
#guard_msgs in
-- Term: fun f -> (fun g -> (fun x -> (f (g x))))
-- Expected type: ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
#eval do let ans ← inferType TEnv.default
                            es[λλλ(%2 (%1 %0))]
         return (format $ ans.fst)

/-- info: ok: (arrow (arrow $__ty3 $__ty3) (arrow $__ty3 $__ty3)) -/
#guard_msgs in
-- Term: fun f -> (fun x -> (f (f x)))
-- Expected type: ('a -> 'a) -> 'a -> 'a
#eval do let ans ← inferType TEnv.default
                            es[λλ (%1 (%1 %0))]
         return (format $ ans.fst)

/--
info: ok: (arrow (arrow $__ty2 (arrow $__ty4 $__ty5)) (arrow (arrow $__ty2 $__ty4) (arrow $__ty2 $__ty5)))
-/
#guard_msgs in
-- Function: fun f -> (fun g -> (fun x -> ((f x) (g x))))
-- Expected type: ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
#eval do let ans ← inferType TEnv.default
                            es[λλλ ((%2 %0) (%1 %0))]
         return (format $ ans.fst)

/-- info: error: Ftvar $__ty1 is in the free variables of (arrow $__ty1 $__ty2)! -/
#guard_msgs in
#eval do let ans ← inferType TEnv.default
                            es[λλ(%1 (%0 %0))]
         return (format $ ans.fst)

def testIntFns : (@Factory String) :=
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
      output := mty[int]}]

/--
info: error: Type unit is not an instance of a previously registered type!
Known Types: [∀[a, b]. (arrow a b), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with functions := testIntFns }
                             es[~unit]
         return (format $ ans.fst)

/-- info: ok: unit -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with functions := testIntFns,
                                                 knownTypes := [t[unit]] }
                             es[~unit]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← inferType
                    { (@TEnv.default String)
                    with functions := testIntFns,
                                          context :=
                                          { aliases := [{args := [],
                                                         lhs := mty[myInt],
                                                         rhs := mty[int]}]} }
                             es[((~SynonymTest #20) #30)]
         return (format $ ans.fst)

/-- info: error: Cannot unify differently named type constructors int and bool! -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with functions := testIntFns }
                             es[(~Int.Neg #true)]
         return (format $ ans)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with functions := testIntFns }
                             es[(~Int.Neg #100)]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← inferType { TEnv.default with functions := testIntFns }
                             es[((λ %0) ((~Int.Add #20) #30))]
         return (format $ ans.fst)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← inferType { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             es[(λ (~Int.Add %0))]
         return (format $ ans.fst)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← inferType { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             es[λλ ((~Int.Add %0) %1)]
         return (format $ ans.fst)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← inferType { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             es[(λλ ((~Int.Add %1) %0))]
         return (format $ ans.fst);

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← inferType { (@TEnv.default String) with functions := testIntFns, context := { types := [[("x", t[int])]] }}
                             es[((~Int.Add x) (~Int.Neg #30))]
         return (format $ ans.fst)

end Tests

---------------------------------------------------------------------
end Lambda

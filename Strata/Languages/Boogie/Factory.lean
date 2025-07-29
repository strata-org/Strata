/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/



import Strata.Languages.Boogie.Identifiers
import Strata.DL.Lambda.IntBoolFactory
---------------------------------------------------------------------

namespace Boogie
open Lambda LTy.Syntax

@[match_pattern]
def mapTy (keyTy : LMonoTy) (valTy : LMonoTy) : LMonoTy :=
  .tcons "Map" [keyTy, valTy]

def KnownTypes : List LTy :=
  [t[bool],
   t[int],
   t[string],
   t[∀a b. %a → %b],
   t[∀a b. Map %a %b]]

-- TODO: generalize denote function to a functor that can map between Identifiers
-- and resuse IntBoolFactory
def Factory : @Factory BoogieIdent :=
  open LTy.Syntax in
  #[
    /- Integer Arithmetic Operations -/
    { name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      denote := some (binOpDenote Int Int LExpr.denoteInt Int.add mty[int]) },
    { name := "Int.Sub",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      denote := some (binOpDenote Int Int LExpr.denoteInt Int.sub mty[int]) },
    { name := "Int.Mul",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      denote := some (binOpDenote Int Int LExpr.denoteInt Int.mul mty[int]) },
    { name := "Int.Div",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      -- We hand-code a denotation for `Int.Div` to leave the expression
      -- unchanged if we have `0` for the denominator.
      denote := some (fun e args => match args with
                       | [e1, e2] =>
                         let e1i := LExpr.denoteInt e1
                         let e2i := LExpr.denoteInt e2
                         match e1i, e2i with
                         | some x, some y =>
                           if y == 0 then e else (.const (toString (x / y)) mty[int])
                         | _, _ => e
                       | _ => e) },
    { name := "Int.Mod",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      -- We hand-code a denotation for `Int.Mod` to leave the expression
      -- unchanged if we have `0` for the denominator.
      denote := some (fun e args => match args with
                       | [e1, e2] =>
                         let e1i := LExpr.denoteInt e1
                         let e2i := LExpr.denoteInt e2
                         match e1i, e2i with
                         | some x, some y =>
                           if y == 0 then e else (.const (toString (x % y)) mty[int])
                         | _, _ => e
                       | _ => e) },
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int],
      denote := some (unOpDenote Int Int LExpr.denoteInt Int.neg mty[int]) },

    /- Integer Comparison Operations -/
    { name := "Int.Lt",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[bool],
      denote := some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x < y) mty[bool]) },
    { name := "Int.Le",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[bool],
      denote := some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x <= y) mty[bool]) },
    { name := "Int.Gt",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[bool],
      denote := some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x > y) mty[bool]) },
    { name := "Int.Ge",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[bool],
      denote := some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x >= y) mty[bool]) },

    /- Boolean Operations -/
    { name := "Bool.And",
      inputs := [("x", mty[bool]), ("y", mty[bool])],
      output := mty[bool],
      denote := some (binOpDenote Bool Bool LExpr.denoteBool Bool.and mty[bool]) },
    { name := "Bool.Or",
      inputs := [("x", mty[bool]), ("y", mty[bool])],
      output := mty[bool],
      denote := some (binOpDenote Bool Bool LExpr.denoteBool Bool.or mty[bool]) },
    { name := "Bool.Implies",
      inputs := [("x", mty[bool]), ("y", mty[bool])],
      output := mty[bool],
      denote := some (binOpDenote Bool Bool LExpr.denoteBool (fun x y => ((not x) || y)) mty[bool]) },
    { name := "Bool.Equiv",
      inputs := [("x", mty[bool]), ("y", mty[bool])],
      output := mty[bool],
      denote := some (binOpDenote Bool Bool LExpr.denoteBool (fun x y => (x == y)) mty[bool]) },
    { name := "Bool.Not",
      inputs := [("x", mty[bool])],
      output := mty[bool],
      denote := some (unOpDenote Bool Bool LExpr.denoteBool Bool.not mty[bool]) }
   ].append #[

   /- String Operations -/
    { name := "Str.Length",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[int],
      denote := some (unOpDenote String Int LExpr.denoteString
                        (fun s => (Int.ofNat (String.length s)))
                        mty[int])},
    { name := "Str.Concat",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[string],
      denote := some (binOpDenote String String LExpr.denoteString
                       String.append mty[string])},

   /- A polymorphic `old` function with type `∀a. a → a`. -/
    { name := "old",
      typeArgs := ["a"],
      inputs := [((.locl, "x"), mty[%a])]
      output := mty[%a]},

   /- A `Map` selection function with type `∀k, v. Map k v → k → v`. -/
   { name := "select",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])],
     output := mty[%v] },
   /- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
   { name := "update",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k]), ("x", mty[%v])],
     output := mapTy mty[%k] mty[%v],
     axioms := [
       -- ∀ m k v. select(update(m, k, v), k) = v
       (.quant .all (.some (mapTy mty[%k] mty[%v]))
         (.quant .all (.some mty[%k])
           (.quant .all (.some mty[%v])
             (.eq
               (LExpr.mkApp (.op "select"  (.some (LMonoTy.mkArrow (mapTy mty[%k] mty[%v]) [mty[%k], mty[%v]])))
                 [LExpr.mkApp (.op "update" (.some (LMonoTy.mkArrow (mapTy mty[%k] mty[%v]) [mty[%k], mty[%v], mapTy mty[%k] mty[%v]]))) [(.bvar 2), (.bvar 1), (.bvar 0)], (.bvar 1)])
               (.bvar 0)
             )
           )
         )
       ),

       -- ∀ m kk okk v. okk ≠ kk → select(update(m, kk, v), okk) = select(m, okk)
       (.quant .all (.some (mapTy mty[%k] mty[%v]))
         (.quant .all (.some mty[%k])
           (.quant .all (.some mty[%k])
             (.quant .all (.some mty[%v])
               (.ite
                 (LExpr.mkApp (.op "Bool.Not" (.some (LMonoTy.mkArrow mty[%k] [mty[%k], mty[bool]]))) [(.eq (.bvar 1) (.bvar 2))])
                 (.eq
                   (LExpr.mkApp (.op "select" (.some (LMonoTy.mkArrow (mapTy mty[%k] mty[%v]) [mty[%k], mty[%v]]))) [(.bvar 3), (.bvar 1)])
                   (LExpr.mkApp (.op "select" (.some (LMonoTy.mkArrow (mapTy mty[%k] mty[%v]) [mty[%k], mty[%v]])))
                     [LExpr.mkApp (.op "update" (.some (LMonoTy.mkArrow (mapTy mty[%k] mty[%v]) [mty[%k], mty[%v], mapTy mty[%k] mty[%v]]))) [(.bvar 3), (.bvar 2), (.bvar 0)], (.bvar 1)])
                 )
                 (.const "true" (.some mty[bool]))
               )
             )
           )
         )
       )
     ] }]

---------------------------------------------------------------------

end Boogie

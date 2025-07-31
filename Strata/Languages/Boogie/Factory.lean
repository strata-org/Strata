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
   t[real],
   t[bv1],
   t[bv8],
   t[bv16],
   t[bv32],
   t[bv64],
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

    /- Bv1 Arithmetic Operations -/
    { name := "Bv1.Add",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bv1],
      denote := none },
    { name := "Bv1.Sub",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bv1],
      denote := none },
    { name := "Bv1.Mul",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bv1],
      denote := none },
    { name := "Bv1.Neg",
      inputs := [("x", mty[bv1])],
      output := mty[bv1],
      denote := none },

    /- Bv1 Comparison Operations -/
    { name := "Bv1.Lt",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bool],
      denote := none },
    { name := "Bv1.Le",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bool],
      denote := none },
    { name := "Bv1.Gt",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bool],
      denote := none },
    { name := "Bv1.Ge",
      inputs := [("x", mty[bv1]), ("y", mty[bv1])],
      output := mty[bool],
      denote := none },

    /- Bv8 Arithmetic Operations -/
    { name := "Bv8.Add",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bv8],
      denote := none },
    { name := "Bv8.Sub",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bv8],
      denote := none },
    { name := "Bv8.Mul",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bv8],
      denote := none },
    { name := "Bv8.Neg",
      inputs := [("x", mty[bv8])],
      output := mty[bv8],
      denote := none },

    /- Bv8 Comparison Operations -/
    { name := "Bv8.Lt",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bool],
      denote := none },
    { name := "Bv8.Le",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bool],
      denote := none },
    { name := "Bv8.Gt",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bool],
      denote := none },
    { name := "Bv8.Ge",
      inputs := [("x", mty[bv8]), ("y", mty[bv8])],
      output := mty[bool],
      denote := none },

    /- Bv16 Arithmetic Operations -/
    { name := "Bv16.Add",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bv16],
      denote := none },
    { name := "Bv16.Sub",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bv16],
      denote := none },
    { name := "Bv16.Mul",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bv16],
      denote := none },
    { name := "Bv16.Neg",
      inputs := [("x", mty[bv16])],
      output := mty[bv16],
      denote := none },

    /- Bv16 Comparison Operations -/
    { name := "Bv16.Lt",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bool],
      denote := none },
    { name := "Bv16.Le",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bool],
      denote := none },
    { name := "Bv16.Gt",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bool],
      denote := none },
    { name := "Bv16.Ge",
      inputs := [("x", mty[bv16]), ("y", mty[bv16])],
      output := mty[bool],
      denote := none },

    /- Bv32 Arithmetic Operations -/
    { name := "Bv32.Add",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bv32],
      denote := none },
    { name := "Bv32.Sub",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bv32],
      denote := none },
    { name := "Bv32.Mul",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bv32],
      denote := none },
    { name := "Bv32.Neg",
      inputs := [("x", mty[bv32])],
      output := mty[bv32],
      denote := none },

    /- Bv32 Comparison Operations -/
    { name := "Bv32.Lt",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bool],
      denote := none },
    { name := "Bv32.Le",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bool],
      denote := none },
    { name := "Bv32.Gt",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bool],
      denote := none },
    { name := "Bv32.Ge",
      inputs := [("x", mty[bv32]), ("y", mty[bv32])],
      output := mty[bool],
      denote := none },

    /- Bv64 Arithmetic Operations -/
    { name := "Bv64.Add",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bv64],
      denote := none },
    { name := "Bv64.Sub",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bv64],
      denote := none },
    { name := "Bv64.Mul",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bv64],
      denote := none },
    { name := "Bv64.Neg",
      inputs := [("x", mty[bv64])],
      output := mty[bv64],
      denote := none },

    /- Bv64 Comparison Operations -/
    { name := "Bv64.Lt",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bool],
      denote := none },
    { name := "Bv64.Le",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bool],
      denote := none },
    { name := "Bv64.Gt",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bool],
      denote := none },
    { name := "Bv64.Ge",
      inputs := [("x", mty[bv64]), ("y", mty[bv64])],
      output := mty[bool],
      denote := none },

    /- Real Arithmetic Operations -/
    { name := "Real.Add",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[real],
      denote := none },
    { name := "Real.Sub",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[real],
      denote := none },
    { name := "Real.Mul",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[real],
      denote := none },
    { name := "Real.Div",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[real],
      denote := none },
    { name := "Real.Neg",
      inputs := [("x", mty[real])],
      output := mty[real],
      denote := none },

    /- Real Comparison Operations -/
    { name := "Real.Lt",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[bool],
      denote := none },
    { name := "Real.Le",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[bool],
      denote := none },
    { name := "Real.Gt",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[bool],
      denote := none },
    { name := "Real.Ge",
      inputs := [("x", mty[real]), ("y", mty[real])],
      output := mty[bool],
      denote := none },

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
     output := mapTy mty[%k] mty[%v] }]

---------------------------------------------------------------------

end Boogie

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LState

/-! ## A Minimal Factory with Support for Unbounded Integer and Boolean Operations

See also `Strata.DL.Lambda.Factory`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open LExpr LTy

section IntBoolFactory

def unOpDenote  {Identifier : Type} (InTy OutTy : Type) [ToString OutTy]
                (denoteInTy : (LExpr Identifier) → Option InTy) (op : InTy → OutTy)
                (ty : LMonoTy) :
                (LExpr Identifier) → List (LExpr Identifier) → (LExpr Identifier) :=
  (fun e args => match args with
   | [e1] =>
     let e1i := denoteInTy e1
     match e1i with
     | some x => (LExpr.const (toString (op x)) ty)
     | _ => e
   | _ => e)

def binOpDenote {Identifier : Type} (InTy OutTy : Type) [ToString OutTy]
                (denoteInTy : (LExpr Identifier) → Option InTy) (op : InTy → InTy → OutTy)
                (ty : LMonoTy) :
                (LExpr Identifier) → List (LExpr Identifier) → (LExpr Identifier) :=
  (fun e args => match args with
   | [e1, e2] =>
     let e1i := denoteInTy e1
     let e2i := denoteInTy e2
     match e1i, e2i with
     | some x, some y => (LExpr.const (toString (op x y)) ty)
     | _, _ => e
   | _ => e)

def IntBoolFactory : @Factory String :=
  open LTy.Syntax in
  #[{ name := "Int.Add",
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
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int],
      denote := some (unOpDenote Int Int LExpr.denoteInt Int.neg mty[int]) },

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
   ]

end IntBoolFactory

---------------------------------------------------------------------

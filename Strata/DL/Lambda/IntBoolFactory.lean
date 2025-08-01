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

def unaryOp [Coe String Ident]
            (n : Ident)
            (ty : LMonoTy)
            (denote : Option (LExpr Ident → List (LExpr Ident) → LExpr Ident)) : LFunc Ident :=
  { name := n,
    inputs := [("x", ty)],
    output := ty,
    denote := denote }

def binaryOp [Coe String Ident]
             (n : Ident)
             (ty : LMonoTy)
             (denote : Option (LExpr Ident → List (LExpr Ident) → LExpr Ident)) : LFunc Ident :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := ty,
    denote := denote }

def binaryPredicate [Coe String Ident]
                    (n : Ident)
                    (ty : LMonoTy)
                    (denote : Option (LExpr Ident → List (LExpr Ident) → LExpr Ident)) : LFunc Ident :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := .bool,
    denote := denote }

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

-- We hand-code a denotation for `Int.Div` to leave the expression
-- unchanged if we have `0` for the denominator.
def denoteIntDiv (e : LExpr Ident) (args : List (LExpr Ident)) : LExpr Ident :=
  match args with
  | [e1, e2] =>
    let e1i := LExpr.denoteInt e1
    let e2i := LExpr.denoteInt e2
    match e1i, e2i with
    | some x, some y =>
      if y == 0 then e else (.const (toString (x / y)) (.some .int))
    | _, _ => e
  | _ => e

-- We hand-code a denotation for `Int.Mod` to leave the expression
-- unchanged if we have `0` for the denominator.
def denoteIntMod (e : LExpr Ident) (args : List (LExpr Ident)) : LExpr Ident :=
  match args with
  | [e1, e2] =>
    let e1i := LExpr.denoteInt e1
    let e2i := LExpr.denoteInt e2
    match e1i, e2i with
    | some x, some y =>
      if y == 0 then e else (.const (toString (x % y)) (.some .int))
    | _, _ => e
  | _ => e

/- Integer Arithmetic Operations -/

def intAddFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Int.Add" .int
  (some (binOpDenote Int Int LExpr.denoteInt Int.add .int))

def intSubFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Int.Sub" .int
  (some (binOpDenote Int Int LExpr.denoteInt Int.sub .int))

def intMulFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Int.Mul" .int
  (some (binOpDenote Int Int LExpr.denoteInt Int.mul .int))

def intDivFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Int.Div" .int
  (some denoteIntDiv)

def intModFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Int.Mod" .int
  (some denoteIntMod)

def intNegFunc [Coe String Ident] : LFunc Ident :=
  unaryOp "Int.Neg" .int
  (some (unOpDenote Int Int LExpr.denoteInt Int.neg .int))

def intLtFunc [Coe String Ident] : LFunc Ident :=
  binaryPredicate "Int.Lt" .int
  (some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x < y) .bool))

def intLeFunc [Coe String Ident] : LFunc Ident :=
  binaryPredicate "Int.Le" .int
  (some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x <= y) .bool))

def intGtFunc [Coe String Ident] : LFunc Ident :=
  binaryPredicate "Int.Gt" .int
  (some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x > y) .bool))

def intGeFunc [Coe String Ident] : LFunc Ident :=
  binaryPredicate "Int.Ge" .int
  (some (binOpDenote Int Bool LExpr.denoteInt (fun x y => x >= y) .bool))

/- Boolean Operations -/
def boolAndFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Bool.And" .bool
  (some (binOpDenote Bool Bool LExpr.denoteBool Bool.and .bool))

def boolOrFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Bool.Or" .bool
  (some (binOpDenote Bool Bool LExpr.denoteBool Bool.or .bool))

def boolImpliesFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Bool.Implies" .bool
  (some (binOpDenote Bool Bool LExpr.denoteBool (fun x y => ((not x) || y)) .bool))

def boolEquivFunc [Coe String Ident] : LFunc Ident :=
  binaryOp "Bool.Equiv" .bool
  (some (binOpDenote Bool Bool LExpr.denoteBool (fun x y => (x == y)) .bool))

def boolNotFunc [Coe String Ident] : LFunc Ident :=
  unaryOp "Bool.Not" .bool
  (some (unOpDenote Bool Bool LExpr.denoteBool Bool.not .bool))

def IntBoolFactory : @Factory String :=
  open LTy.Syntax in #[
    intAddFunc,
    intSubFunc,
    intMulFunc,
    intDivFunc,
    intModFunc,
    intNegFunc,
    intLtFunc,
    intLeFunc,
    intGtFunc,
    intGeFunc,

    boolAndFunc,
    boolOrFunc,
    boolImpliesFunc,
    boolEquivFunc,
    boolNotFunc,
  ]

end IntBoolFactory

---------------------------------------------------------------------

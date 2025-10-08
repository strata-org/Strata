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
            (ty : LMonoTy ExtraRestrict)
            (ceval : Option (LExpr (LMonoTy ExtraRestrict) Ident → List (LExpr (LMonoTy ExtraRestrict) Ident) → LExpr (LMonoTy ExtraRestrict) Ident)) : LFunc Ident ExtraRestrict :=
  { name := n,
    inputs := [("x", ty)],
    output := ty,
    concreteEval := ceval }

def binaryOp [Coe String Ident]
             (n : Ident)
             (ty : LMonoTy ExtraRestrict)
             (ceval : Option (LExpr (LMonoTy ExtraRestrict) Ident → List (LExpr (LMonoTy ExtraRestrict) Ident) → LExpr (LMonoTy ExtraRestrict) Ident)) : LFunc Ident ExtraRestrict :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := ty,
    concreteEval := ceval }

def binaryPredicate [Coe String Ident]
                    (n : Ident)
                    (ty : LMonoTy ExtraRestrict)
                    (ceval : Option (LExpr (LMonoTy ExtraRestrict) Ident → List (LExpr (LMonoTy ExtraRestrict) Ident) → LExpr (LMonoTy ExtraRestrict) Ident)) : LFunc Ident ExtraRestrict :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := .bool,
    concreteEval := ceval }

def unOpCeval  {Identifier ExtraRestrict: Type} (InTy OutTy : Type) [ToString OutTy]
                (cevalInTy : (LExpr (LMonoTy ExtraRestrict) Identifier) → Option InTy) (op : InTy → OutTy)
                (ty : LMonoTy ExtraRestrict) :
                (LExpr (LMonoTy ExtraRestrict) Identifier) → List (LExpr (LMonoTy ExtraRestrict) Identifier) → (LExpr (LMonoTy ExtraRestrict) Identifier) :=
  (fun e args => match args with
   | [e1] =>
     let e1i := cevalInTy e1
     match e1i with
     | some x => (LExpr.const (toString (op x)) ty)
     | _ => e
   | _ => e)

def binOpCeval {Identifier : Type} (InTy OutTy : Type) [ToString OutTy]
                (cevalInTy : (LExpr (LMonoTy ExtraRestrict) Identifier) → Option InTy) (op : InTy → InTy → OutTy)
                (ty : LMonoTy ExtraRestrict) :
                (LExpr (LMonoTy ExtraRestrict) Identifier) → List (LExpr (LMonoTy ExtraRestrict) Identifier) → (LExpr (LMonoTy ExtraRestrict) Identifier) :=
  (fun e args => match args with
   | [e1, e2] =>
     let e1i := cevalInTy e1
     let e2i := cevalInTy e2
     match e1i, e2i with
     | some x, some y => (LExpr.const (toString (op x y)) ty)
     | _, _ => e
   | _ => e)

-- We hand-code a denotation for `Int.Div` to leave the expression
-- unchanged if we have `0` for the denominator.
def cevalIntDiv (e : LExpr (LMonoTy ExtraRestrict) Ident) (args : List (LExpr (LMonoTy ExtraRestrict) Ident)) : LExpr (LMonoTy ExtraRestrict) Ident :=
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
def cevalIntMod (e : LExpr (LMonoTy ExtraRestrict) Ident) (args : List (LExpr (LMonoTy ExtraRestrict) Ident)) : LExpr (LMonoTy ExtraRestrict) Ident :=
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

def intAddFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Int.Add" .int
  (some (binOpCeval Int Int LExpr.denoteInt Int.add .int))

def intSubFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Int.Sub" .int
  (some (binOpCeval Int Int LExpr.denoteInt Int.sub .int))

def intMulFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Int.Mul" .int
  (some (binOpCeval Int Int LExpr.denoteInt Int.mul .int))

def intDivFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Int.Div" .int
  (some cevalIntDiv)

def intModFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Int.Mod" .int
  (some cevalIntMod)

def intNegFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  unaryOp "Int.Neg" .int
  (some (unOpCeval Int Int LExpr.denoteInt Int.neg .int))

def intLtFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryPredicate "Int.Lt" .int
  (some (binOpCeval Int Bool LExpr.denoteInt (fun x y => x < y) .bool))

def intLeFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryPredicate "Int.Le" .int
  (some (binOpCeval Int Bool LExpr.denoteInt (fun x y => x <= y) .bool))

def intGtFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryPredicate "Int.Gt" .int
  (some (binOpCeval Int Bool LExpr.denoteInt (fun x y => x > y) .bool))

def intGeFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryPredicate "Int.Ge" .int
  (some (binOpCeval Int Bool LExpr.denoteInt (fun x y => x >= y) .bool))

/- Boolean Operations -/
def boolAndFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Bool.And" .bool
  (some (binOpCeval Bool Bool LExpr.denoteBool Bool.and .bool))

def boolOrFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Bool.Or" .bool
  (some (binOpCeval Bool Bool LExpr.denoteBool Bool.or .bool))

def boolImpliesFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Bool.Implies" .bool
  (some (binOpCeval Bool Bool LExpr.denoteBool (fun x y => ((not x) || y)) .bool))

def boolEquivFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  binaryOp "Bool.Equiv" .bool
  (some (binOpCeval Bool Bool LExpr.denoteBool (fun x y => (x == y)) .bool))

def boolNotFunc [Coe String Ident] : LFunc Ident ExtraRestrict :=
  unaryOp "Bool.Not" .bool
  (some (unOpCeval Bool Bool LExpr.denoteBool Bool.not .bool))

def IntBoolFactory : @Factory String Empty :=
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

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

variable {T : LExprParams} [Coe String T.Identifier]

def unaryOp (n : T.Identifier)
            (ty : LMonoTy)
            (ceval : Option (LExpr T.mono → List (LExpr T.mono) → LExpr T.mono)) : LFunc T :=
  { name := n,
    inputs := [("x", ty)],
    output := ty,
    concreteEval := ceval }

def binaryOp (n : T.Identifier)
             (ty : LMonoTy)
             (ceval : Option (LExpr T.mono → List (LExpr T.mono) → LExpr T.mono)) : LFunc T :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := ty,
    concreteEval := ceval }

def binaryPredicate (n : T.Identifier)
                    (ty : LMonoTy)
                    (ceval : Option (LExpr T.mono → List (LExpr T.mono) → LExpr T.mono)) : LFunc T :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := .bool,
    concreteEval := ceval }

def unOpCeval (InTy OutTy : Type) [ToString OutTy]
                (cevalInTy : (LExpr T.mono) → Option InTy) (op : InTy → OutTy)
                (ty : LMonoTy) :
                (LExpr T.mono) → List (LExpr T.mono) → (LExpr T.mono) :=
  (fun e args => match args with
   | [e1] =>
     let e1i := cevalInTy e1
     match e1i with
     | some x => (LExpr.const e1.metadata (toString (op x)) ty)
     | _ => e
   | _ => e)

def binOpCeval (InTy OutTy : Type) [ToString OutTy]
                (cevalInTy : (LExpr T.mono) → Option InTy) (op : InTy → InTy → OutTy)
                (ty : LMonoTy) :
                (LExpr T.mono) → List (LExpr T.mono) → (LExpr T.mono) :=
  (fun e args => match args with
   | [e1, e2] =>
     let e1i := cevalInTy e1
     let e2i := cevalInTy e2
     match e1i, e2i with
     | some x, some y => (LExpr.const e1.metadata (toString (op x y)) ty)
     | _, _ => e
   | _ => e)

-- We hand-code a denotation for `Int.Div` to leave the expression
-- unchanged if we have `0` for the denominator.
def cevalIntDiv (e : LExpr T.mono) (args : List (LExpr T.mono)) : LExpr T.mono :=
  match args with
  | [e1, e2] =>
    let e1i := LExpr.denoteInt T e1
    let e2i := LExpr.denoteInt T e2
    match e1i, e2i with
    | some x, some y =>
      if y == 0 then e else (.const e.metadata (toString (x / y)) (.some .int))
    | _, _ => e
  | _ => e

-- We hand-code a denotation for `Int.Mod` to leave the expression
-- unchanged if we have `0` for the denominator.
def cevalIntMod (e : LExpr T.mono) (args : List (LExpr T.mono)) : LExpr T.mono :=
  match args with
  | [e1, e2] =>
    let e1i := LExpr.denoteInt T e1
    let e2i := LExpr.denoteInt T e2
    match e1i, e2i with
    | some x, some y =>
      if y == 0 then e else (.const e.metadata (toString (x % y)) (.some .int))
    | _, _ => e
  | _ => e

/- Integer Arithmetic Operations -/

def intAddFunc : LFunc T :=
  binaryOp "Int.Add" .int
  (some (binOpCeval Int Int (LExpr.denoteInt T) Int.add .int))

def intSubFunc : LFunc T :=
  binaryOp "Int.Sub" .int
  (some (binOpCeval Int Int (LExpr.denoteInt T) Int.sub .int))

def intMulFunc : LFunc T :=
  binaryOp "Int.Mul" .int
  (some (binOpCeval Int Int (LExpr.denoteInt T) Int.mul .int))

def intDivFunc : LFunc T :=
  binaryOp "Int.Div" .int
  (some cevalIntDiv)

def intModFunc : LFunc T :=
  binaryOp "Int.Mod" .int
  (some cevalIntMod)

def intNegFunc : LFunc T :=
  unaryOp "Int.Neg" .int
  (some (unOpCeval Int Int (LExpr.denoteInt T) Int.neg .int))

def intLtFunc : LFunc T :=
  binaryPredicate "Int.Lt" .int
  (some (binOpCeval Int Bool (LExpr.denoteInt T) (fun x y => x < y) .bool))

def intLeFunc : LFunc T :=
  binaryPredicate "Int.Le" .int
  (some (binOpCeval Int Bool (LExpr.denoteInt T) (fun x y => x <= y) .bool))

def intGtFunc : LFunc T :=
  binaryPredicate "Int.Gt" .int
  (some (binOpCeval Int Bool (LExpr.denoteInt T) (fun x y => x > y) .bool))

def intGeFunc : LFunc T :=
  binaryPredicate "Int.Ge" .int
  (some (binOpCeval Int Bool (LExpr.denoteInt T) (fun x y => x >= y) .bool))

/- Boolean Operations -/
def boolAndFunc : LFunc T :=
  binaryOp "Bool.And" .bool
  (some (binOpCeval Bool Bool (LExpr.denoteBool T) Bool.and .bool))

def boolOrFunc : LFunc T :=
  binaryOp "Bool.Or" .bool
  (some (binOpCeval Bool Bool (LExpr.denoteBool T) Bool.or .bool))

def boolImpliesFunc : LFunc T :=
  binaryOp "Bool.Implies" .bool
  (some (binOpCeval Bool Bool (LExpr.denoteBool T) (fun x y => ((not x) || y)) .bool))

def boolEquivFunc : LFunc T :=
  binaryOp "Bool.Equiv" .bool
  (some (binOpCeval Bool Bool (LExpr.denoteBool T) (fun x y => (x == y)) .bool))

def boolNotFunc : LFunc T :=
  unaryOp "Bool.Not" .bool
  (some (unOpCeval Bool Bool (LExpr.denoteBool T) Bool.not .bool))

def IntBoolFactory : @Factory T :=
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

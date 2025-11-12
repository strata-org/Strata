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

def unaryOp[Coe String (Identifier IDMeta)]
            (n : Identifier IDMeta)
            (ty : LMonoTy)
            (ceval : Option (LExpr LMonoTy IDMeta → List (LExpr LMonoTy IDMeta) → LExpr LMonoTy IDMeta)) : LFunc IDMeta :=
  { name := n,
    inputs := [("x", ty)],
    output := ty,
    concreteEval := ceval }

def binaryOp [Coe String (Identifier IDMeta)]
             (n : Identifier IDMeta)
             (ty : LMonoTy)
             (ceval : Option (LExpr LMonoTy IDMeta → List (LExpr LMonoTy IDMeta) → LExpr LMonoTy IDMeta)) : LFunc IDMeta :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := ty,
    concreteEval := ceval }

def binaryPredicate [Coe String (Identifier IDMeta)]
                    (n : Identifier IDMeta)
                    (ty : LMonoTy)
                    (ceval : Option (LExpr LMonoTy IDMeta → List (LExpr LMonoTy IDMeta) → LExpr LMonoTy IDMeta)) : LFunc IDMeta :=
  { name := n,
    inputs := [("x", ty), ("y", ty)],
    output := .bool,
    concreteEval := ceval }

def unOpCeval  {IDMeta : Type} (InTy OutTy : Type) [ToString OutTy]
                (mkConst : OutTy → LExpr LMonoTy IDMeta)
                (cevalInTy : (LExpr LMonoTy IDMeta) → Option InTy) (op : InTy → OutTy):
                (LExpr LMonoTy IDMeta) → List (LExpr LMonoTy IDMeta) → (LExpr LMonoTy IDMeta) :=
  (fun e args => match args with
   | [e1] =>
     let e1i := cevalInTy e1
     match e1i with
     | some x => mkConst (op x)
     | _ => e
   | _ => e)

def binOpCeval {IDMeta : Type} (InTy OutTy : Type) [ToString OutTy]
                (mkConst : OutTy → LExpr LMonoTy IDMeta)
                (cevalInTy : (LExpr LMonoTy IDMeta) → Option InTy) (op : InTy → InTy → OutTy) :
                (LExpr LMonoTy IDMeta) → List (LExpr LMonoTy IDMeta) → (LExpr LMonoTy IDMeta) :=
  (fun e args => match args with
   | [e1, e2] =>
     let e1i := cevalInTy e1
     let e2i := cevalInTy e2
     match e1i, e2i with
     | some x, some y => mkConst (op x y)
     | _, _ => e
   | _ => e)

-- We hand-code a denotation for `Int.Div` to leave the expression
-- unchanged if we have `0` for the denominator.
def cevalIntDiv (e : LExpr LMonoTy IDMeta) (args : List (LExpr LMonoTy IDMeta)) : LExpr LMonoTy IDMeta :=
  match args with
  | [e1, e2] =>
    let e1i := LExpr.denoteInt e1
    let e2i := LExpr.denoteInt e2
    match e1i, e2i with
    | some x, some y =>
      if y == 0 then e else .intConst (x / y)
    | _, _ => e
  | _ => e

-- We hand-code a denotation for `Int.Mod` to leave the expression
-- unchanged if we have `0` for the denominator.
def cevalIntMod (e : LExpr LMonoTy IDMeta) (args : List (LExpr LMonoTy IDMeta)) : LExpr LMonoTy IDMeta :=
  match args with
  | [e1, e2] =>
    let e1i := LExpr.denoteInt e1
    let e2i := LExpr.denoteInt e2
    match e1i, e2i with
    | some x, some y =>
      if y == 0 then e else .intConst (x % y)
    | _, _ => e
  | _ => e

/- Integer Arithmetic Operations -/

def intAddFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Int.Add" .int
  (some (binOpCeval Int Int intConst LExpr.denoteInt Int.add))

def intSubFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Int.Sub" .int
  (some (binOpCeval Int Int intConst LExpr.denoteInt Int.sub))

def intMulFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Int.Mul" .int
  (some (binOpCeval Int Int intConst LExpr.denoteInt Int.mul))

def intDivFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Int.Div" .int
  (some cevalIntDiv)

def intModFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Int.Mod" .int
  (some cevalIntMod)

def intNegFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  unaryOp "Int.Neg" .int
  (some (unOpCeval Int Int intConst LExpr.denoteInt Int.neg))

def intLtFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryPredicate "Int.Lt" .int
  (some (binOpCeval Int Bool boolConst LExpr.denoteInt (fun x y => x < y)))

def intLeFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryPredicate "Int.Le" .int
  (some (binOpCeval Int Bool boolConst LExpr.denoteInt (fun x y => x <= y)))

def intGtFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta:=
  binaryPredicate "Int.Gt" .int
  (some (binOpCeval Int Bool boolConst LExpr.denoteInt (fun x y => x > y)))

def intGeFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryPredicate "Int.Ge" .int
  (some (binOpCeval Int Bool boolConst LExpr.denoteInt (fun x y => x >= y)))

/- Boolean Operations -/
def boolAndFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Bool.And" .bool
  (some (binOpCeval Bool Bool boolConst LExpr.denoteBool Bool.and))

def boolOrFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Bool.Or" .bool
  (some (binOpCeval Bool Bool boolConst LExpr.denoteBool Bool.or))

def boolImpliesFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Bool.Implies" .bool
  (some (binOpCeval Bool Bool boolConst LExpr.denoteBool (fun x y => ((not x) || y))))

def boolEquivFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  binaryOp "Bool.Equiv" .bool
  (some (binOpCeval Bool Bool boolConst LExpr.denoteBool (fun x y => (x == y))))

def boolNotFunc [Coe String (Identifier IDMeta)] : LFunc IDMeta :=
  unaryOp "Bool.Not" .bool
  (some (unOpCeval Bool Bool boolConst LExpr.denoteBool Bool.not))

def IntBoolFactory : @Factory Unit :=
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

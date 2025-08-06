/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Identifiers
import Strata.Languages.Boogie.Expressions
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.IntBoolFactory
---------------------------------------------------------------------

namespace Boogie
open Lambda LTy.Syntax LExpr.Syntax

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

/--
  Convert an LExpr String to an LExpr BoogieIdent, by considering all identifier as global, which is valid for axioms
  TODO: Remove when Lambda elaborator offers parametric identifier type
-/
def ToBoogieIdent (ine: LExpr String): (LExpr BoogieIdent) :=
match ine with
    | .const c ty => .const c ty
    | .op o oty => .op (BoogieIdent.glob o) oty
    | .bvar deBruijnIndex => .bvar deBruijnIndex
    | .fvar name oty => .fvar (BoogieIdent.glob name) oty
    | .mdata info e => .mdata info (ToBoogieIdent e)
    | .abs oty e => .abs oty (ToBoogieIdent e)
    | .quant k oty e => .quant k oty (ToBoogieIdent e)
    | .app fn e => .app (ToBoogieIdent fn) (ToBoogieIdent e)
    | .ite c t e => .ite (ToBoogieIdent c) (ToBoogieIdent t) (ToBoogieIdent e)
    | .eq e1 e2 => .eq (ToBoogieIdent e1) (ToBoogieIdent e2)

/- Bv1 Arithmetic Operations -/
def bv1AddFunc : LFunc BoogieIdent := binaryOp "Bv1.Add" mty[bv1] none
def bv1SubFunc : LFunc BoogieIdent := binaryOp "Bv1.Sub" mty[bv1] none
def bv1MulFunc : LFunc BoogieIdent := binaryOp "Bv1.Mul" mty[bv1] none
def bv1NegFunc : LFunc BoogieIdent := unaryOp "Bv1.Neg" mty[bv1] none

/- Bv1 Comparison Operations -/
def bv1LtFunc : LFunc BoogieIdent := binaryPredicate "Bv1.Lt" mty[bv1] none
def bv1LeFunc : LFunc BoogieIdent := binaryPredicate "Bv1.Le" mty[bv1] none
def bv1GtFunc : LFunc BoogieIdent := binaryPredicate "Bv1.Gt" mty[bv1] none
def bv1GeFunc : LFunc BoogieIdent := binaryPredicate "Bv1.Ge" mty[bv1] none

/- Bv8 Arithmetic Operations -/
def bv8AddFunc : LFunc BoogieIdent := binaryOp "Bv8.Add" mty[bv8] none
def bv8SubFunc : LFunc BoogieIdent := binaryOp "Bv8.Sub" mty[bv8] none
def bv8MulFunc : LFunc BoogieIdent := binaryOp "Bv8.Mul" mty[bv8] none
def bv8NegFunc : LFunc BoogieIdent := unaryOp "Bv8.Neg" mty[bv8] none

/- Bv8 Comparison Operations -/
def bv8LtFunc : LFunc BoogieIdent := binaryPredicate "Bv8.Lt" mty[bv8] none
def bv8LeFunc : LFunc BoogieIdent := binaryPredicate "Bv8.Le" mty[bv8] none
def bv8GtFunc : LFunc BoogieIdent := binaryPredicate "Bv8.Gt" mty[bv8] none
def bv8GeFunc : LFunc BoogieIdent := binaryPredicate "Bv8.Ge" mty[bv8] none

/- Bv16 Arithmetic Operations -/
def bv16AddFunc : LFunc BoogieIdent := binaryOp "Bv16.Add" mty[bv16] none
def bv16SubFunc : LFunc BoogieIdent := binaryOp "Bv16.Sub" mty[bv16] none
def bv16MulFunc : LFunc BoogieIdent := binaryOp "Bv16.Mul" mty[bv16] none
def bv16NegFunc : LFunc BoogieIdent := unaryOp "Bv16.Neg" mty[bv16] none

/- Bv16 Comparison Operations -/
def bv16LtFunc : LFunc BoogieIdent := binaryPredicate "Bv16.Lt" mty[bv16] none
def bv16LeFunc : LFunc BoogieIdent := binaryPredicate "Bv16.Le" mty[bv16] none
def bv16GtFunc : LFunc BoogieIdent := binaryPredicate "Bv16.Gt" mty[bv16] none
def bv16GeFunc : LFunc BoogieIdent := binaryPredicate "Bv16.Ge" mty[bv16] none

/- Bv32 Arithmetic Operations -/
def bv32AddFunc : LFunc BoogieIdent := binaryOp "Bv32.Add" mty[bv32] none
def bv32SubFunc : LFunc BoogieIdent := binaryOp "Bv32.Sub" mty[bv32] none
def bv32MulFunc : LFunc BoogieIdent := binaryOp "Bv32.Mul" mty[bv32] none
def bv32NegFunc : LFunc BoogieIdent := unaryOp "Bv32.Neg" mty[bv32] none

/- Bv32 Comparison Operations -/
def bv32LtFunc : LFunc BoogieIdent := binaryPredicate "Bv32.Lt" mty[bv32] none
def bv32LeFunc : LFunc BoogieIdent := binaryPredicate "Bv32.Le" mty[bv32] none
def bv32GtFunc : LFunc BoogieIdent := binaryPredicate "Bv32.Gt" mty[bv32] none
def bv32GeFunc : LFunc BoogieIdent := binaryPredicate "Bv32.Ge" mty[bv32] none

/- Bv64 Arithmetic Operations -/
def bv64AddFunc : LFunc BoogieIdent := binaryOp "Bv64.Add" mty[bv64] none
def bv64SubFunc : LFunc BoogieIdent := binaryOp "Bv64.Sub" mty[bv64] none
def bv64MulFunc : LFunc BoogieIdent := binaryOp "Bv64.Mul" mty[bv64] none
def bv64NegFunc : LFunc BoogieIdent := unaryOp "Bv64.Neg" mty[bv64] none

/- Bv64 Comparison Operations -/
def bv64LtFunc : LFunc BoogieIdent := binaryPredicate "Bv64.Lt" mty[bv64] none
def bv64LeFunc : LFunc BoogieIdent := binaryPredicate "Bv64.Le" mty[bv64] none
def bv64GtFunc : LFunc BoogieIdent := binaryPredicate "Bv64.Gt" mty[bv64] none
def bv64GeFunc : LFunc BoogieIdent := binaryPredicate "Bv64.Ge" mty[bv64] none

/- Real Arithmetic Operations -/

def realAddFunc : LFunc BoogieIdent := binaryOp "Real.Add" mty[real] none
def realSubFunc : LFunc BoogieIdent := binaryOp "Real.Sub" mty[real] none
def realMulFunc : LFunc BoogieIdent := binaryOp "Real.Mul" mty[real] none
def realDivFunc : LFunc BoogieIdent := binaryOp "Real.Div" mty[real] none
def realNegFunc : LFunc BoogieIdent := unaryOp "Real.Neg" mty[real] none

/- Real Comparison Operations -/
def realLtFunc : LFunc BoogieIdent := binaryPredicate "Real.Lt" mty[real] none
def realLeFunc : LFunc BoogieIdent := binaryPredicate "Real.Le" mty[real] none
def realGtFunc : LFunc BoogieIdent := binaryPredicate "Real.Gt" mty[real] none
def realGeFunc : LFunc BoogieIdent := binaryPredicate "Real.Ge" mty[real] none

/- String Operations -/

def strLengthFunc : LFunc BoogieIdent :=
    { name := "Str.Length",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[int],
      denote := some (unOpDenote String Int LExpr.denoteString
                        (fun s => (Int.ofNat (String.length s)))
                        mty[int])}

def strConcatFunc : LFunc BoogieIdent :=
    { name := "Str.Concat",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[string],
      denote := some (binOpDenote String String LExpr.denoteString
                       String.append mty[string])}

/- A polymorphic `old` function with type `∀a. a → a`. -/
def polyOldFunc : LFunc BoogieIdent :=
    { name := "old",
      typeArgs := ["a"],
      inputs := [((.locl, "x"), mty[%a])]
      output := mty[%a]}

/- A `Map` selection function with type `∀k, v. Map k v → k → v`. -/
def mapSelectFunc : LFunc BoogieIdent :=
   { name := "select",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])],
     output := mty[%v] }

/- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
def mapUpdateFunc : LFunc BoogieIdent :=
   { name := "update",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k]), ("x", mty[%v])],
     output := mapTy mty[%k] mty[%v],
     axioms :=
     [
      -- updateSelect
      ToBoogieIdent es[∀(Map %k %v):
          (∀ (%k):
            (∀ (%v):
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1) == %0))],
      -- update preserves
      ToBoogieIdent es[∀ (Map %k %v):
          (∀ (%k):
            (∀ (%k):
              (∀ (%v):
                  (((~select : (Map %k %v) → %k → %v)
                    ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %3) %1) %0)) %2)
                  ==
                  ((((~select : (Map %k %v) → %k → %v) %3) %2)))))]
     ]
   }

def Factory : @Factory BoogieIdent := #[
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

  bv1AddFunc,
  bv1SubFunc,
  bv1MulFunc,
  bv1NegFunc,
  bv1LtFunc,
  bv1LeFunc,
  bv1GtFunc,
  bv1GeFunc,

  bv8AddFunc,
  bv8SubFunc,
  bv8MulFunc,
  bv8NegFunc,
  bv8LtFunc,
  bv8LeFunc,
  bv8GtFunc,
  bv8GeFunc,

  bv16AddFunc,
  bv16SubFunc,
  bv16MulFunc,
  bv16NegFunc,
  bv16LtFunc,
  bv16LeFunc,
  bv16GtFunc,
  bv16GeFunc,

  bv32AddFunc,
  bv32SubFunc,
  bv32MulFunc,
  bv32NegFunc,
  bv32LtFunc,
  bv32LeFunc,
  bv32GtFunc,
  bv32GeFunc,

  bv64AddFunc,
  bv64SubFunc,
  bv64MulFunc,
  bv64NegFunc,
  bv64LtFunc,
  bv64LeFunc,
  bv64GtFunc,
  bv64GeFunc,

  realAddFunc,
  realSubFunc,
  realMulFunc,
  realDivFunc,
  realNegFunc,
  realLtFunc,
  realLeFunc,
  realGtFunc,
  realGeFunc,

  boolAndFunc,
  boolOrFunc,
  boolImpliesFunc,
  boolEquivFunc,
  boolNotFunc,

  strLengthFunc,
  strConcatFunc,

  polyOldFunc,

  mapSelectFunc,
  mapUpdateFunc,
]

def intAddOp : LExpr BoogieIdent := intAddFunc.opExpr
def intSubOp : LExpr BoogieIdent := intSubFunc.opExpr
def intMulOp : LExpr BoogieIdent := intMulFunc.opExpr
def intDivOp : LExpr BoogieIdent := intDivFunc.opExpr
def intModOp : LExpr BoogieIdent := intModFunc.opExpr
def intNegOp : LExpr BoogieIdent := intNegFunc.opExpr
def intLtOp : LExpr BoogieIdent := intLtFunc.opExpr
def intLeOp : LExpr BoogieIdent := intLeFunc.opExpr
def intGtOp : LExpr BoogieIdent := intGtFunc.opExpr
def intGeOp : LExpr BoogieIdent := intGeFunc.opExpr
def bv1AddOp : LExpr BoogieIdent := bv1AddFunc.opExpr
def bv1SubOp : LExpr BoogieIdent := bv1SubFunc.opExpr
def bv1MulOp : LExpr BoogieIdent := bv1MulFunc.opExpr
def bv1NegOp : LExpr BoogieIdent := bv1NegFunc.opExpr
def bv1LtOp : LExpr BoogieIdent := bv1LtFunc.opExpr
def bv1LeOp : LExpr BoogieIdent := bv1LeFunc.opExpr
def bv1GtOp : LExpr BoogieIdent := bv1GtFunc.opExpr
def bv1GeOp : LExpr BoogieIdent := bv1GeFunc.opExpr
def bv8AddOp : LExpr BoogieIdent := bv8AddFunc.opExpr
def bv8SubOp : LExpr BoogieIdent := bv8SubFunc.opExpr
def bv8MulOp : LExpr BoogieIdent := bv8MulFunc.opExpr
def bv8NegOp : LExpr BoogieIdent := bv8NegFunc.opExpr
def bv8LtOp : LExpr BoogieIdent := bv8LtFunc.opExpr
def bv8LeOp : LExpr BoogieIdent := bv8LeFunc.opExpr
def bv8GtOp : LExpr BoogieIdent := bv8GtFunc.opExpr
def bv8GeOp : LExpr BoogieIdent := bv8GeFunc.opExpr
def bv16AddOp : LExpr BoogieIdent := bv16AddFunc.opExpr
def bv16SubOp : LExpr BoogieIdent := bv16SubFunc.opExpr
def bv16MulOp : LExpr BoogieIdent := bv16MulFunc.opExpr
def bv16NegOp : LExpr BoogieIdent := bv16NegFunc.opExpr
def bv16LtOp : LExpr BoogieIdent := bv16LtFunc.opExpr
def bv16LeOp : LExpr BoogieIdent := bv16LeFunc.opExpr
def bv16GtOp : LExpr BoogieIdent := bv16GtFunc.opExpr
def bv16GeOp : LExpr BoogieIdent := bv16GeFunc.opExpr
def bv32AddOp : LExpr BoogieIdent := bv32AddFunc.opExpr
def bv32SubOp : LExpr BoogieIdent := bv32SubFunc.opExpr
def bv32MulOp : LExpr BoogieIdent := bv32MulFunc.opExpr
def bv32NegOp : LExpr BoogieIdent := bv32NegFunc.opExpr
def bv32LtOp : LExpr BoogieIdent := bv32LtFunc.opExpr
def bv32LeOp : LExpr BoogieIdent := bv32LeFunc.opExpr
def bv32GtOp : LExpr BoogieIdent := bv32GtFunc.opExpr
def bv32GeOp : LExpr BoogieIdent := bv32GeFunc.opExpr
def bv64AddOp : LExpr BoogieIdent := bv64AddFunc.opExpr
def bv64SubOp : LExpr BoogieIdent := bv64SubFunc.opExpr
def bv64MulOp : LExpr BoogieIdent := bv64MulFunc.opExpr
def bv64NegOp : LExpr BoogieIdent := bv64NegFunc.opExpr
def bv64LtOp : LExpr BoogieIdent := bv64LtFunc.opExpr
def bv64LeOp : LExpr BoogieIdent := bv64LeFunc.opExpr
def bv64GtOp : LExpr BoogieIdent := bv64GtFunc.opExpr
def bv64GeOp : LExpr BoogieIdent := bv64GeFunc.opExpr
def realAddOp : LExpr BoogieIdent := realAddFunc.opExpr
def realSubOp : LExpr BoogieIdent := realSubFunc.opExpr
def realMulOp : LExpr BoogieIdent := realMulFunc.opExpr
def realDivOp : LExpr BoogieIdent := realDivFunc.opExpr
def realNegOp : LExpr BoogieIdent := realNegFunc.opExpr
def realLtOp : LExpr BoogieIdent := realLtFunc.opExpr
def realLeOp : LExpr BoogieIdent := realLeFunc.opExpr
def realGtOp : LExpr BoogieIdent := realGtFunc.opExpr
def realGeOp : LExpr BoogieIdent := realGeFunc.opExpr
def boolAndOp : LExpr BoogieIdent := boolAndFunc.opExpr
def boolOrOp : LExpr BoogieIdent := boolOrFunc.opExpr
def boolImpliesOp : LExpr BoogieIdent := boolImpliesFunc.opExpr
def boolEquivOp : LExpr BoogieIdent := boolEquivFunc.opExpr
def boolNotOp : LExpr BoogieIdent := boolNotFunc.opExpr
def strLengthOp : LExpr BoogieIdent := strLengthFunc.opExpr
def strConcatOp : LExpr BoogieIdent := strConcatFunc.opExpr
def polyOldOp : LExpr BoogieIdent := polyOldFunc.opExpr
def mapSelectOp : LExpr BoogieIdent := mapSelectFunc.opExpr
def mapUpdateOp : LExpr BoogieIdent := mapUpdateFunc.opExpr

end Boogie

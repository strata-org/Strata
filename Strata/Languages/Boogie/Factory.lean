/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Elab.Command

import Strata.Languages.Boogie.Identifiers
import Strata.Languages.Boogie.Expressions
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.IntBoolFactory
---------------------------------------------------------------------

namespace Boogie
open Lambda LTy.Syntax LExpr.SyntaxMono

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
  Convert an LExpr LMonoTy String to an LExpr LMonoTy BoogieIdent
  TODO: Remove when Lambda elaborator offers parametric identifier type
-/
def ToBoogieIdent (ine: LExpr LMonoTy String): (LExpr LMonoTy BoogieIdent) :=
match ine with
    | .const c ty => .const c ty
    | .op o oty => .op (BoogieIdent.unres o) oty
    | .bvar deBruijnIndex => .bvar deBruijnIndex
    | .fvar name oty => .fvar (BoogieIdent.unres name) oty
    | .mdata info e => .mdata info (ToBoogieIdent e)
    | .abs oty e => .abs oty (ToBoogieIdent e)
    | .quant k oty tr e => .quant k oty (ToBoogieIdent tr) (ToBoogieIdent e)
    | .app fn e => .app (ToBoogieIdent fn) (ToBoogieIdent e)
    | .ite c t e => .ite (ToBoogieIdent c) (ToBoogieIdent t) (ToBoogieIdent e)
    | .eq e1 e2 => .eq (ToBoogieIdent e1) (ToBoogieIdent e2)

private def BVOpNames :=
  ["Neg", "Add", "Sub", "Mul", "Div", "Mod",
   "Not", "And", "Or", "Xor", "Shl", "UShr",
   "Lt", "Le", "Gt", "Ge"]

private def BVCompNames := ["Lt", "Le", "Gt", "Ge"]

private def BVOpAritys := ["unaryOp", "binaryOp", "binaryOp", "binaryOp",
                           "binaryOp", "binaryOp", "unaryOp", "binaryOp",
                           "binaryOp", "binaryOp", "binaryOp", "binaryOp",
                           "binaryPredicate", "binaryPredicate", "binaryPredicate", "binaryPredicate", ]

/--
info: [("Neg", "unaryOp"), ("Add", "binaryOp"), ("Sub", "binaryOp"), ("Mul", "binaryOp"), ("Div", "binaryOp"),
  ("Mod", "binaryOp"), ("Not", "unaryOp"), ("And", "binaryOp"), ("Or", "binaryOp"), ("Xor", "binaryOp"),
  ("Shl", "binaryOp"), ("UShr", "binaryOp"), ("Lt", "binaryPredicate"), ("Le", "binaryPredicate"),
  ("Gt", "binaryPredicate"), ("Ge", "binaryPredicate")]
-/
#guard_msgs in
#eval List.zip (BVOpNames ++ BVCompNames) BVOpAritys

open Lean Elab Command in
elab "ExpandBVOpFuncDefs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for (op, arity) in List.zip (BVOpNames ++ BVCompNames) BVOpAritys do
      let funcName := mkIdent (.str .anonymous s!"bv{s}{op}Func")
      let funcArity := mkIdent (.str (.str .anonymous "Lambda") arity)
      let opName := Syntax.mkStrLit s!"Bv{s}.{op}"
      let bvTypeName := Name.mkSimple s!"bv{s}"
      elabCommand (← `(def $funcName : LFunc BoogieIdent := $funcArity $opName mty[$(mkIdent bvTypeName):ident] none))

-- def bv1AddOp : LExpr BoogieIdent := bv1AddFunc.opExpr
ExpandBVOpFuncDefs[1, 2, 8, 16, 32, 64]

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
      concreteEval := some (unOpCeval String Int LExpr.denoteString
                            (fun s => (Int.ofNat (String.length s)))
                            mty[int])}

def strConcatFunc : LFunc BoogieIdent :=
    { name := "Str.Concat",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[string],
      concreteEval := some (binOpCeval String String LExpr.denoteString
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
      -- updateSelect: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv
      ToBoogieIdent esM[∀(Map %k %v):
          (∀ (%k):
            (∀ (%v):{
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1)}
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1) == %0))],
      -- updatePreserve: forall m: Map k v, okk: k, kk: k, vv: v :: okk != kk ==> m[kk := vv][okk] == m[okk]
      ToBoogieIdent esM[∀ (Map %k %v): -- %3 m
          (∀ (%k): -- %2 okk
            (∀ (%k): -- %1 kk
              (∀ (%v): -- %0 vv
                  -- okk != kk ==> ...
                  (if (%2 == %1) then
                      #true
                  else
                    -- if keys are different, the value of the other key one remains unchanged
                    -- (select (update m kk vv) okk) ==  (select m okk)
                    ((((~select : (Map %k %v) → %k → %v)
                        ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %3) %1) %0)
                      ) %2)
                    ==
                    ((((~select : (Map %k %v) → %k → %v) %3) %2)))
                    ))))]
     ]
   }

open Lean in
macro "ExpandBVOpFuncNames" "[" sizes:num,* "]" : term => do
  let mut allOps := #[]
  for size in sizes.getElems do
    let s := size.getNat.repr
    let ops := BVOpNames.map (mkIdent ∘ (.str (.str .anonymous "Boogie")) ∘ (s!"bv{s}" ++ · ++ "Func"))
    allOps := allOps ++ ops.toArray
  `([$(allOps),*])

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
] ++ ExpandBVOpFuncNames [1,8,16,32,64]

open Lean Elab Command in
elab "DefBVOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for op in BVOpNames do
      let opName := mkIdent (.str .anonymous s!"bv{s}{op}Op")
      let funcName := mkIdent (.str (.str .anonymous "Boogie") s!"bv{s}{op}Func")
      elabCommand (← `(def $opName : LExpr LMonoTy BoogieIdent := ($funcName).opExpr))

DefBVOpFuncExprs [1, 8, 16, 32, 64]

def intAddOp : LExpr LMonoTy BoogieIdent := intAddFunc.opExpr
def intSubOp : LExpr LMonoTy BoogieIdent := intSubFunc.opExpr
def intMulOp : LExpr LMonoTy BoogieIdent := intMulFunc.opExpr
def intDivOp : LExpr LMonoTy BoogieIdent := intDivFunc.opExpr
def intModOp : LExpr LMonoTy BoogieIdent := intModFunc.opExpr
def intNegOp : LExpr LMonoTy BoogieIdent := intNegFunc.opExpr
def intLtOp : LExpr LMonoTy BoogieIdent := intLtFunc.opExpr
def intLeOp : LExpr LMonoTy BoogieIdent := intLeFunc.opExpr
def intGtOp : LExpr LMonoTy BoogieIdent := intGtFunc.opExpr
def intGeOp : LExpr LMonoTy BoogieIdent := intGeFunc.opExpr
def realAddOp : LExpr LMonoTy BoogieIdent := realAddFunc.opExpr
def realSubOp : LExpr LMonoTy BoogieIdent := realSubFunc.opExpr
def realMulOp : LExpr LMonoTy BoogieIdent := realMulFunc.opExpr
def realDivOp : LExpr LMonoTy BoogieIdent := realDivFunc.opExpr
def realNegOp : LExpr LMonoTy BoogieIdent := realNegFunc.opExpr
def realLtOp : LExpr LMonoTy BoogieIdent := realLtFunc.opExpr
def realLeOp : LExpr LMonoTy BoogieIdent := realLeFunc.opExpr
def realGtOp : LExpr LMonoTy BoogieIdent := realGtFunc.opExpr
def realGeOp : LExpr LMonoTy BoogieIdent := realGeFunc.opExpr
def boolAndOp : LExpr LMonoTy BoogieIdent := boolAndFunc.opExpr
def boolOrOp : LExpr LMonoTy BoogieIdent := boolOrFunc.opExpr
def boolImpliesOp : LExpr LMonoTy BoogieIdent := boolImpliesFunc.opExpr
def boolEquivOp : LExpr LMonoTy BoogieIdent := boolEquivFunc.opExpr
def boolNotOp : LExpr LMonoTy BoogieIdent := boolNotFunc.opExpr
def strLengthOp : LExpr LMonoTy BoogieIdent := strLengthFunc.opExpr
def strConcatOp : LExpr LMonoTy BoogieIdent := strConcatFunc.opExpr
def polyOldOp : LExpr LMonoTy BoogieIdent := polyOldFunc.opExpr
def mapSelectOp : LExpr LMonoTy BoogieIdent := mapSelectFunc.opExpr
def mapUpdateOp : LExpr LMonoTy BoogieIdent := mapUpdateFunc.opExpr

end Boogie

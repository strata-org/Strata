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

def KnownLTys : LTys :=
  [t[bool],
   t[int],
   t[string],
   t[real],
   t[Triggers],
   t[TriggerGroup],
   -- Note: t[bv<n>] elaborates to (.forAll [] .tcons "bitvec" <n>).
   -- We can simply add the following here.
   t[∀n. bitvec n],
   t[∀a b. %a → %b],
   t[∀a b. Map %a %b]]

def KnownTypes : KnownTypes :=
  makeKnownTypes (KnownLTys.map (fun ty => ty.toKnownType!))

/--
  Convert an LExpr LMonoTy Unit to an LExpr LMonoTy Visibility
  TODO: Remove when Lambda elaborator offers parametric identifier type
-/
def ToBoogieIdent (ine: LExpr LMonoTy Unit): (LExpr LMonoTy Visibility) :=
match ine with
    | .const c ty => .const c ty
    | .op o oty => .op (BoogieIdent.unres o.name) oty
    | .bvar deBruijnIndex => .bvar deBruijnIndex
    | .fvar name oty => .fvar (BoogieIdent.unres name.name) oty
    | .mdata info e => .mdata info (ToBoogieIdent e)
    | .abs oty e => .abs oty (ToBoogieIdent e)
    | .quant k oty tr e => .quant k oty (ToBoogieIdent tr) (ToBoogieIdent e)
    | .app fn e => .app (ToBoogieIdent fn) (ToBoogieIdent e)
    | .ite c t e => .ite (ToBoogieIdent c) (ToBoogieIdent t) (ToBoogieIdent e)
    | .eq e1 e2 => .eq (ToBoogieIdent e1) (ToBoogieIdent e2)


private def BVOpNames :=
  ["Neg", "Add", "Sub", "Mul", "UDiv", "UMod", "SDiv", "SMod",
   "Not", "And", "Or", "Xor", "Shl", "UShr", "SShr",
   "ULt", "ULe", "UGt", "UGe",
   "SLt", "SLe", "SGt", "SGe"]

private def BVOpAritys :=
  ["unaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp",
   "unaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp",
   "binaryPredicate", "binaryPredicate", "binaryPredicate", "binaryPredicate",
   "binaryPredicate", "binaryPredicate", "binaryPredicate", "binaryPredicate" ]

/--
info: [("Neg", "unaryOp"), ("Add", "binaryOp"), ("Sub", "binaryOp"), ("Mul", "binaryOp"), ("UDiv", "binaryOp"),
  ("UMod", "binaryOp"), ("SDiv", "binaryOp"), ("SMod", "binaryOp"), ("Not", "unaryOp"), ("And", "binaryOp"),
  ("Or", "binaryOp"), ("Xor", "binaryOp"), ("Shl", "binaryOp"), ("UShr", "binaryOp"), ("SShr", "binaryOp"),
  ("ULt", "binaryPredicate"), ("ULe", "binaryPredicate"), ("UGt", "binaryPredicate"), ("UGe", "binaryPredicate"),
  ("SLt", "binaryPredicate"), ("SLe", "binaryPredicate"), ("SGt", "binaryPredicate"), ("SGe", "binaryPredicate")]
-/
#guard_msgs in
#eval List.zip BVOpNames BVOpAritys

open Lean Elab Command in
elab "ExpandBVOpFuncDefs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for (op, arity) in List.zip BVOpNames BVOpAritys do
      let funcName := mkIdent (.str .anonymous s!"bv{s}{op}Func")
      let funcArity := mkIdent (.str (.str .anonymous "Lambda") arity)
      let opName := Syntax.mkStrLit s!"Bv{s}.{op}"
      let bvTypeName := Name.mkSimple s!"bv{s}"
      elabCommand (← `(def $funcName : LFunc Visibility := $funcArity $opName mty[$(mkIdent bvTypeName):ident] none))

ExpandBVOpFuncDefs[1, 2, 8, 16, 32, 64]

/- Real Arithmetic Operations -/

def realAddFunc : LFunc Visibility := binaryOp "Real.Add" mty[real] none
def realSubFunc : LFunc Visibility := binaryOp "Real.Sub" mty[real] none
def realMulFunc : LFunc Visibility := binaryOp "Real.Mul" mty[real] none
def realDivFunc : LFunc Visibility := binaryOp "Real.Div" mty[real] none
def realNegFunc : LFunc Visibility := unaryOp "Real.Neg" mty[real] none

/- Real Comparison Operations -/
def realLtFunc : LFunc Visibility := binaryPredicate "Real.Lt" mty[real] none
def realLeFunc : LFunc Visibility := binaryPredicate "Real.Le" mty[real] none
def realGtFunc : LFunc Visibility := binaryPredicate "Real.Gt" mty[real] none
def realGeFunc : LFunc Visibility := binaryPredicate "Real.Ge" mty[real] none

/- String Operations -/
def strLengthFunc : LFunc Visibility :=
    { name := "Str.Length",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[int],
      concreteEval := some (unOpCeval String Int LExpr.denoteString
                            (fun s => (Int.ofNat (String.length s)))
                            mty[int])}

def strConcatFunc : LFunc Visibility :=
    { name := "Str.Concat",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[string],
      concreteEval := some (binOpCeval String String LExpr.denoteString
                            String.append mty[string])}

/- A polymorphic `old` function with type `∀a. a → a`. -/
def polyOldFunc : LFunc Visibility :=
    { name := "old",
      typeArgs := ["a"],
      inputs := [((BoogieIdent.locl "x"), mty[%a])]
      output := mty[%a]}

/- A `Map` selection function with type `∀k, v. Map k v → k → v`. -/
def mapSelectFunc : LFunc Visibility :=
   { name := "select",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])],
     output := mty[%v] }

/- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
def mapUpdateFunc : LFunc Visibility :=
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

def emptyTriggersFunc : LFunc Visibility :=
    { name := "Triggers.empty",
      typeArgs := [],
      inputs := [],
      output := mty[Triggers],
      concreteEval := none }

def addTriggerGroupFunc : LFunc Visibility :=
    { name := "Triggers.addGroup",
      typeArgs := [],
      inputs := [("g", mty[TriggerGroup]), ("t", mty[Triggers])],
      output := mty[Triggers],
      concreteEval := none }

def emptyTriggerGroupFunc : LFunc Visibility :=
    { name := "TriggerGroup.empty",
      typeArgs := [],
      inputs := [],
      output := mty[TriggerGroup],
      concreteEval := none }

def addTriggerFunc : LFunc Visibility :=
    { name := "TriggerGroup.addTrigger",
      typeArgs := ["a"],
      inputs := [("x", mty[%a]), ("t", mty[TriggerGroup])],
      output := mty[TriggerGroup],
      concreteEval := none }

open Lean in
macro "ExpandBVOpFuncNames" "[" sizes:num,* "]" : term => do
  let mut allOps := #[]
  for size in sizes.getElems do
    let s := size.getNat.repr
    let ops := BVOpNames.map (mkIdent ∘ (.str (.str .anonymous "Boogie")) ∘ (s!"bv{s}" ++ · ++ "Func"))
    allOps := allOps ++ ops.toArray
  `([$(allOps),*])

def bvConcatFunc (size : Nat) : LFunc Visibility :=
  { name := s!"Bv{size}.Concat",
    typeArgs := [],
    inputs := [("x", .bitvec size), ("y", .bitvec size)]
    output := .bitvec (size*2),
    concreteEval := none }

def bvExtractFunc (size hi lo: Nat) : LFunc Visibility :=
  { name := s!"Bv{size}.Extract_{hi}_{lo}",
    typeArgs := [],
    inputs := [("x", .bitvec size)]
    output := .bitvec (hi + 1 - lo),
    concreteEval := none }

def bv8ConcatFunc := bvConcatFunc 8
def bv16ConcatFunc := bvConcatFunc 16
def bv32ConcatFunc := bvConcatFunc 32

def bv8Extract_7_7_Func    := bvExtractFunc  8  7  7
def bv16Extract_15_15_Func := bvExtractFunc 16 15 15
def bv16Extract_7_0_Func   := bvExtractFunc 16  7  0
def bv32Extract_31_31_Func := bvExtractFunc 32 31 31
def bv32Extract_15_0_Func  := bvExtractFunc 32 15  0
def bv32Extract_7_0_Func   := bvExtractFunc 32  7  0
def bv64Extract_31_0_Func  := bvExtractFunc 64 31  0
def bv64Extract_15_0_Func  := bvExtractFunc 64 15  0
def bv64Extract_7_0_Func   := bvExtractFunc 64  7  0

def Factory : @Factory Visibility := #[
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

  emptyTriggersFunc,
  addTriggerGroupFunc,
  emptyTriggerGroupFunc,
  addTriggerFunc,

  bv8ConcatFunc,
  bv16ConcatFunc,
  bv32ConcatFunc,
  bv8Extract_7_7_Func,
  bv16Extract_15_15_Func,
  bv16Extract_7_0_Func,
  bv32Extract_31_31_Func,
  bv32Extract_15_0_Func,
  bv32Extract_7_0_Func,
  bv64Extract_31_0_Func,
  bv64Extract_15_0_Func,
  bv64Extract_7_0_Func,
] ++ ExpandBVOpFuncNames [1,8,16,32,64]

open Lean Elab Command in
elab "DefBVOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for op in BVOpNames do
      let opName := mkIdent (.str .anonymous s!"bv{s}{op}Op")
      let funcName := mkIdent (.str (.str .anonymous "Boogie") s!"bv{s}{op}Func")
      elabCommand (← `(def $opName : Expression.Expr := ($funcName).opExpr))

DefBVOpFuncExprs [1, 8, 16, 32, 64]

def bv8ConcatOp : Expression.Expr := bv8ConcatFunc.opExpr
def bv16ConcatOp : Expression.Expr := bv16ConcatFunc.opExpr
def bv32ConcatOp : Expression.Expr := bv32ConcatFunc.opExpr

def bv8Extract_7_7_Op    := bv8Extract_7_7_Func.opExpr
def bv16Extract_15_15_Op := bv16Extract_15_15_Func.opExpr
def bv16Extract_7_0_Op   := bv16Extract_7_0_Func.opExpr
def bv32Extract_31_31_Op := bv32Extract_31_31_Func.opExpr
def bv32Extract_15_0_Op  := bv32Extract_15_0_Func.opExpr
def bv32Extract_7_0_Op   := bv32Extract_7_0_Func.opExpr
def bv64Extract_31_0_Op  := bv64Extract_31_0_Func.opExpr
def bv64Extract_15_0_Op  := bv64Extract_15_0_Func.opExpr
def bv64Extract_7_0_Op   := bv64Extract_7_0_Func.opExpr

def emptyTriggersOp : Expression.Expr := emptyTriggersFunc.opExpr
def addTriggerGroupOp : Expression.Expr := addTriggerGroupFunc.opExpr
def emptyTriggerGroupOp : Expression.Expr :=  emptyTriggerGroupFunc.opExpr
def addTriggerOp : Expression.Expr := addTriggerFunc.opExpr

def intAddOp : Expression.Expr := intAddFunc.opExpr
def intSubOp : Expression.Expr := intSubFunc.opExpr
def intMulOp : Expression.Expr := intMulFunc.opExpr
def intDivOp : Expression.Expr := intDivFunc.opExpr
def intModOp : Expression.Expr := intModFunc.opExpr
def intNegOp : Expression.Expr := intNegFunc.opExpr
def intLtOp : Expression.Expr := intLtFunc.opExpr
def intLeOp : Expression.Expr := intLeFunc.opExpr
def intGtOp : Expression.Expr := intGtFunc.opExpr
def intGeOp : Expression.Expr := intGeFunc.opExpr
def realAddOp : Expression.Expr := realAddFunc.opExpr
def realSubOp : Expression.Expr := realSubFunc.opExpr
def realMulOp : Expression.Expr := realMulFunc.opExpr
def realDivOp : Expression.Expr := realDivFunc.opExpr
def realNegOp : Expression.Expr := realNegFunc.opExpr
def realLtOp : Expression.Expr := realLtFunc.opExpr
def realLeOp : Expression.Expr := realLeFunc.opExpr
def realGtOp : Expression.Expr := realGtFunc.opExpr
def realGeOp : Expression.Expr := realGeFunc.opExpr
def boolAndOp : Expression.Expr := boolAndFunc.opExpr
def boolOrOp : Expression.Expr := boolOrFunc.opExpr
def boolImpliesOp : Expression.Expr := boolImpliesFunc.opExpr
def boolEquivOp : Expression.Expr := boolEquivFunc.opExpr
def boolNotOp : Expression.Expr := boolNotFunc.opExpr
def strLengthOp : Expression.Expr := strLengthFunc.opExpr
def strConcatOp : Expression.Expr := strConcatFunc.opExpr
def polyOldOp : Expression.Expr := polyOldFunc.opExpr
def mapSelectOp : Expression.Expr := mapSelectFunc.opExpr
def mapUpdateOp : Expression.Expr := mapUpdateFunc.opExpr

def mkTriggerGroup (ts : List Expression.Expr) : Expression.Expr :=
  ts.foldl (fun g t => .app (.app addTriggerOp t) g) emptyTriggerGroupOp

def mkTriggerExpr (ts : List (List Expression.Expr)) : Expression.Expr :=
  let groups := ts.map mkTriggerGroup
  groups.foldl (fun gs g => .app (.app addTriggerGroupOp g) gs) emptyTriggersOp

end Boogie

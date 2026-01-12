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
   t[regex],
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

def TImplicit {Metadata: Type} (IDMeta: Type): LExprParamsT := ({Metadata := Metadata, IDMeta}: LExprParams).mono

/--
  Convert an LExpr LMonoTy Unit to an LExpr LMonoTy Visibility
  TODO: Remove when Lambda elaborator offers parametric identifier type
-/
def ToBoogieIdent {M: Type} (ine: LExpr (@TImplicit M Unit)): LExpr (@TImplicit M Visibility) :=
match ine with
    | .const m c => .const m c
    | .op m o oty => .op m (BoogieIdent.unres o.name) oty
    | .bvar m deBruijnIndex => .bvar m deBruijnIndex
    | .fvar m name oty => .fvar m (BoogieIdent.unres name.name) oty
    | .abs m oty e => .abs m oty (ToBoogieIdent e)
    | .quant m k oty tr e => .quant m k oty (ToBoogieIdent tr) (ToBoogieIdent e)
    | .app m fn e => .app m (ToBoogieIdent fn) (ToBoogieIdent e)
    | .ite m c t e => .ite m (ToBoogieIdent c) (ToBoogieIdent t) (ToBoogieIdent e)
    | .eq m e1 e2 => .eq m (ToBoogieIdent e1) (ToBoogieIdent e2)


private def bvBinaryOp (fn:∀ {n}, BitVec n → BitVec n → BitVec n)
  (check:∀ {n}, BitVec n → BitVec n → Bool)
  (m:BoogieLParams.Metadata)
  (ops:List (LExpr BoogieLParams.mono))
    : Option (LExpr BoogieLParams.mono) :=
  match ops with
  | [.bitvecConst _ n1 b1, .bitvecConst _ n2 b2] =>
    if h : n1 = n2 then
      if check (h ▸ b1) b2 then
        .some (.bitvecConst m n2 (fn (h ▸ b1) b2))
      else .none
    else .none
  | _ => .none

private def bvShiftOp (fn:∀ {n}, BitVec n → Nat → BitVec n)
  (m:BoogieLParams.Metadata)
  (ops:List (LExpr BoogieLParams.mono))
    : Option (LExpr BoogieLParams.mono) :=
  match ops with
  | [.bitvecConst _ n1 b1, .bitvecConst _ n2 b2] =>
    let i2 := BitVec.toNat b2
    if n1 = n2 && i2 < n1 then
      .some (.bitvecConst m n1 (fn b1 i2))
    else .none
  | _ => .none

private def bvUnaryOp (fn:∀ {n}, BitVec n → BitVec n)
  (m:BoogieLParams.Metadata)
  (ops:List (LExpr BoogieLParams.mono))
    : Option (LExpr BoogieLParams.mono) :=
  match ops with
  | [.bitvecConst _ n b] => .some (.bitvecConst m n (fn b))
  | _ => .none

private def bvBinaryPred (fn:∀ {n}, BitVec n → BitVec n → Bool)
  (swap:Bool)
  (m:BoogieLParams.Metadata)
  (ops:List (LExpr BoogieLParams.mono))
    : Option (LExpr BoogieLParams.mono) :=
  match ops with
  | [.bitvecConst _ n1 b1, .bitvecConst _ n2 b2] =>
    if h : n1 = n2 then
      let res := if swap then fn b2 (h ▸ b1) else fn (h ▸ b1) b2
      .some (.boolConst m res)
    else .none
  | _ => .none


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

private def BVOpEvals :=
  [("Neg", Option.some (bvUnaryOp BitVec.neg)),
   ("Add", .some (bvBinaryOp BitVec.add (λ_ _ => true))),
   ("Sub", .some (bvBinaryOp BitVec.sub (λ_ _ => true))),
   ("Mul", .some (bvBinaryOp BitVec.mul (λ_ _ => true))),
   ("UDiv", .some (bvBinaryOp BitVec.udiv (λ_ y => y ≠ 0))),
   ("UMod", .some (bvBinaryOp BitVec.umod (λ_ y => y ≠ 0))),
   ("SDiv", .some (bvBinaryOp BitVec.sdiv (λ_ y => y ≠ 0))),
   ("SMod", .some (bvBinaryOp BitVec.srem (λ_ y => y ≠ 0))),
   ("Not", .some (bvUnaryOp BitVec.not)),
   ("And", .some (bvBinaryOp BitVec.and (λ_ _ => true))),
   ("Or", .some (bvBinaryOp BitVec.or (λ_ _ => true))),
   ("Xor", .some (bvBinaryOp BitVec.xor (λ_ _ => true))),
   ("Shl", .some (bvShiftOp BitVec.shiftLeft)),
   ("UShr", .some (bvShiftOp BitVec.ushiftRight)),
   ("SShr", .some (bvShiftOp BitVec.sshiftRight)),
   ("ULt", .some (bvBinaryPred BitVec.ult false)),
   ("ULe", .some (bvBinaryPred BitVec.ule false)),
   ("UGt", .some (bvBinaryPred BitVec.ult true)),
   ("UGe", .some (bvBinaryPred BitVec.ule true)),
   ("SLt", .some (bvBinaryPred BitVec.slt false)),
   ("SLe", .some (bvBinaryPred BitVec.sle false)),
   ("SGt", .some (bvBinaryPred BitVec.slt true)),
   ("SGe", .some (bvBinaryPred BitVec.sle true))]

/--
info: [("Neg", "unaryOp"), ("Add", "binaryOp"), ("Sub", "binaryOp"), ("Mul", "binaryOp"), ("UDiv", "binaryOp"),
  ("UMod", "binaryOp"), ("SDiv", "binaryOp"), ("SMod", "binaryOp"), ("Not", "unaryOp"), ("And", "binaryOp"),
  ("Or", "binaryOp"), ("Xor", "binaryOp"), ("Shl", "binaryOp"), ("UShr", "binaryOp"), ("SShr", "binaryOp"),
  ("ULt", "binaryPredicate"), ("ULe", "binaryPredicate"), ("UGt", "binaryPredicate"), ("UGe", "binaryPredicate"),
  ("SLt", "binaryPredicate"), ("SLe", "binaryPredicate"), ("SGt", "binaryPredicate"), ("SGe", "binaryPredicate")]
-/
#guard_msgs in
#eval List.zip BVOpNames BVOpAritys

/--
Coercion of a string to BoogieIdent yields an unresolved identifier
This is the default setting of Strata/Languages/Boogie/Identifiers.lean
as well
-/
instance coeStringIdent: Coe String (BoogieLParams.Identifier) where
  coe | s => BoogieIdent.unres s

open Lean Elab Command in
elab "ExpandBVOpFuncDefs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for (op, arity) in List.zip BVOpNames BVOpAritys do
      let funcName := mkIdent (.str .anonymous s!"bv{s}{op}Func")
      let funcArity := mkIdent (.str (.str .anonymous "Lambda") arity)
      let opName := Syntax.mkStrLit s!"Bv{s}.{op}"
      let bvTypeName := Name.mkSimple s!"bv{s}"
      let opStr := Syntax.mkStrLit op
      elabCommand (← `(def $funcName : LFunc BoogieLParams :=
        $funcArity $opName mty[$(mkIdent bvTypeName):ident]
        ((BVOpEvals.find? (fun (k,_) => k == $opStr)).bind (fun (_,w)=>w))))

ExpandBVOpFuncDefs[1, 2, 8, 16, 32, 64]

/- Real Arithmetic Operations -/

def realAddFunc : LFunc BoogieLParams := binaryOp "Real.Add" mty[real] none
def realSubFunc : LFunc BoogieLParams := binaryOp "Real.Sub" mty[real] none
def realMulFunc : LFunc BoogieLParams := binaryOp "Real.Mul" mty[real] none
def realDivFunc : LFunc BoogieLParams := binaryOp "Real.Div" mty[real] none
def realNegFunc : LFunc BoogieLParams := unaryOp "Real.Neg" mty[real] none

/- Real Comparison Operations -/
def realLtFunc : LFunc BoogieLParams := binaryPredicate "Real.Lt" mty[real] none
def realLeFunc : LFunc BoogieLParams := binaryPredicate "Real.Le" mty[real] none
def realGtFunc : LFunc BoogieLParams := binaryPredicate "Real.Gt" mty[real] none
def realGeFunc : LFunc BoogieLParams := binaryPredicate "Real.Ge" mty[real] none

/- String Operations -/
def strLengthFunc : LFunc BoogieLParams :=
    { name := "Str.Length",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[int],
      concreteEval := some (unOpCeval (T:=BoogieLParams) String Int (.intConst (T:=BoogieLParams.mono)) (@LExpr.denoteString BoogieLParams)
                            (fun s => (Int.ofNat (String.length s))))}

def strConcatFunc : LFunc BoogieLParams :=
    { name := "Str.Concat",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[string],
      concreteEval := some (binOpCeval String String (.strConst (T := BoogieLParams.mono))
                            LExpr.denoteString String.append)}

def strSubstrFunc : LFunc BoogieLParams :=
    { name := "Str.Substr",
      typeArgs := [],
      -- longest substring of `x` of length at most `n` starting at position `i`.
      inputs := [("x", mty[string]), ("i", mty[int]), ("n", mty[int])]
      output := mty[string] }

def strToRegexFunc : LFunc BoogieLParams :=
    { name := "Str.ToRegEx",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[regex] }

def strInRegexFunc : LFunc BoogieLParams :=
    { name := "Str.InRegEx",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[regex])]
      output := mty[bool] }

def reAllCharFunc : LFunc BoogieLParams :=
    { name := "Re.AllChar",
      typeArgs := [],
      inputs := []
      output := mty[regex] }

def reAllFunc : LFunc BoogieLParams :=
    { name := "Re.All",
      typeArgs := [],
      inputs := []
      output := mty[regex] }

def reRangeFunc : LFunc BoogieLParams :=
    { name := "Re.Range",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[regex] }

def reConcatFunc : LFunc BoogieLParams :=
    { name := "Re.Concat",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("y", mty[regex])]
      output := mty[regex] }

def reStarFunc : LFunc BoogieLParams :=
    { name := "Re.Star",
      typeArgs := [],
      inputs := [("x", mty[regex])]
      output := mty[regex] }

def rePlusFunc : LFunc BoogieLParams :=
    { name := "Re.Plus",
      typeArgs := [],
      inputs := [("x", mty[regex])]
      output := mty[regex] }

def reLoopFunc : LFunc BoogieLParams :=
    { name := "Re.Loop",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("n1", mty[int]), ("n2", mty[int])]
      output := mty[regex] }

def reUnionFunc : LFunc BoogieLParams :=
    { name := "Re.Union",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("y", mty[regex])]
      output := mty[regex] }

def reInterFunc : LFunc BoogieLParams :=
    { name := "Re.Inter",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("y", mty[regex])]
      output := mty[regex] }

def reCompFunc : LFunc BoogieLParams :=
    { name := "Re.Comp",
      typeArgs := [],
      inputs := [("x", mty[regex])]
      output := mty[regex] }

def reNoneFunc : LFunc BoogieLParams :=
    { name := "Re.None",
      typeArgs := [],
      inputs := []
      output := mty[regex] }

/- A polymorphic `old` function with type `∀a. a → a`. -/
def polyOldFunc : LFunc BoogieLParams :=
    { name := "old",
      typeArgs := ["a"],
      inputs := [((BoogieIdent.locl "x"), mty[%a])]
      output := mty[%a]}

/- A `Map` selection function with type `∀k, v. Map k v → k → v`. -/
def mapSelectFunc : LFunc BoogieLParams :=
   { name := "select",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])],
     output := mty[%v] }

/- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
def mapUpdateFunc : LFunc BoogieLParams :=
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
instance : Coe String BoogieLParams.Identifier where
  coe | s => ⟨s, .unres⟩

def emptyTriggersFunc : LFunc BoogieLParams :=
    { name := "Triggers.empty",
      typeArgs := [],
      inputs := [],
      output := mty[Triggers],
      concreteEval := none }

def addTriggerGroupFunc : LFunc BoogieLParams :=
    { name := "Triggers.addGroup",
      typeArgs := [],
      inputs := [("g", mty[TriggerGroup]), ("t", mty[Triggers])],
      output := mty[Triggers],
      concreteEval := none }

def emptyTriggerGroupFunc : LFunc BoogieLParams :=
    { name := "TriggerGroup.empty",
      typeArgs := [],
      inputs := [],
      output := mty[TriggerGroup],
      concreteEval := none }

def addTriggerFunc : LFunc BoogieLParams :=
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

def bvConcatFunc (size : Nat) : LFunc BoogieLParams :=
  { name := s!"Bv{size}.Concat",
    typeArgs := [],
    inputs := [("x", .bitvec size), ("y", .bitvec size)]
    output := .bitvec (size*2),
    concreteEval := none }

def bvExtractFunc (size hi lo: Nat) : LFunc BoogieLParams :=
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

/--
Split Factorys to smaller ones for faster well-formedness proof.
In the end, we concatenate the smaller Factorys with Factory.addFactory and do
panic! check.
-/

private def intRealBoolFactory : @Factory BoogieLParams := #[
  @intAddFunc BoogieLParams _,
  @intSubFunc BoogieLParams _,
  @intMulFunc BoogieLParams _,
  @intDivFunc BoogieLParams _,
  @intModFunc BoogieLParams _,
  @intNegFunc BoogieLParams _,

  @intLtFunc BoogieLParams _,
  @intLeFunc BoogieLParams _,
  @intGtFunc BoogieLParams _,
  @intGeFunc BoogieLParams _,

  realAddFunc,
  realSubFunc,
  realMulFunc,
  realDivFunc,
  realNegFunc,
  realLtFunc,
  realLeFunc,
  realGtFunc,
  realGeFunc,

  @boolAndFunc BoogieLParams _,
  @boolOrFunc BoogieLParams _,
  @boolImpliesFunc BoogieLParams _,
  @boolEquivFunc BoogieLParams _,
  @boolNotFunc BoogieLParams _
]

/-- All operations other than Int, Real, Bool and the Bit-vector operations
(which will follow).
-/
private def nonIntRealBoolFactory : @Factory BoogieLParams := #[
  strLengthFunc,
  strConcatFunc,
  strSubstrFunc,
  strToRegexFunc,
  strInRegexFunc,
  reAllFunc,
  reAllCharFunc,
  reRangeFunc,
  reConcatFunc,
  reStarFunc,
  rePlusFunc,
  reLoopFunc,
  reUnionFunc,
  reInterFunc,
  reCompFunc,
  reNoneFunc,

  polyOldFunc,

  mapSelectFunc,
  mapUpdateFunc,

  emptyTriggersFunc,
  addTriggerGroupFunc,
  emptyTriggerGroupFunc,
  addTriggerFunc,
]

/-- Bit-vector operations of bit-width 1 and 8. -/
private def expandedBVOp_1_8_Factory : @Factory BoogieLParams := #[
  bv8ConcatFunc,
  bv8Extract_7_7_Func,
] ++ (ExpandBVOpFuncNames [1,8])

/-- Bit-vector operations of bit-width 16 -/
private def expandedBVOp_16_Factory : @Factory BoogieLParams := #[
  bv16ConcatFunc,
  bv16Extract_15_15_Func,
  bv16Extract_7_0_Func,
] ++ (ExpandBVOpFuncNames [16])

/-- Bit-vector operations of bit-width 32 -/
private def expandedBVOp_32_Factory : @Factory BoogieLParams := #[
  bv32ConcatFunc,
  bv32Extract_31_31_Func,
  bv32Extract_15_0_Func,
  bv32Extract_7_0_Func,
] ++ (ExpandBVOpFuncNames [32])

/-- Bit-vector operations of bit-width 64. -/
private def expandedBVOp_64_Factory : @Factory BoogieLParams := #[
  bv64Extract_31_0_Func,
  bv64Extract_15_0_Func,
  bv64Extract_7_0_Func,
] ++ (ExpandBVOpFuncNames [64])

def FactoryE := do
    let fv ← intRealBoolFactory.addFactory nonIntRealBoolFactory
    let fv ← fv.addFactory expandedBVOp_1_8_Factory
    let fv ← fv.addFactory expandedBVOp_16_Factory
    let fv ← fv.addFactory expandedBVOp_32_Factory
    let fv ← fv.addFactory expandedBVOp_64_Factory
    return fv

def Factory : @Factory BoogieLParams := match FactoryE with
  | .ok F => F | .error _ => panic! "may have duplicated ops"


open Lean Elab Command in
elab "DefBVOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for op in BVOpNames do
      let opName := mkIdent (.str .anonymous s!"bv{s}{op}Op")
      let funcName := mkIdent (.str (.str .anonymous "Boogie") s!"bv{s}{op}Func")
      elabCommand (← `(def $opName : Expression.Expr := ($funcName).opExpr))

instance : Inhabited BoogieLParams.Metadata where
  default := ()

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

instance : Inhabited (⟨ExpressionMetadata, BoogieIdent⟩: LExprParams).Metadata where
  default := ()

def intAddOp : Expression.Expr := (@intAddFunc BoogieLParams _).opExpr
def intSubOp : Expression.Expr := (@intSubFunc BoogieLParams _).opExpr
def intMulOp : Expression.Expr := (@intMulFunc BoogieLParams _).opExpr
def intDivOp : Expression.Expr := (@intDivFunc BoogieLParams _).opExpr
def intModOp : Expression.Expr := (@intModFunc BoogieLParams _).opExpr
def intNegOp : Expression.Expr := (@intNegFunc BoogieLParams _).opExpr
def intLtOp : Expression.Expr := (@intLtFunc BoogieLParams _).opExpr
def intLeOp : Expression.Expr := (@intLeFunc BoogieLParams _).opExpr
def intGtOp : Expression.Expr := (@intGtFunc BoogieLParams _).opExpr
def intGeOp : Expression.Expr := (@intGeFunc BoogieLParams _).opExpr
def realAddOp : Expression.Expr := realAddFunc.opExpr
def realSubOp : Expression.Expr := realSubFunc.opExpr
def realMulOp : Expression.Expr := realMulFunc.opExpr
def realDivOp : Expression.Expr := realDivFunc.opExpr
def realNegOp : Expression.Expr := realNegFunc.opExpr
def realLtOp : Expression.Expr := realLtFunc.opExpr
def realLeOp : Expression.Expr := realLeFunc.opExpr
def realGtOp : Expression.Expr := realGtFunc.opExpr
def realGeOp : Expression.Expr := realGeFunc.opExpr
def boolAndOp : Expression.Expr := (@boolAndFunc BoogieLParams _).opExpr
def boolOrOp : Expression.Expr := (@boolOrFunc BoogieLParams _).opExpr
def boolImpliesOp : Expression.Expr := (@boolImpliesFunc BoogieLParams _).opExpr
def boolEquivOp : Expression.Expr := (@boolEquivFunc BoogieLParams _).opExpr
def boolNotOp : Expression.Expr := (@boolNotFunc BoogieLParams _).opExpr
def strLengthOp : Expression.Expr := strLengthFunc.opExpr
def strConcatOp : Expression.Expr := strConcatFunc.opExpr
def strSubstrOp : Expression.Expr := strSubstrFunc.opExpr
def strToRegexOp : Expression.Expr := strToRegexFunc.opExpr
def strInRegexOp : Expression.Expr := strInRegexFunc.opExpr
def reAllOp : Expression.Expr := reAllFunc.opExpr
def reAllCharOp : Expression.Expr := reAllCharFunc.opExpr
def reRangeOp : Expression.Expr := reRangeFunc.opExpr
def reConcatOp : Expression.Expr := reConcatFunc.opExpr
def reStarOp : Expression.Expr := reStarFunc.opExpr
def rePlusOp : Expression.Expr := rePlusFunc.opExpr
def reLoopOp : Expression.Expr := reLoopFunc.opExpr
def reUnionOp : Expression.Expr := reUnionFunc.opExpr
def reInterOp : Expression.Expr := reInterFunc.opExpr
def reCompOp : Expression.Expr := reCompFunc.opExpr
def reNoneOp : Expression.Expr := reNoneFunc.opExpr
def polyOldOp : Expression.Expr := polyOldFunc.opExpr
def mapSelectOp : Expression.Expr := mapSelectFunc.opExpr
def mapUpdateOp : Expression.Expr := mapUpdateFunc.opExpr

def mkTriggerGroup (ts : List Expression.Expr) : Expression.Expr :=
  ts.foldl (fun g t => .app () (.app () addTriggerOp t) g) emptyTriggerGroupOp

def mkTriggerExpr (ts : List (List Expression.Expr)) : Expression.Expr :=
  let groups := ts.map mkTriggerGroup
  groups.foldl (fun gs g => .app () (.app () addTriggerGroupOp g) gs) emptyTriggersOp

/--
Get all the built-in functions supported by Boogie.
-/
def builtinFunctions : Array String :=
  Factory.map (fun f => BoogieIdent.toPretty f.name)


/--
Wellformedness of the factories.
-/

private theorem intRealBoolFactory_wf : FactoryWf intRealBoolFactory := by
  apply FactoryWf.mk
  · unfold intRealBoolFactory
    simp only []
    repeat(
      apply List.Pairwise.cons
      (focus ((intros a' Hmem <;>
        repeat (
          rcases Hmem with _ | ⟨ a', Hmem ⟩
          (focus (simp (config := { ground := true }); done)))) <;>
        contradiction)))
    apply List.Pairwise.nil
  · unfold intRealBoolFactory
    intros lf Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · apply LFuncWf.mk <;> try (simp (config := { ground := true }); done)
        -- Tactics below here are for unfolding fns defined in IntBoolFactory.
        try (
          simp (config := { ground := true })
          try unfold unOpCeval
          try unfold binOpCeval
          try unfold cevalIntDiv
          try unfold cevalIntMod
          intros lf md args res
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind)))
    contradiction

private theorem nonIntRealBoolFactory_wf : FactoryWf nonIntRealBoolFactory := by
  apply FactoryWf.mk
  · unfold nonIntRealBoolFactory
    simp only []
    repeat(
      apply List.Pairwise.cons
      (focus ((intros a' Hmem <;>
        repeat (
          rcases Hmem with _ | ⟨ a', Hmem ⟩
          (focus (simp (config := { ground := true }); done)))) <;>
        contradiction)))
    apply List.Pairwise.nil
  · unfold nonIntRealBoolFactory
    intros lf Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · apply LFuncWf.mk <;> try (simp (config := { ground := true }); done)
        try (
          simp (config := { ground := true })
          try unfold unOpCeval
          try unfold binOpCeval
          intros lf md args res
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind)))
    contradiction


set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem expandedBVOp_1_8_Factory_wf :
    FactoryWf expandedBVOp_1_8_Factory := by
  unfold expandedBVOp_1_8_Factory
  apply FactoryWf.mk
  · rw [Array.toList_appendList]
    simp only []
    unfold HAppend.hAppend instHAppendOfAppend Append.append List.instAppend
    simp only [List.append]
    repeat (
      apply List.Pairwise.cons
      (focus ((intros a' Hmem <;>
        repeat (
          rcases Hmem with _ | ⟨ a', Hmem ⟩
          (focus (simp (config := { ground := true }); done)))) <;>
        contradiction)))
    apply List.Pairwise.nil
  · unfold HAppend.hAppend Array.instHAppendList
    simp only []
    unfold Array.appendList
    simp only [List.foldl, Array.push, List.concat]
    intros lf
    rw [← Array.mem_toList_iff]
    simp only []
    intros Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · apply LFuncWf.mk <;> try (simp (config := { ground := true }); done)
        try (
          simp (config := { ground := true })
          try unfold bvUnaryOp
          try unfold bvBinaryOp
          try unfold bvShiftOp
          try unfold bvBinaryPred
          intros lf md args res
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind)))
    contradiction

private theorem expandedBVOp_16_Factory_wf :
    FactoryWf expandedBVOp_16_Factory := by
  unfold expandedBVOp_16_Factory
  apply FactoryWf.mk
  · rw [Array.toList_appendList]
    simp only []
    unfold HAppend.hAppend instHAppendOfAppend Append.append List.instAppend
    simp only [List.append]
    repeat (
      apply List.Pairwise.cons
      (focus ((intros a' Hmem <;>
        repeat (
          rcases Hmem with _ | ⟨ a', Hmem ⟩
          (focus (simp (config := { ground := true }); done)))) <;>
        contradiction)))
    apply List.Pairwise.nil
  · unfold HAppend.hAppend Array.instHAppendList
    simp only []
    unfold Array.appendList
    simp only [List.foldl, Array.push, List.concat]
    intros lf
    rw [← Array.mem_toList_iff]
    simp only []
    intros Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · apply LFuncWf.mk <;> try (simp (config := { ground := true }); done)
        try (
          simp (config := { ground := true })
          try unfold bvUnaryOp
          try unfold bvBinaryOp
          try unfold bvShiftOp
          try unfold bvBinaryPred
          intros lf md args res
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind)))
    contradiction

private theorem expandedBVOp_32_Factory_wf :
    FactoryWf expandedBVOp_32_Factory := by
  unfold expandedBVOp_32_Factory
  apply FactoryWf.mk
  · rw [Array.toList_appendList]
    simp only []
    unfold HAppend.hAppend instHAppendOfAppend Append.append List.instAppend
    simp only [List.append]
    repeat (
      apply List.Pairwise.cons
      (focus ((intros a' Hmem <;>
        repeat (
          rcases Hmem with _ | ⟨ a', Hmem ⟩
          (focus (simp (config := { ground := true }); done)))) <;>
        contradiction)))
    apply List.Pairwise.nil
  · unfold HAppend.hAppend Array.instHAppendList
    simp only []
    unfold Array.appendList
    simp only [List.foldl, Array.push, List.concat]
    intros lf
    rw [← Array.mem_toList_iff]
    simp only []
    intros Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · apply LFuncWf.mk <;> try (simp (config := { ground := true }); done)
        try (
          simp (config := { ground := true })
          try unfold bvUnaryOp
          try unfold bvBinaryOp
          try unfold bvShiftOp
          try unfold bvBinaryPred
          intros lf md args res
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind)))
    contradiction

private theorem expandedBVOp_64_Factory_wf :
    FactoryWf expandedBVOp_64_Factory := by
  unfold expandedBVOp_64_Factory
  apply FactoryWf.mk
  · rw [Array.toList_appendList]
    simp only []
    unfold HAppend.hAppend instHAppendOfAppend Append.append List.instAppend
    simp only [List.append]
    repeat (
      apply List.Pairwise.cons
      (focus ((intros a' Hmem <;>
        repeat (
          rcases Hmem with _ | ⟨ a', Hmem ⟩
          (focus (simp (config := { ground := true }); done)))) <;>
        contradiction)))
    apply List.Pairwise.nil
  · unfold HAppend.hAppend Array.instHAppendList
    simp only []
    unfold Array.appendList
    simp only [List.foldl, Array.push, List.concat]
    intros lf
    rw [← Array.mem_toList_iff]
    simp only []
    intros Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · apply LFuncWf.mk <;> try (simp (config := { ground := true }); done)
        try (
          simp (config := { ground := true })
          try unfold bvUnaryOp
          try unfold bvBinaryOp
          try unfold bvShiftOp
          try unfold bvBinaryPred
          intros lf md args res
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind)))
    contradiction

def Factory_wf_if_ok: ∀ F', FactoryE = .ok F' → FactoryWf F' := by
  -- Challenge: it seems this theorem can be possibly automated with
  -- a decision procedure for first order logic. Can we use grind?
  intros F'
  unfold FactoryE Bind.bind Pure.pure Except.instMonad Except.bind
  simp only []
  intro H
  split at H <;> try contradiction
  rename_i F1 HF1
  split at H <;> try contradiction
  rename_i F2 HF2
  split at H <;> try contradiction
  rename_i F3 HF3
  split at H <;> try contradiction
  rename_i F4 HF4
  split at H <;> try contradiction
  rename_i F5 HF5
  have Hwf1:= Factory.addFactory_wf intRealBoolFactory intRealBoolFactory_wf
      nonIntRealBoolFactory nonIntRealBoolFactory_wf F1 HF1
  have Hwf2:= Factory.addFactory_wf F1 Hwf1
      expandedBVOp_1_8_Factory expandedBVOp_1_8_Factory_wf F2 HF2
  have Hwf3:= Factory.addFactory_wf F2 Hwf2
      expandedBVOp_16_Factory expandedBVOp_16_Factory_wf F3 HF3
  have Hwf4:= Factory.addFactory_wf F3 Hwf3
      expandedBVOp_32_Factory expandedBVOp_32_Factory_wf F4 HF4
  have Hwf5:= Factory.addFactory_wf F4 Hwf4
      expandedBVOp_64_Factory expandedBVOp_64_Factory_wf F5 HF5
  unfold Except.pure at H
  grind

/-
Currently, this theorem cannot be proven true because the existing proof for
smaller factories raises timeout/heartbeat error if applied this larger Factory.
But we are pretty close: Factory_wf_if_ok is proven, and evaluting Factory
must have raised 'panic!' if it was not ok, so from the fact that it did not
panic! the resulting Factory is well-formed.
-/

/-
def Factory_wf: FactoryWf Factory := by
  sorry
-/

end Boogie

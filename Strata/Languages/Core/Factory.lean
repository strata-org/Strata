/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Elab.Command

import Strata.Languages.Core.Identifiers
import Strata.Languages.Core.Expressions
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.FactoryWF
import Strata.DL.Lambda.IntBoolFactory
---------------------------------------------------------------------

namespace Core
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
def ToCoreIdent {M: Type} (ine: LExpr (@TImplicit M Unit)): LExpr (@TImplicit M Visibility) :=
match ine with
    | .const m c => .const m c
    | .op m o oty => .op m (CoreIdent.unres o.name) oty
    | .bvar m deBruijnIndex => .bvar m deBruijnIndex
    | .fvar m name oty => .fvar m (CoreIdent.unres name.name) oty
    | .abs m oty e => .abs m oty (ToCoreIdent e)
    | .quant m k oty tr e => .quant m k oty (ToCoreIdent tr) (ToCoreIdent e)
    | .app m fn e => .app m (ToCoreIdent fn) (ToCoreIdent e)
    | .ite m c t e => .ite m (ToCoreIdent c) (ToCoreIdent t) (ToCoreIdent e)
    | .eq m e1 e2 => .eq m (ToCoreIdent e1) (ToCoreIdent e2)


def bvBinaryOp (fn:∀ {n}, BitVec n → BitVec n → BitVec n)
  (check:∀ {n}, BitVec n → BitVec n → Bool)
  (m:CoreLParams.Metadata)
  (ops:List (LExpr CoreLParams.mono))
    : Option (LExpr CoreLParams.mono) :=
  match ops with
  | [.bitvecConst _ n1 b1, .bitvecConst _ n2 b2] =>
    if h : n1 = n2 then
      if check (h ▸ b1) b2 then
        .some (.bitvecConst m n2 (fn (h ▸ b1) b2))
      else .none
    else .none
  | _ => .none

def bvShiftOp (fn:∀ {n}, BitVec n → Nat → BitVec n)
  (m:CoreLParams.Metadata)
  (ops:List (LExpr CoreLParams.mono))
    : Option (LExpr CoreLParams.mono) :=
  match ops with
  | [.bitvecConst _ n1 b1, .bitvecConst _ n2 b2] =>
    let i2 := BitVec.toNat b2
    if n1 = n2 && i2 < n1 then
      .some (.bitvecConst m n1 (fn b1 i2))
    else .none
  | _ => .none

def bvUnaryOp (fn:∀ {n}, BitVec n → BitVec n)
  (m:CoreLParams.Metadata)
  (ops:List (LExpr CoreLParams.mono))
    : Option (LExpr CoreLParams.mono) :=
  match ops with
  | [.bitvecConst _ n b] => .some (.bitvecConst m n (fn b))
  | _ => .none

def bvBinaryPred (fn:∀ {n}, BitVec n → BitVec n → Bool)
  (swap:Bool)
  (m:CoreLParams.Metadata)
  (ops:List (LExpr CoreLParams.mono))
    : Option (LExpr CoreLParams.mono) :=
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

/--
info: [("Neg", "unaryOp"), ("Add", "binaryOp"), ("Sub", "binaryOp"), ("Mul", "binaryOp"), ("UDiv", "binaryOp"),
  ("UMod", "binaryOp"), ("SDiv", "binaryOp"), ("SMod", "binaryOp"), ("Not", "unaryOp"), ("And", "binaryOp"),
  ("Or", "binaryOp"), ("Xor", "binaryOp"), ("Shl", "binaryOp"), ("UShr", "binaryOp"), ("SShr", "binaryOp"),
  ("ULt", "binaryPredicate"), ("ULe", "binaryPredicate"), ("UGt", "binaryPredicate"), ("UGe", "binaryPredicate"),
  ("SLt", "binaryPredicate"), ("SLe", "binaryPredicate"), ("SGt", "binaryPredicate"), ("SGe", "binaryPredicate")]
-/
#guard_msgs in
#eval List.zip BVOpNames BVOpAritys

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
      elabCommand (← `(def $funcName : LFunc CoreLParams :=
        $funcArity $opName mty[$(mkIdent bvTypeName):ident]
        ((BVOpEvals.find? (fun (k,_) => k == $opStr)).bind (fun (_,w)=>w))))

ExpandBVOpFuncDefs[1, 2, 8, 16, 32, 64]

/- Real Arithmetic Operations -/

def realAddFunc : LFunc CoreLParams := binaryOp "Real.Add" mty[real] none
def realSubFunc : LFunc CoreLParams := binaryOp "Real.Sub" mty[real] none
def realMulFunc : LFunc CoreLParams := binaryOp "Real.Mul" mty[real] none
def realDivFunc : LFunc CoreLParams := binaryOp "Real.Div" mty[real] none
def realNegFunc : LFunc CoreLParams := unaryOp "Real.Neg" mty[real] none

/- Real Comparison Operations -/
def realLtFunc : LFunc CoreLParams := binaryPredicate "Real.Lt" mty[real] none
def realLeFunc : LFunc CoreLParams := binaryPredicate "Real.Le" mty[real] none
def realGtFunc : LFunc CoreLParams := binaryPredicate "Real.Gt" mty[real] none
def realGeFunc : LFunc CoreLParams := binaryPredicate "Real.Ge" mty[real] none

/- String Operations -/
def strLengthFunc : LFunc CoreLParams :=
    { name := "Str.Length",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[int],
      concreteEval := some (unOpCeval (T:=CoreLParams) String Int (.intConst (T:=CoreLParams.mono)) (@LExpr.denoteString CoreLParams)
                            (fun s => (Int.ofNat (String.length s))))}

def strConcatFunc : LFunc CoreLParams :=
    { name := "Str.Concat",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[string],
      concreteEval := some (binOpCeval String String (.strConst (T := CoreLParams.mono))
                            LExpr.denoteString String.append)}

def strSubstrFunc : LFunc CoreLParams :=
    { name := "Str.Substr",
      typeArgs := [],
      -- longest substring of `x` of length at most `n` starting at position `i`.
      inputs := [("x", mty[string]), ("i", mty[int]), ("n", mty[int])]
      output := mty[string] }

def strToRegexFunc : LFunc CoreLParams :=
    { name := "Str.ToRegEx",
      typeArgs := [],
      inputs := [("x", mty[string])]
      output := mty[regex] }

def strInRegexFunc : LFunc CoreLParams :=
    { name := "Str.InRegEx",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[regex])]
      output := mty[bool] }

def reAllCharFunc : LFunc CoreLParams :=
    { name := "Re.AllChar",
      typeArgs := [],
      inputs := []
      output := mty[regex] }

def reAllFunc : LFunc CoreLParams :=
    { name := "Re.All",
      typeArgs := [],
      inputs := []
      output := mty[regex] }

def reRangeFunc : LFunc CoreLParams :=
    { name := "Re.Range",
      typeArgs := [],
      inputs := [("x", mty[string]), ("y", mty[string])]
      output := mty[regex] }

def reConcatFunc : LFunc CoreLParams :=
    { name := "Re.Concat",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("y", mty[regex])]
      output := mty[regex] }

def reStarFunc : LFunc CoreLParams :=
    { name := "Re.Star",
      typeArgs := [],
      inputs := [("x", mty[regex])]
      output := mty[regex] }

def rePlusFunc : LFunc CoreLParams :=
    { name := "Re.Plus",
      typeArgs := [],
      inputs := [("x", mty[regex])]
      output := mty[regex] }

def reLoopFunc : LFunc CoreLParams :=
    { name := "Re.Loop",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("n1", mty[int]), ("n2", mty[int])]
      output := mty[regex] }

def reUnionFunc : LFunc CoreLParams :=
    { name := "Re.Union",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("y", mty[regex])]
      output := mty[regex] }

def reInterFunc : LFunc CoreLParams :=
    { name := "Re.Inter",
      typeArgs := [],
      inputs := [("x", mty[regex]), ("y", mty[regex])]
      output := mty[regex] }

def reCompFunc : LFunc CoreLParams :=
    { name := "Re.Comp",
      typeArgs := [],
      inputs := [("x", mty[regex])]
      output := mty[regex] }

def reNoneFunc : LFunc CoreLParams :=
    { name := "Re.None",
      typeArgs := [],
      inputs := []
      output := mty[regex] }

/- A polymorphic `old` function with type `∀a. a → a`. -/
def polyOldFunc : LFunc CoreLParams :=
    { name := "old",
      typeArgs := ["a"],
      inputs := [((CoreIdent.locl "x"), mty[%a])]
      output := mty[%a]}

/- A `Map` selection function with type `∀k, v. Map k v → k → v`. -/
def mapSelectFunc : LFunc CoreLParams :=
   { name := "select",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])],
     output := mty[%v] }

/- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
def mapUpdateFunc : LFunc CoreLParams :=
   { name := "update",
     typeArgs := ["k", "v"],
     inputs := [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k]), ("x", mty[%v])],
     output := mapTy mty[%k] mty[%v],
     axioms :=
     [
      -- updateSelect: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv
      ToCoreIdent esM[∀(Map %k %v):
          (∀ (%k):
            (∀ (%v):{
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1)}
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1) == %0))],
      -- updatePreserve: forall m: Map k v, okk: k, kk: k, vv: v :: okk != kk ==> m[kk := vv][okk] == m[okk]
      ToCoreIdent esM[∀ (Map %k %v): -- %3 m
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

def emptyTriggersFunc : LFunc CoreLParams :=
    { name := "Triggers.empty",
      typeArgs := [],
      inputs := [],
      output := mty[Triggers],
      concreteEval := none }

def addTriggerGroupFunc : LFunc CoreLParams :=
    { name := "Triggers.addGroup",
      typeArgs := [],
      inputs := [("g", mty[TriggerGroup]), ("t", mty[Triggers])],
      output := mty[Triggers],
      concreteEval := none }

def emptyTriggerGroupFunc : LFunc CoreLParams :=
    { name := "TriggerGroup.empty",
      typeArgs := [],
      inputs := [],
      output := mty[TriggerGroup],
      concreteEval := none }

def addTriggerFunc : LFunc CoreLParams :=
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
    let ops := BVOpNames.map (mkIdent ∘ (.str (.str .anonymous "Core")) ∘ (s!"bv{s}" ++ · ++ "Func"))
    allOps := allOps ++ ops.toArray
  `([$(allOps),*])

def bvConcatFunc (size : Nat) : LFunc CoreLParams :=
  { name := s!"Bv{size}.Concat",
    typeArgs := [],
    inputs := [("x", .bitvec size), ("y", .bitvec size)]
    output := .bitvec (size*2),
    concreteEval := none }

def bvExtractFunc (size hi lo: Nat) : LFunc CoreLParams :=
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

def Factory : @Factory CoreLParams := #[
  @intAddFunc CoreLParams _,
  @intSubFunc CoreLParams _,
  @intMulFunc CoreLParams _,
  @intDivFunc CoreLParams _,
  @intModFunc CoreLParams _,
  @intNegFunc CoreLParams _,

  @intLtFunc CoreLParams _,
  @intLeFunc CoreLParams _,
  @intGtFunc CoreLParams _,
  @intGeFunc CoreLParams _,

  realAddFunc,
  realSubFunc,
  realMulFunc,
  realDivFunc,
  realNegFunc,
  realLtFunc,
  realLeFunc,
  realGtFunc,
  realGeFunc,

  @boolAndFunc CoreLParams _,
  @boolOrFunc CoreLParams _,
  @boolImpliesFunc CoreLParams _,
  @boolEquivFunc CoreLParams _,
  @boolNotFunc CoreLParams _,

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
] ++ (ExpandBVOpFuncNames [1,8,16,32,64])

open Lean Elab Command in
elab "DefBVOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for op in BVOpNames do
      let opName := mkIdent (.str .anonymous s!"bv{s}{op}Op")
      let funcName := mkIdent (.str (.str .anonymous "Core") s!"bv{s}{op}Func")
      elabCommand (← `(def $opName : Expression.Expr := ($funcName).opExpr))

instance : Inhabited CoreLParams.Metadata where
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

instance : Inhabited (⟨ExpressionMetadata, CoreIdent⟩: LExprParams).Metadata where
  default := ()

def intAddOp : Expression.Expr := (@intAddFunc CoreLParams _).opExpr
def intSubOp : Expression.Expr := (@intSubFunc CoreLParams _).opExpr
def intMulOp : Expression.Expr := (@intMulFunc CoreLParams _).opExpr
def intDivOp : Expression.Expr := (@intDivFunc CoreLParams _).opExpr
def intModOp : Expression.Expr := (@intModFunc CoreLParams _).opExpr
def intNegOp : Expression.Expr := (@intNegFunc CoreLParams _).opExpr
def intLtOp : Expression.Expr := (@intLtFunc CoreLParams _).opExpr
def intLeOp : Expression.Expr := (@intLeFunc CoreLParams _).opExpr
def intGtOp : Expression.Expr := (@intGtFunc CoreLParams _).opExpr
def intGeOp : Expression.Expr := (@intGeFunc CoreLParams _).opExpr
def realAddOp : Expression.Expr := realAddFunc.opExpr
def realSubOp : Expression.Expr := realSubFunc.opExpr
def realMulOp : Expression.Expr := realMulFunc.opExpr
def realDivOp : Expression.Expr := realDivFunc.opExpr
def realNegOp : Expression.Expr := realNegFunc.opExpr
def realLtOp : Expression.Expr := realLtFunc.opExpr
def realLeOp : Expression.Expr := realLeFunc.opExpr
def realGtOp : Expression.Expr := realGtFunc.opExpr
def realGeOp : Expression.Expr := realGeFunc.opExpr
def boolAndOp : Expression.Expr := (@boolAndFunc CoreLParams _).opExpr
def boolOrOp : Expression.Expr := (@boolOrFunc CoreLParams _).opExpr
def boolImpliesOp : Expression.Expr := (@boolImpliesFunc CoreLParams _).opExpr
def boolEquivOp : Expression.Expr := (@boolEquivFunc CoreLParams _).opExpr
def boolNotOp : Expression.Expr := (@boolNotFunc CoreLParams _).opExpr
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
Get all the built-in functions supported by Strata Core.
-/
def builtinFunctions : Array String :=
  Factory.map (fun f => CoreIdent.toPretty f.name)

end Core

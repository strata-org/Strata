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


/-- Kind of bitvector evaluator, used to generate both the combinator name
    and the concrete-evaluator syntax for each BV operation. -/
private inductive BVEvalKind
  /-- Unary: `unaryOp fn` -/
  | unary (fn : Lean.Name)
  /-- Binary: `binaryOp fn` or `binaryOp fn (· != 0)` -/
  | binary (fn : Lean.Name) (divGuard : Bool)
  /-- Shift: `binaryOp` with toNat conversion and size guard -/
  | shift (fn : Lean.Name)
  /-- Predicate: `binaryOp fn` -/
  | pred (fn : Lean.Name) (swap : Bool)

/-- Specification of a single bitvector operation for metaprogramming. -/
private structure BVOpSpec where
  opName : String
  evalKind : BVEvalKind

/-- All bitvector operations, in canonical order.
    This is the single source of truth: `ExpandBVOpFuncDefs`,
    `ExpandBVOpFuncNames`, and `DefBVOpFuncExprs` all derive from it. -/
private def BVOpSpecs : Array BVOpSpec := #[
  -- Unary
  ⟨"Neg", .unary ``BitVec.neg⟩,
  -- Binary arithmetic
  ⟨"Add",  .binary ``BitVec.add  false⟩,
  ⟨"Sub",  .binary ``BitVec.sub  false⟩,
  ⟨"Mul",  .binary ``BitVec.mul  false⟩,
  ⟨"UDiv", .binary ``BitVec.udiv true⟩,
  ⟨"UMod", .binary ``BitVec.umod true⟩,
  ⟨"SDiv", .binary ``BitVec.sdiv true⟩,
  ⟨"SMod", .binary ``BitVec.srem true⟩,
  -- Unary bitwise
  ⟨"Not", .unary ``BitVec.not⟩,
  -- Binary bitwise
  ⟨"And", .binary ``BitVec.and false⟩,
  ⟨"Or",  .binary ``BitVec.or  false⟩,
  ⟨"Xor", .binary ``BitVec.xor false⟩,
  -- Shifts
  ⟨"Shl",  .shift ``BitVec.shiftLeft⟩,
  ⟨"UShr", .shift ``BitVec.ushiftRight⟩,
  ⟨"SShr", .shift ``BitVec.sshiftRight⟩,
  -- Predicates
  ⟨"ULt", .pred ``BitVec.ult false⟩,
  ⟨"ULe", .pred ``BitVec.ule false⟩,
  ⟨"UGt", .pred ``BitVec.ult true⟩,
  ⟨"UGe", .pred ``BitVec.ule true⟩,
  ⟨"SLt", .pred ``BitVec.slt false⟩,
  ⟨"SLe", .pred ``BitVec.sle false⟩,
  ⟨"SGt", .pred ``BitVec.slt true⟩,
  ⟨"SGe", .pred ``BitVec.sle true⟩
]

open Lean Elab Command in
/-- Generate the full definition RHS for a BV operation.
    Uses typeclass-based combinators for all operation kinds. -/
private def BVEvalKind.toDefRHS (opName : TSyntax `str)
    (sizeNum : TSyntax `num)
    : BVEvalKind → CommandElabM (TSyntax `term)
  | .unary fn =>
    `(Lambda.unaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent fn))
  | .binary fn false =>
    `(Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent fn))
  | .binary fn true =>
    `(Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent fn) (· != 0))
  | .shift fn =>
    `(Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName
      (fun b1 b2 => $(mkIdent fn) b1 b2.toNat)
      (fun b => decide (b.toNat < $sizeNum)))
  | .pred fn false =>
    `(Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent fn))
  | .pred fn true =>
    `(Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName (fun x y => $(mkIdent fn) y x))

open Lean Elab Command in
elab "ExpandBVOpFuncDefs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    let sizeNum := Syntax.mkNumLit s
    for spec in BVOpSpecs do
      let funcName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Func")
      let opName := Syntax.mkStrLit s!"Bv{s}.{spec.opName}"
      let rhs ← spec.evalKind.toDefRHS opName sizeNum
      elabCommand (← `(def $funcName : Lambda.WFLFunc CoreLParams := $rhs))

ExpandBVOpFuncDefs[1, 2, 8, 16, 32, 64]

/- Real Arithmetic Operations -/

def realAddFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Add" mty[real] mty[real] mty[real]
def realSubFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Sub" mty[real] mty[real] mty[real]
def realMulFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Mul" mty[real] mty[real] mty[real]
def realDivFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Div" mty[real] mty[real] mty[real]
def realNegFunc : WFLFunc CoreLParams :=
  unaryFuncUneval "Real.Neg" mty[real] mty[real]

/- Real Comparison Operations -/

def realLtFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Lt" mty[real] mty[real] mty[bool]
def realLeFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Le" mty[real] mty[real] mty[bool]
def realGtFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Gt" mty[real] mty[real] mty[bool]
def realGeFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Real.Ge" mty[real] mty[real] mty[bool]

/- String Operations -/
def strLengthFunc : WFLFunc CoreLParams :=
  unaryOp "Str.Length" (fun (s : String) => Int.ofNat s.length)

def strConcatFunc : WFLFunc CoreLParams :=
  binaryOp "Str.Concat" String.append

def strSubstrFunc : WFLFunc CoreLParams :=
  polyUneval "Str.Substr" []
    [("x", mty[string]), ("i", mty[int]), ("n", mty[int])] mty[string]

def strToRegexFunc : WFLFunc CoreLParams :=
  unaryFuncUneval "Str.ToRegEx" mty[string] mty[regex]

def strInRegexFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Str.InRegEx" mty[string] mty[regex] mty[bool]

def reAllCharFunc : WFLFunc CoreLParams :=
  nullaryUneval "Re.AllChar" mty[regex]

def reAllFunc : WFLFunc CoreLParams :=
  nullaryUneval "Re.All" mty[regex]

def reRangeFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Re.Range" mty[string] mty[string] mty[regex]

def reConcatFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Re.Concat" mty[regex] mty[regex] mty[regex]

def reStarFunc : WFLFunc CoreLParams :=
  unaryFuncUneval "Re.Star" mty[regex] mty[regex]

def rePlusFunc : WFLFunc CoreLParams :=
  unaryFuncUneval "Re.Plus" mty[regex] mty[regex]

def reLoopFunc : WFLFunc CoreLParams :=
  polyUneval "Re.Loop" []
    [("x", mty[regex]), ("n1", mty[int]), ("n2", mty[int])] mty[regex]

def reUnionFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Re.Union" mty[regex] mty[regex] mty[regex]

def reInterFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Re.Inter" mty[regex] mty[regex] mty[regex]

def reCompFunc : WFLFunc CoreLParams :=
  unaryFuncUneval "Re.Comp" mty[regex] mty[regex]

def reNoneFunc : WFLFunc CoreLParams :=
  nullaryUneval "Re.None" mty[regex]

/- A polymorphic `old` function with type `∀a. a → a`. -/
def polyOldFunc : WFLFunc CoreLParams :=
  polyUneval "old" ["a"] [("x", mty[%a])] mty[%a]

/- A `Map` selection function with type `∀k, v. Map k v → k → v`. -/
def mapSelectFunc : WFLFunc CoreLParams :=
  polyUneval "select" ["k", "v"]
    [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])] mty[%v]

/- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
def mapUpdateFunc : WFLFunc CoreLParams :=
  polyUneval "update" ["k", "v"]
    [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k]), ("x", mty[%v])]
    (mapTy mty[%k] mty[%v])
    (axioms := [
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
    ])

def emptyTriggersFunc : WFLFunc CoreLParams :=
  nullaryUneval "Triggers.empty" mty[Triggers]

def addTriggerGroupFunc : WFLFunc CoreLParams :=
  polyUneval "Triggers.addGroup" []
    [("g", mty[TriggerGroup]), ("t", mty[Triggers])] mty[Triggers]

def emptyTriggerGroupFunc : WFLFunc CoreLParams :=
  nullaryUneval "TriggerGroup.empty" mty[TriggerGroup]

def addTriggerFunc : WFLFunc CoreLParams :=
  polyUneval "TriggerGroup.addTrigger" ["a"]
    [("x", mty[%a]), ("t", mty[TriggerGroup])] mty[TriggerGroup]

open Lean in
macro "ExpandBVOpFuncNames" "[" sizes:num,* "]" : term => do
  let mut allOps := #[]
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVOpSpecs do
      let name := s!"bv{s}" ++ spec.opName ++ "Func"
      allOps := allOps.push (mkIdent (.str (.str .anonymous "Core") name))
  `([$(allOps),*])

def bvConcatFunc (size : Nat) : WFLFunc CoreLParams :=
  binaryFuncUneval s!"Bv{size}.Concat"
    (.bitvec size) (.bitvec size) (.bitvec (size * 2)) rfl rfl rfl

def bvExtractFunc (size hi lo : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Bv{size}.Extract_{hi}_{lo}"
    (.bitvec size) (.bitvec (hi + 1 - lo)) rfl rfl

def bv8ConcatFunc  := bvConcatFunc 8
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

def WFFactory : Lambda.WFLFactory CoreLParams :=
  -- (T := CoreLParams) annotations needed for IntBoolFactory
  -- functions to resolve typeclass instances.
  WFLFactory.ofArray (name_nodup := by native_decide) (#[
  intAddFunc (T := CoreLParams),
  intSubFunc (T := CoreLParams),
  intMulFunc (T := CoreLParams),
  intDivFunc (T := CoreLParams),
  intSafeDivFunc (T := CoreLParams),
  intModFunc (T := CoreLParams),
  intSafeModFunc (T := CoreLParams),
  intDivTFunc (T := CoreLParams),
  intModTFunc (T := CoreLParams),
  intNegFunc (T := CoreLParams),

  intLtFunc (T := CoreLParams),
  intLeFunc (T := CoreLParams),
  intGtFunc (T := CoreLParams),
  intGeFunc (T := CoreLParams),

  realAddFunc,
  realSubFunc,
  realMulFunc,
  realDivFunc,
  realNegFunc,
  realLtFunc,
  realLeFunc,
  realGtFunc,
  realGeFunc,

  boolAndFunc (T := CoreLParams),
  boolOrFunc (T := CoreLParams),
  boolImpliesFunc (T := CoreLParams),
  boolEquivFunc (T := CoreLParams),
  boolNotFunc (T := CoreLParams),

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
] ++ (ExpandBVOpFuncNames [1,8,16,32,64]))

def Factory : @Factory CoreLParams := WFLFactory.toFactory WFFactory

open Lean Elab Command in
elab "DefBVOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVOpSpecs do
      let opName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Op")
      let funcName := mkIdent (.str (.str .anonymous "Core") s!"bv{s}{spec.opName}Func")
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
def emptyTriggerGroupOp : Expression.Expr := emptyTriggerGroupFunc.opExpr
def addTriggerOp : Expression.Expr := addTriggerFunc.opExpr

instance : Inhabited (⟨ExpressionMetadata, CoreIdent⟩: LExprParams).Metadata where
  default := ()

def intAddOp : Expression.Expr := (@intAddFunc CoreLParams _).opExpr
def intSubOp : Expression.Expr := (@intSubFunc CoreLParams _).opExpr
def intMulOp : Expression.Expr := (@intMulFunc CoreLParams _).opExpr
def intDivOp : Expression.Expr := (@intDivFunc CoreLParams _).opExpr
def intSafeDivOp : Expression.Expr := (@intSafeDivFunc CoreLParams _ _).opExpr
def intModOp : Expression.Expr := (@intModFunc CoreLParams _).opExpr
def intSafeModOp : Expression.Expr := (@intSafeModFunc CoreLParams _ _).opExpr
def intDivTOp : Expression.Expr := (@intDivTFunc CoreLParams _).opExpr
def intModTOp : Expression.Expr := (@intModTFunc CoreLParams _).opExpr
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

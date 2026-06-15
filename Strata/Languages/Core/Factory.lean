/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command

public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
import Strata.DL.Util.BitVec
public meta import Strata.DL.Lambda.IntBoolFactory
---------------------------------------------------------------------

namespace Core
open Lambda LTy.Syntax LExpr.SyntaxMono

public section

@[expose, match_pattern]
def mapTy (keyTy : LMonoTy) (valTy : LMonoTy) : LMonoTy :=
  .tcons "Map" [keyTy, valTy]

@[expose, match_pattern]
def seqTy (elemTy : LMonoTy) : LMonoTy :=
  .tcons "Sequence" [elemTy]

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
   t[∀a b. Map %a %b],
   t[∀a. Sequence %a]]

def KnownTypes : KnownTypes :=
  makeKnownTypes (KnownLTys.map (fun ty => ty.toKnownType!))

def TImplicit {Metadata: Type} (IDMeta: Type): LExprParamsT := ({Metadata := Metadata, IDMeta}: LExprParams).mono

end -- public section

public meta section

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
  /-- Binary overflow predicate: `binaryOp fn` returning bool -/
  | overflowBinary (fn : Lean.Name)
  /-- Unary overflow predicate: `unaryOp fn` returning bool -/
  | overflowUnary (fn : Lean.Name)

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
  ⟨"SGe", .pred ``BitVec.sle true⟩,
  -- Signed overflow predicates (return bool: true iff overflow occurs)
  ⟨"SNegOverflow",  .overflowUnary ``BitVec.negOverflow⟩,
  ⟨"SAddOverflow",  .overflowBinary ``BitVec.saddOverflow⟩,
  ⟨"SSubOverflow",  .overflowBinary ``BitVec.ssubOverflow⟩,
  ⟨"SMulOverflow",  .overflowBinary ``BitVec.smulOverflow⟩,
  -- Signed division overflow predicate: true iff x == INT_MIN ∧ y == -1
  ⟨"SDivOverflow",  .overflowBinary ``BitVec.sdivOverflow⟩,
  -- Unsigned overflow predicates
  ⟨"UNegOverflow",  .overflowUnary ``BitVec.unegOverflow⟩,
  ⟨"UAddOverflow",  .overflowBinary ``BitVec.uaddOverflow⟩,
  ⟨"USubOverflow",  .overflowBinary ``BitVec.usubOverflow⟩,
  ⟨"UMulOverflow",  .overflowBinary ``BitVec.umulOverflow⟩
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
  | .overflowBinary fn =>
    `(Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent fn))
  | .overflowUnary fn =>
    `(Lambda.unaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent fn))

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

/-- Specification of a safe (preconditioned) bitvector operation. -/
private structure BVSafeOpSpec where
  opName : String
  /-- The underlying operation function (e.g., BitVec.add) -/
  opFn : Lean.Name
  /-- The overflow predicate function name suffix (e.g., "SAddOverflow") -/
  overflowPredSuffix : String
  /-- Whether this is a unary operation -/
  isUnary : Bool := false

private def BVSafeOpSpecs : Array BVSafeOpSpec := #[
  ⟨"SafeAdd", ``BitVec.add,  "SAddOverflow", false⟩,
  ⟨"SafeSub", ``BitVec.sub,  "SSubOverflow", false⟩,
  ⟨"SafeMul", ``BitVec.mul,  "SMulOverflow", false⟩,
  ⟨"SafeNeg", ``BitVec.neg,  "SNegOverflow", true⟩,
  ⟨"SafeUAdd", ``BitVec.add,  "UAddOverflow", false⟩,
  ⟨"SafeUSub", ``BitVec.sub,  "USubOverflow", false⟩,
  ⟨"SafeUMul", ``BitVec.mul,  "UMulOverflow", false⟩,
  ⟨"SafeUNeg", ``BitVec.neg,  "UNegOverflow", true⟩
]

/-- Specs for safe signed division operations (need both div-by-zero and overflow preconditions). -/
private structure BVSafeDivOpSpec where
  opName : String
  opFn : Lean.Name

private def BVSafeDivOpSpecs : Array BVSafeDivOpSpec := #[
  ⟨"SafeSDiv", ``BitVec.sdiv⟩,
  ⟨"SafeSMod", ``BitVec.srem⟩
]

open Lean Elab Command in
/-- Generate safe BV operations with overflow preconditions.
    Each safe operation carries a precondition asserting that the overflow
    predicate is false. The precondition references the overflow predicate
    function generated by `ExpandBVOpFuncDefs`. -/
elab "ExpandBVSafeOpFuncDefs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    let sizeNum := Syntax.mkNumLit s
    for spec in BVSafeOpSpecs do
      let funcName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Func")
      let opName := Syntax.mkStrLit s!"Bv{s}.{spec.opName}"
      let overflowFuncName := mkIdent
        (.str .anonymous s!"bv{s}{spec.overflowPredSuffix}Func")
      let xParam := Syntax.mkStrLit Lambda.unaryParamName
      let yParam := Syntax.mkStrLit Lambda.binaryParam2Name
      if spec.isUnary then
        elabCommand (← `(
          def $funcName : Lambda.WFLFunc CoreLParams :=
            Lambda.unaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent spec.opFn)
              (preconditions := [⟨.app default
                (Lambda.boolNotFunc (T := CoreLParams)).func.opExpr
                (.app default ($overflowFuncName).opExpr
                  (.fvar default $xParam (some (.bitvec $sizeNum)))),
                default⟩])
              (h_precond := by
                intro p hp; simp at hp; subst hp
                decide)))
      else
        elabCommand (← `(
          def $funcName : Lambda.WFLFunc CoreLParams :=
            Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent spec.opFn)
              (preconditions := [⟨.app default
                (Lambda.boolNotFunc (T := CoreLParams)).func.opExpr
                (.app default
                  (.app default ($overflowFuncName).opExpr
                    (.fvar default $xParam (some (.bitvec $sizeNum))))
                  (.fvar default $yParam (some (.bitvec $sizeNum)))),
                default⟩])
              (h_precond := by
                intro p hp; simp at hp; subst hp
                decide)))

open Lean Elab Command in
/-- Generate safe signed division/modulo operations with both div-by-zero
    and overflow (INT_MIN / -1) preconditions. -/
elab "ExpandBVSafeDivOpFuncDefs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    let sizeNum := Syntax.mkNumLit s
    for spec in BVSafeDivOpSpecs do
      let funcName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Func")
      let opName := Syntax.mkStrLit s!"Bv{s}.{spec.opName}"
      let overflowFuncName := mkIdent
        (.str .anonymous s!"bv{s}SDivOverflowFunc")
      let xParam := Syntax.mkStrLit Lambda.binaryParam1Name
      let yParam := Syntax.mkStrLit Lambda.binaryParam2Name
      elabCommand (← `(
        def $funcName : Lambda.WFLFunc CoreLParams :=
          Lambda.binaryOp (InValTy := BitVec $sizeNum) $opName $(mkIdent spec.opFn) (· != 0)
            (preconditions := [
              -- Precondition 1: y ≠ 0 (division by zero)
              ⟨.app default
                (Lambda.boolNotFunc (T := CoreLParams)).func.opExpr
                (.eq default
                  (.fvar default $yParam (some (.bitvec $sizeNum)))
                  (LExpr.bitvecConst default $sizeNum (0 : BitVec $sizeNum))),
                default⟩,
              -- Precondition 2: ¬ SDivOverflow(x, y)
              ⟨.app default
                (Lambda.boolNotFunc (T := CoreLParams)).func.opExpr
                (.app default
                  (.app default ($overflowFuncName).opExpr
                    (.fvar default $xParam (some (.bitvec $sizeNum))))
                  (.fvar default $yParam (some (.bitvec $sizeNum)))),
                default⟩])
            (h_precond := by
              intro p hp
              simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hp
              cases hp with
              | inl h => subst h; decide
              | inr h => subst h; decide)))

end -- public meta section

public section

ExpandBVOpFuncDefs[1, 2, 8, 16, 32, 64]
ExpandBVSafeOpFuncDefs[1, 2, 8, 16, 32, 64]
ExpandBVSafeDivOpFuncDefs[1, 2, 8, 16, 32, 64]

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

def strPrefixOfFunc : WFLFunc CoreLParams :=
  binaryOp "Str.PrefixOf" String.isPrefixOf

def strSuffixOfFunc : WFLFunc CoreLParams :=
  binaryOp "Str.SuffixOf" (fun s t => String.endsWith t s)

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

/- A constant `Map` constructor with type `∀k, v. v → Map k v`.
   `const(d)` returns a map where every key maps to the value `d`. -/
def mapConstFunc : WFLFunc CoreLParams :=
  polyUneval "const" ["k", "v"]
    [("d", mty[%v])]
    (mapTy mty[%k] mty[%v])
    (axioms := [
      esM[∀ (%v): -- %1 d
          (∀ (%k): -- %0 kk
            {(((~select : (Map %k %v) → %k → %v)
                ((~const : %v → (Map %k %v)) %1)) %0)}
            (((~select : (Map %k %v) → %k → %v)
                ((~const : %v → (Map %k %v)) %1)) %0) == %1)]
    ])

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
      esM[∀(Map %k %v):
          (∀ (%k):
            (∀ (%v):{
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1)}
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1) == %0))],
      -- updatePreserve: forall m: Map k v, okk: k, kk: k, vv: v :: okk != kk ==> m[kk := vv][okk] == m[okk]
      esM[∀ (Map %k %v): -- %3 m
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

/- A `Sequence` length function with type `∀a. Sequence a → int`. -/
def seqLengthFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.length" ["a"]
    [("s", seqTy mty[%a])] mty[int]
    (axioms := [
      -- length(s) >= 0
      esM[∀ (Sequence %a): -- %0 s
        {((~Sequence.length : (Sequence %a) → int) %0)}
        (((~Int.Ge : int → int → bool)
          ((~Sequence.length : (Sequence %a) → int) %0))
          #0)]
    ])

/- An empty `Sequence` constructor with type `∀a. Sequence a`.
   `Sequence.empty<A>()` returns an empty sequence of element type `A`.
   The `<A>` is surface syntax produced by Grammar.lean and consumed by
   Translate.lean; this function itself takes no value parameters. -/
def seqEmptyFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.empty" ["a"] [] (seqTy mty[%a])
    (axioms := [
      -- length(empty()) == 0
      esM[((~Sequence.length : (Sequence %a) → int)
            (~Sequence.empty : (Sequence %a))) == #0]
    ])

/- A `Sequence` append function with type `∀a. Sequence a → Sequence a → Sequence a`. -/
def seqAppendFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.append" ["a"]
    [("s1", seqTy mty[%a]), ("s2", seqTy mty[%a])]
    (seqTy mty[%a])
    (axioms := [
      -- length(append(s0, s1)) == length(s0) + length(s1)
      esM[∀ (Sequence %a): -- %1 s0
          (∀ (Sequence %a): -- %0 s1
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %1) %0))}
            ((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %1) %0))
            ==
            (((~Int.Add : int → int → int)
              ((~Sequence.length : (Sequence %a) → int) %1))
              ((~Sequence.length : (Sequence %a) → int) %0)))],
      -- select(append(s0, s1), n):
      --   0 <= n < length(s0) ==> select(append(s0,s1), n) == select(s0, n)
      esM[∀ (Sequence %a): -- %2 s0
          (∀ (Sequence %a): -- %1 s1
            (∀ (int): -- %0 n
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0) ((~Sequence.length : (Sequence %a) → int) %2)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2) %0)
              else #true))],
      -- select(append(s0, s1), n):
      --   n >= length(s0) && n < length(s0) + length(s1)
      --     ==> select(append(s0,s1), n) == select(s1, n - length(s0))
      esM[∀ (Sequence %a): -- %2 s0
          (∀ (Sequence %a): -- %1 s1
            (∀ (int): -- %0 n
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) ((~Sequence.length : (Sequence %a) → int) %2)))
                    (((~Int.Lt : int → int → bool) %0)
                      (((~Int.Add : int → int → int)
                        ((~Sequence.length : (Sequence %a) → int) %2))
                        ((~Sequence.length : (Sequence %a) → int) %1))))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %1)
                    (((~Int.Sub : int → int → int) %0) ((~Sequence.length : (Sequence %a) → int) %2)))
              else #true))]
    ])

/-! ### Sequence bounds preconditions

`Sequence.select` / `update` / `take` / `drop` carry bounds
preconditions; the other `Sequence.*` ops are total. -/

/-- Choice of upper-bound operator in `mkSeqBoundsPrecond`: `Lt` (strict) for
    `Sequence.select`/`update`, `Le` (non-strict) for `Sequence.take`/`drop`.
    Restricting the parameter to this inductive rather than taking an
    arbitrary `WFLFunc` or `LExpr` makes it impossible to attach a partial
    operator (which would create a nested precondition obligation) by
    accident. -/
private inductive SeqBoundKind where | Lt | Le

/-- Returns the *upper-bound* comparison for `mkSeqBoundsPrecond`.
    The lower bound is always `0 ≤ x` (see `mkSeqBoundsPrecond`), so this
    method characterises only the upper comparison. A future partial
    Sequence op requiring a non-`int` comparison (e.g. a bitvector variant)
    should introduce a separate helper rather than extend this enum. -/
private def SeqBoundKind.upperOpExpr : SeqBoundKind → LExpr CoreLParams.mono
  | .Lt => (intLtFunc (T := CoreLParams)).opExpr
  | .Le => (intLeFunc (T := CoreLParams)).opExpr

/-- Precondition `0 <= varName && varName `k.upperOpExpr` Sequence.length(seqName)`.

    `seqName` defaults to `"s"` since all four current call sites
    (`Sequence.select`/`update`/`take`/`drop`) name their `Sequence a` input
    that way. The parameter exists so a future partial Sequence op with a
    different input name need only pass it explicitly rather than rely on a
    hidden string literal. Either way, mismatches between the function's
    declared inputs and the names used here are caught at elaboration by
    `polyUneval`'s `h_precond` free-vars check. -/
private def mkSeqBoundsPrecond
    (varName : String) (k : SeqBoundKind) (seqName : String := "s") :
    Strata.DL.Util.FuncPrecondition (LExpr CoreLParams.mono) CoreLParams.Metadata :=
  let sVar  : LExpr CoreLParams.mono := .fvar default seqName (some (seqTy mty[%a]))
  let xVar  : LExpr CoreLParams.mono := .fvar default varName (some mty[int])
  let zero  : LExpr CoreLParams.mono := .intConst default 0
  let lenS  : LExpr CoreLParams.mono := .app default seqLengthFunc.opExpr sVar
  let lower : LExpr CoreLParams.mono :=
    .app default (.app default (intLeFunc (T := CoreLParams)).opExpr zero) xVar
  let upper : LExpr CoreLParams.mono :=
    .app default (.app default k.upperOpExpr xVar) lenS
  ⟨.app default (.app default (boolAndFunc (T := CoreLParams)).opExpr lower) upper,
   default⟩

/- A `Sequence` selection function with type `∀a. Sequence a → int → a`.
   Partial: requires `0 <= i && i < Sequence.length(s)`. -/
def seqSelectFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.select" ["a"]
    [("s", seqTy mty[%a]), ("i", mty[int])] mty[%a]
    (preconditions := [mkSeqBoundsPrecond "i" .Lt])

/- A `Sequence` build (snoc) function with type `∀a. Sequence a → a → Sequence a`.
   `build(s, v)` appends a single element `v` to the end of `s`. -/
def seqBuildFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.build" ["a"]
    [("s", seqTy mty[%a]), ("v", mty[%a])]
    (seqTy mty[%a])
    (axioms := [
      -- length(build(s, v)) == 1 + length(s)
      esM[∀ (Sequence %a): -- %1 s
          (∀ (%a): -- %0 v
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %1) %0))}
            ((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %1) %0))
            ==
            (((~Int.Add : int → int → int)
              #1)
              ((~Sequence.length : (Sequence %a) → int) %1)))],
      -- select(build(s, v), i):
      --   i == length(s) ==> select(build(s,v), i) == v
      esM[∀ (Sequence %a): -- %2 s
          (∀ (%a): -- %1 v
            (∀ (int): -- %0 i
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)}
              if (%0 == ((~Sequence.length : (Sequence %a) → int) %2))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)
                == %1
              else #true))],
      -- select(build(s, v), i):
      --   0 <= i < length(s) ==> select(build(s,v), i) == select(s, i)
      esM[∀ (Sequence %a): -- %2 s
          (∀ (%a): -- %1 v
            (∀ (int): -- %0 i
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0)
                      ((~Sequence.length : (Sequence %a) → int) %2)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2) %0)
              else #true))]
    ])

/- A `Sequence` update function with type `∀a. Sequence a → int → a → Sequence a`.
   `update(s, i, v)` returns a sequence identical to `s` except at index `i` where the value is `v`.
   Partial: requires `0 <= i && i < Sequence.length(s)`. -/
def seqUpdateFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.update" ["a"]
    [("s", seqTy mty[%a]), ("i", mty[int]), ("v", mty[%a])]
    (seqTy mty[%a])
    (axioms := [
      -- length(update(s, i, v)) == length(s)
      esM[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 i
            (∀ (%a): -- %0 v
              {((~Sequence.length : (Sequence %a) → int)
                ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0))}
              ((~Sequence.length : (Sequence %a) → int)
                ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0))
              ==
              ((~Sequence.length : (Sequence %a) → int) %2)))],
      -- 0 <= i < length(s) ==> select(update(s, i, v), i) == v  (same index)
      esM[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 i
            (∀ (%a): -- %0 v
              {(((~Sequence.select : (Sequence %a) → int → %a)
                  ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0)) %1)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %1) #0))
                    (((~Int.Lt : int → int → bool) %1)
                      ((~Sequence.length : (Sequence %a) → int) %2)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0)) %1)
                == %0
              else #true))],
      -- 0 <= n < length(s) && n != i ==> select(update(s, i, v), n) == select(s, n)
      esM[∀ (Sequence %a): -- %3 s
          (∀ (int): -- %2 i
            (∀ (%a): -- %1 v
              (∀ (int): -- %0 n
                {(((~Sequence.select : (Sequence %a) → int → %a)
                    ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %3) %2) %1)) %0)}
                if (((~Bool.And : bool → bool → bool)
                      (((~Bool.And : bool → bool → bool)
                        (((~Int.Ge : int → int → bool) %0) #0))
                        (((~Int.Lt : int → int → bool) %0)
                          ((~Sequence.length : (Sequence %a) → int) %3))))
                      ((~Bool.Not : bool → bool) (%0 == %2)))
                then
                  (((~Sequence.select : (Sequence %a) → int → %a)
                      ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %3) %2) %1)) %0)
                  ==
                  (((~Sequence.select : (Sequence %a) → int → %a) %3) %0)
                else #true)))]
    ])
    (preconditions := [mkSeqBoundsPrecond "i" .Lt])

/- A `Sequence` contains function with type `∀a. Sequence a → a → bool`.
   `contains(s, v)` is true iff there exists an index `i` such that `select(s, i) == v`. -/
def seqContainsFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.contains" ["a"]
    [("s", seqTy mty[%a]), ("v", mty[%a])] mty[bool]
    (axioms := [
      -- contains(s, v) <==> exists i :: 0 <= i < length(s) && select(s, i) == v
      esM[∀ (Sequence %a): -- %1 s
          (∀ (%a): -- %0 v
            {(((~Sequence.contains : (Sequence %a) → %a → bool) %1) %0)}
            (((~Sequence.contains : (Sequence %a) → %a → bool) %1) %0)
            ==
            (∃ (int): -- %0 i (inside this quantifier: s=%2, v=%1, i=%0)
              (((~Bool.And : bool → bool → bool)
                (((~Bool.And : bool → bool → bool)
                  (((~Int.Ge : int → int → bool) %0) #0))
                  (((~Int.Lt : int → int → bool) %0) ((~Sequence.length : (Sequence %a) → int) %2))))
                ((((~Sequence.select : (Sequence %a) → int → %a) %2) %0) == %1))))]
    ])

/- A `Sequence` take function with type `∀a. Sequence a → int → Sequence a`.
   `take(s, n)` returns the first `n` elements of `s`.
   Partial: requires `0 <= n && n <= Sequence.length(s)`. -/
def seqTakeFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.take" ["a"]
    [("s", seqTy mty[%a]), ("n", mty[int])]
    (seqTy mty[%a])
    (axioms := [
      -- 0 <= n <= length(s) ==> length(take(s, n)) == n
      esM[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 n
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %1) %0))}
            if (((~Bool.And : bool → bool → bool)
                  (((~Int.Ge : int → int → bool) %0) #0))
                  (((~Int.Le : int → int → bool) %0)
                    ((~Sequence.length : (Sequence %a) → int) %1)))
            then
              ((~Sequence.length : (Sequence %a) → int)
                (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %1) %0))
              == %0
            else #true)],
      -- select(take(s, n), j) == select(s, j)  (when 0 <= j < n)
      esM[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 n
            (∀ (int): -- %0 j
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0) %1))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2) %0)
              else #true))]
    ])
    (preconditions := [mkSeqBoundsPrecond "n" .Le])

/- A `Sequence` drop function with type `∀a. Sequence a → int → Sequence a`.
   `drop(s, n)` returns the sequence with the first `n` elements removed.
   Partial: requires `0 <= n && n <= Sequence.length(s)`. -/
def seqDropFunc : WFLFunc CoreLParams :=
  polyUneval "Sequence.drop" ["a"]
    [("s", seqTy mty[%a]), ("n", mty[int])]
    (seqTy mty[%a])
    (axioms := [
      -- 0 <= n <= length(s) ==> length(drop(s, n)) == length(s) - n
      esM[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 n
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %1) %0))}
            if (((~Bool.And : bool → bool → bool)
                  (((~Int.Ge : int → int → bool) %0) #0))
                  (((~Int.Le : int → int → bool) %0)
                    ((~Sequence.length : (Sequence %a) → int) %1)))
            then
              ((~Sequence.length : (Sequence %a) → int)
                (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %1) %0))
              ==
              (((~Int.Sub : int → int → int)
                ((~Sequence.length : (Sequence %a) → int) %1))
                %0)
            else #true)],
      -- 0 <= j < length(s) - n ==> select(drop(s, n), j) == select(s, j + n)
      esM[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 n
            (∀ (int): -- %0 j
              {(((~Sequence.select : (Sequence %a) → int → %a)
                  (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0)
                      (((~Int.Sub : int → int → int)
                        ((~Sequence.length : (Sequence %a) → int) %2))
                        %1)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2)
                    (((~Int.Add : int → int → int) %0) %1))
              else #true))]
    ])
    (preconditions := [mkSeqBoundsPrecond "n" .Le])

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

end -- public section

public meta section

open Lean in
macro "ExpandBVOpFuncNames" "[" sizes:num,* "]" : term => do
  let mut allOps := #[]
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVOpSpecs do
      let name := s!"bv{s}" ++ spec.opName ++ "Func"
      allOps := allOps.push (mkIdent (.str (.str .anonymous "Core") name))
  `([$(allOps),*])

open Lean in
macro "ExpandBVSafeOpFuncNames" "[" sizes:num,* "]" : term => do
  let mut allOps := #[]
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVSafeOpSpecs do
      let name := s!"bv{s}" ++ spec.opName ++ "Func"
      allOps := allOps.push (mkIdent (.str (.str .anonymous "Core") name))
  `([$(allOps),*])

open Lean in
macro "ExpandBVSafeDivOpFuncNames" "[" sizes:num,* "]" : term => do
  let mut allOps := #[]
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVSafeDivOpSpecs do
      let name := s!"bv{s}" ++ spec.opName ++ "Func"
      allOps := allOps.push (mkIdent (.str (.str .anonymous "Core") name))
  `([$(allOps),*])

end -- public meta section

public section

def bvConcatFunc (size : Nat) : WFLFunc CoreLParams :=
  binaryFuncUneval s!"Bv{size}.Concat"
    (.bitvec size) (.bitvec size) (.bitvec (size * 2)) rfl rfl rfl

def bvExtractFunc (size hi lo : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Bv{size}.Extract_{hi}_{lo}"
    (.bitvec size) (.bitvec (hi + 1 - lo)) rfl rfl

def bvToUIntFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Bv{size}.ToUInt" (.bitvec size) .int rfl rfl

def bvToIntFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Bv{size}.ToInt" (.bitvec size) .int rfl rfl

def intToBvFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Int.ToBv{size}" .int (.bitvec size) rfl rfl

def bv8ConcatFunc  := bvConcatFunc 8
def bv16ConcatFunc := bvConcatFunc 16
def bv32ConcatFunc := bvConcatFunc 32

def bv1ToUIntFunc   := bvToUIntFunc 1
def bv8ToUIntFunc   := bvToUIntFunc 8
def bv16ToUIntFunc  := bvToUIntFunc 16
def bv32ToUIntFunc  := bvToUIntFunc 32
def bv64ToUIntFunc  := bvToUIntFunc 64
def bv128ToUIntFunc := bvToUIntFunc 128

def bv1ToIntFunc   := bvToIntFunc 1
def bv8ToIntFunc   := bvToIntFunc 8
def bv16ToIntFunc  := bvToIntFunc 16
def bv32ToIntFunc  := bvToIntFunc 32
def bv64ToIntFunc  := bvToIntFunc 64
def bv128ToIntFunc := bvToIntFunc 128

def int1ToBvFunc   := intToBvFunc 1
def int8ToBvFunc   := intToBvFunc 8
def int16ToBvFunc  := intToBvFunc 16
def int32ToBvFunc  := intToBvFunc 32
def int64ToBvFunc  := intToBvFunc 64
def int128ToBvFunc := intToBvFunc 128

def bv8Extract_7_7_Func    := bvExtractFunc  8  7  7
def bv16Extract_15_15_Func := bvExtractFunc 16 15 15
def bv16Extract_7_0_Func   := bvExtractFunc 16  7  0
def bv32Extract_31_31_Func := bvExtractFunc 32 31 31
def bv32Extract_15_0_Func  := bvExtractFunc 32 15  0
def bv32Extract_7_0_Func   := bvExtractFunc 32  7  0
def bv64Extract_31_0_Func  := bvExtractFunc 64 31  0
def bv64Extract_15_0_Func  := bvExtractFunc 64 15  0
def bv64Extract_7_0_Func   := bvExtractFunc 64  7  0

@[expose]
def WFFactoryArray : Array (Lambda.WFLFunc CoreLParams) := #[
  intAddFunc (T := CoreLParams),
  intSubFunc (T := CoreLParams),
  intMulFunc (T := CoreLParams),
  intDivFunc (T := CoreLParams),
  intSafeDivFunc (T := CoreLParams),
  intModFunc (T := CoreLParams),
  intSafeModFunc (T := CoreLParams),
  intDivTFunc (T := CoreLParams),
  intSafeDivTFunc (T := CoreLParams),
  intModTFunc (T := CoreLParams),
  intSafeModTFunc (T := CoreLParams),
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
  strPrefixOfFunc,
  strSuffixOfFunc,
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

  mapConstFunc,
  mapSelectFunc,
  mapUpdateFunc,

  seqLengthFunc,
  seqEmptyFunc,
  seqAppendFunc,
  seqSelectFunc,
  seqBuildFunc,
  seqUpdateFunc,
  seqContainsFunc,
  seqTakeFunc,
  seqDropFunc,

  emptyTriggersFunc,
  addTriggerGroupFunc,
  emptyTriggerGroupFunc,
  addTriggerFunc,

  bv8ConcatFunc,
  bv16ConcatFunc,
  bv32ConcatFunc,
  bv1ToUIntFunc,
  bv8ToUIntFunc,
  bv16ToUIntFunc,
  bv32ToUIntFunc,
  bv64ToUIntFunc,
  bv128ToUIntFunc,
  bv1ToIntFunc,
  bv8ToIntFunc,
  bv16ToIntFunc,
  bv32ToIntFunc,
  bv64ToIntFunc,
  bv128ToIntFunc,
  int1ToBvFunc,
  int8ToBvFunc,
  int16ToBvFunc,
  int32ToBvFunc,
  int64ToBvFunc,
  int128ToBvFunc,
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
  ++ (ExpandBVSafeOpFuncNames [1,8,16,32,64])
  ++ (ExpandBVSafeDivOpFuncNames [1,8,16,32,64])

set_option maxRecDepth 2000 in
set_option maxHeartbeats 500000 in
theorem WFFactory_names:
(List.map (fun x => x.func.name.name) WFFactoryArray.toList).Nodup := by
  simp only[WFFactoryArray, Array.toList_appendList]
  simp only[List.map_append, List.map]
  simp only[HAppend.hAppend, Append.append]
  simp only[List.append]
  have h8: Nat.repr 8 = "8" := by native_decide
  have h16: Nat.repr 16 = "16" := by native_decide
  have h32: Nat.repr 32 = "32" := by native_decide
  have h64: Nat.repr 64 = "64" := by native_decide
  have h128: Nat.repr 128 = "128" := by native_decide
  have h0: Nat.repr 0 = "0" := by native_decide
  have h7: Nat.repr 7 = "7" := by native_decide
  have h15: Nat.repr 15 = "15" := by native_decide
  have h31 : Nat.repr 31 = "31" := by native_decide
  have h1 : Nat.repr 1 = "1" := by native_decide
  -- unfold names
  simp only[intAddFunc, intSubFunc, intMulFunc, intDivFunc, intSafeDivFunc, intModFunc, intSafeModFunc, intDivTFunc, intSafeDivTFunc,
  intModTFunc, intSafeModTFunc, intNegFunc, intLtFunc, intLeFunc,
  intGtFunc, intGeFunc,
  realAddFunc, realSubFunc, realMulFunc, realDivFunc, realNegFunc, realLtFunc, realLeFunc, realGtFunc, realGeFunc,
  boolAndFunc, boolOrFunc, boolImpliesFunc, boolEquivFunc, boolNotFunc,
  strLengthFunc, strConcatFunc, strSubstrFunc, strToRegexFunc, strInRegexFunc, strPrefixOfFunc, strSuffixOfFunc,
  reAllFunc, reAllCharFunc, reRangeFunc, reConcatFunc, reStarFunc, rePlusFunc, reLoopFunc, reUnionFunc, reInterFunc, reCompFunc, reNoneFunc,
  mapConstFunc, mapSelectFunc, mapUpdateFunc,
  seqLengthFunc, seqEmptyFunc, seqAppendFunc, seqSelectFunc, seqBuildFunc, seqUpdateFunc, seqContainsFunc, seqTakeFunc, seqDropFunc,
  emptyTriggersFunc, addTriggerGroupFunc, emptyTriggerGroupFunc, addTriggerFunc,
  bv8ConcatFunc, bv16ConcatFunc, bv32ConcatFunc,
  bv1ToUIntFunc, bv8ToUIntFunc, bv16ToUIntFunc, bv32ToUIntFunc, bv64ToUIntFunc, bv128ToUIntFunc,
  bv1ToIntFunc, bv8ToIntFunc, bv16ToIntFunc, bv32ToIntFunc, bv64ToIntFunc, bv128ToIntFunc,
  int1ToBvFunc, int8ToBvFunc, int16ToBvFunc, int32ToBvFunc, int64ToBvFunc, int128ToBvFunc,
  bv8Extract_7_7_Func, bv16Extract_15_15_Func, bv16Extract_7_0_Func, bv32Extract_31_31_Func, bv32Extract_15_0_Func, bv32Extract_7_0_Func,
  bv64Extract_31_0_Func, bv64Extract_15_0_Func, bv64Extract_7_0_Func,
  bv1NegFunc, bv1AddFunc, bv1SubFunc, bv1MulFunc, bv1UDivFunc, bv1UModFunc, bv1SDivFunc, bv1SModFunc,
  bv1NotFunc, bv1AndFunc, bv1OrFunc, bv1XorFunc, bv1ShlFunc, bv1UShrFunc, bv1SShrFunc, bv1ULtFunc,
  bv1ULeFunc, bv1UGtFunc, bv1UGeFunc, bv1SLtFunc, bv1SLeFunc, bv1SGtFunc, bv1SGeFunc, bv1SNegOverflowFunc,
  bv1SAddOverflowFunc, bv1SSubOverflowFunc, bv1SMulOverflowFunc, bv1SDivOverflowFunc, bv1UNegOverflowFunc,
  bv1UAddOverflowFunc, bv1USubOverflowFunc, bv1UMulOverflowFunc,
  bv8NegFunc, bv8AddFunc, bv8SubFunc, bv8MulFunc, bv8UDivFunc, bv8UModFunc, bv8SDivFunc, bv8SModFunc,
  bv8NotFunc, bv8AndFunc, bv8OrFunc, bv8XorFunc, bv8ShlFunc, bv8UShrFunc, bv8SShrFunc, bv8ULtFunc,
  bv8ULeFunc, bv8UGtFunc, bv8UGeFunc, bv8SLtFunc, bv8SLeFunc, bv8SGtFunc, bv8SGeFunc, bv8SNegOverflowFunc,
  bv8SAddOverflowFunc, bv8SSubOverflowFunc, bv8SMulOverflowFunc, bv8SDivOverflowFunc, bv8UNegOverflowFunc,
  bv8UAddOverflowFunc, bv8USubOverflowFunc, bv8UMulOverflowFunc,
  bv16NegFunc, bv16AddFunc, bv16SubFunc, bv16MulFunc, bv16UDivFunc, bv16UModFunc, bv16SDivFunc, bv16SModFunc,
  bv16NotFunc, bv16AndFunc, bv16OrFunc, bv16XorFunc, bv16ShlFunc, bv16UShrFunc, bv16SShrFunc, bv16ULtFunc,
  bv16ULeFunc, bv16UGtFunc, bv16UGeFunc, bv16SLtFunc, bv16SLeFunc, bv16SGtFunc, bv16SGeFunc, bv16SNegOverflowFunc,
  bv16SAddOverflowFunc, bv16SSubOverflowFunc, bv16SMulOverflowFunc, bv16SDivOverflowFunc, bv16UNegOverflowFunc,
  bv16UAddOverflowFunc, bv16USubOverflowFunc, bv16UMulOverflowFunc,
  bv32NegFunc, bv32AddFunc, bv32SubFunc, bv32MulFunc, bv32UDivFunc, bv32UModFunc, bv32SDivFunc, bv32SModFunc,
  bv32NotFunc, bv32AndFunc, bv32OrFunc, bv32XorFunc, bv32ShlFunc, bv32UShrFunc, bv32SShrFunc, bv32ULtFunc,
  bv32ULeFunc, bv32UGtFunc, bv32UGeFunc, bv32SLtFunc, bv32SLeFunc, bv32SGtFunc, bv32SGeFunc, bv32SNegOverflowFunc,
  bv32SAddOverflowFunc, bv32SSubOverflowFunc, bv32SMulOverflowFunc, bv32SDivOverflowFunc, bv32UNegOverflowFunc,
  bv32UAddOverflowFunc, bv32USubOverflowFunc, bv32UMulOverflowFunc,
  bv64NegFunc, bv64AddFunc, bv64SubFunc, bv64MulFunc, bv64UDivFunc, bv64UModFunc, bv64SDivFunc, bv64SModFunc,
  bv64NotFunc, bv64AndFunc, bv64OrFunc, bv64XorFunc, bv64ShlFunc, bv64UShrFunc, bv64SShrFunc, bv64ULtFunc,
  bv64ULeFunc, bv64UGtFunc, bv64UGeFunc, bv64SLtFunc, bv64SLeFunc, bv64SGtFunc, bv64SGeFunc, bv64SNegOverflowFunc,
  bv64SAddOverflowFunc, bv64SSubOverflowFunc, bv64SMulOverflowFunc, bv64SDivOverflowFunc, bv64UNegOverflowFunc,
  bv64UAddOverflowFunc, bv64USubOverflowFunc, bv64UMulOverflowFunc,
  bv1SafeAddFunc, bv1SafeSubFunc, bv1SafeMulFunc, bv1SafeNegFunc,
  bv1SafeUAddFunc, bv1SafeUSubFunc, bv1SafeUMulFunc, bv1SafeUNegFunc,
  bv8SafeAddFunc, bv8SafeSubFunc, bv8SafeMulFunc, bv8SafeNegFunc,
  bv8SafeUAddFunc, bv8SafeUSubFunc, bv8SafeUMulFunc, bv8SafeUNegFunc,
  bv16SafeAddFunc, bv16SafeSubFunc, bv16SafeMulFunc, bv16SafeNegFunc,
  bv16SafeUAddFunc, bv16SafeUSubFunc, bv16SafeUMulFunc, bv16SafeUNegFunc,
  bv32SafeAddFunc, bv32SafeSubFunc, bv32SafeMulFunc, bv32SafeNegFunc,
  bv32SafeUAddFunc, bv32SafeUSubFunc, bv32SafeUMulFunc, bv32SafeUNegFunc,
  bv64SafeAddFunc, bv64SafeSubFunc, bv64SafeMulFunc, bv64SafeNegFunc,
  bv64SafeUAddFunc, bv64SafeUSubFunc, bv64SafeUMulFunc, bv64SafeUNegFunc,
  bv1SafeSDivFunc, bv1SafeSModFunc, bv8SafeSDivFunc, bv8SafeSModFunc,
  bv16SafeSDivFunc, bv16SafeSModFunc, bv32SafeSDivFunc, bv32SafeSModFunc,
  bv64SafeSDivFunc, bv64SafeSModFunc,
   binaryOp, unaryOp, binaryFuncUneval, polyUneval, unaryFuncUneval, nullaryUneval, bvConcatFunc, bvToUIntFunc, bvToIntFunc, bvExtractFunc,
   intToBvFunc]
  -- simplify nat constants and string append
  simp only [toString, h8, h16, h32, h64, h128, h0, h7, h15, h31, h1]
  have heq1 : "Bv" ++ "8" ++ ".Concat" = "Bv8.Concat" := by rfl
  have heq2 : "Bv" ++ "16" ++ ".Concat" = "Bv16.Concat" := by rfl
  have heq3 : "Bv" ++ "32" ++ ".Concat" = "Bv32.Concat" := by rfl
  have heq4 : "Bv" ++ "1" ++ ".ToUInt" = "Bv1.ToUInt" := by rfl
  have heq5 : "Bv" ++ "8" ++ ".ToUInt" = "Bv8.ToUInt" := by rfl
  have heq6 : "Bv" ++ "16" ++ ".ToUInt" = "Bv16.ToUInt" := by rfl
  have heq7 : "Bv" ++ "32" ++ ".ToUInt" = "Bv32.ToUInt" := by rfl
  have heq8 : "Bv" ++ "64" ++ ".ToUInt" = "Bv64.ToUInt" := by rfl
  have heq9 : "Bv" ++ "128" ++ ".ToUInt" = "Bv128.ToUInt" := by rfl
  have heq10 : "Bv" ++ "1" ++ ".ToInt" = "Bv1.ToInt" := by rfl
  have heq11 : "Bv" ++ "8" ++ ".ToInt" = "Bv8.ToInt" := by rfl
  have heq12 : "Bv" ++ "16" ++ ".ToInt" = "Bv16.ToInt" := by rfl
  have heq13 : "Bv" ++ "32" ++ ".ToInt" = "Bv32.ToInt" := by rfl
  have heq14 : "Bv" ++ "64" ++ ".ToInt" = "Bv64.ToInt" := by rfl
  have heq15 : "Bv" ++ "128" ++ ".ToInt" = "Bv128.ToInt" := by rfl
  have heq16 : "Int.ToBv" ++ "1" = "Int.ToBv1" := by rfl
  have heq17 : "Int.ToBv" ++ "8" = "Int.ToBv8" := by rfl
  have heq18 : "Int.ToBv" ++ "16" = "Int.ToBv16" := by rfl
  have heq19 : "Int.ToBv" ++ "32" = "Int.ToBv32" := by rfl
  have heq20 : "Int.ToBv" ++ "64" = "Int.ToBv64" := by rfl
  have heq21 : "Int.ToBv" ++ "128" = "Int.ToBv128" := by rfl
  have heq22 : "Bv" ++ "8" ++ ".Extract_" ++ "7" ++ "_" ++ "7" = "Bv8.Extract_7_7" := by rfl
  have heq23 : "Bv" ++ "16" ++ ".Extract_" ++ "15" ++ "_" ++ "15" = "Bv16.Extract_15_15" := by rfl
  have heq24 : "Bv" ++ "16" ++ ".Extract_" ++ "7" ++ "_" ++ "0" = "Bv16.Extract_7_0" := by rfl
  have heq25 : "Bv" ++ "32" ++ ".Extract_" ++ "31" ++ "_" ++ "31" = "Bv32.Extract_31_31" := by rfl
  have heq26 : "Bv" ++ "32" ++ ".Extract_" ++ "15" ++ "_" ++ "0" = "Bv32.Extract_15_0" := by rfl
  have heq27 : "Bv" ++ "32" ++ ".Extract_" ++ "7" ++ "_" ++ "0" = "Bv32.Extract_7_0" := by rfl
  have heq28 : "Bv" ++ "64" ++ ".Extract_" ++ "31" ++ "_" ++ "0" = "Bv64.Extract_31_0" := by rfl
  have heq29 : "Bv" ++ "64" ++ ".Extract_" ++ "15" ++ "_" ++ "0" = "Bv64.Extract_15_0" := by rfl
  have heq30 : "Bv" ++ "64" ++ ".Extract_" ++ "7" ++ "_" ++ "0" = "Bv64.Extract_7_0" := by rfl
  simp only [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, heq10,
    heq11, heq12, heq13, heq14, heq15, heq16, heq17, heq18, heq19, heq20,
    heq21, heq22, heq23, heq24, heq25, heq26, heq27, heq28, heq29, heq30]
  decide

@[expose]
def WFFactory : Lambda.WFLFactory CoreLParams :=
  WFLFactory.ofArray (name_nodup := by exact WFFactory_names) WFFactoryArray

@[expose]
def Factory : @Factory CoreLParams := WFLFactory.toFactory WFFactory

def FactoryFuncNames : List String :=
  (WFFactoryArray.map (·.func.name.name)).toList

/-- Decidable predicate: is `s` the name of a built-in factory function? -/
def isNameInFactory (s : String) : Bool := s ∈ FactoryFuncNames

end -- public section

public meta section

open Lean Elab Command in
elab "DefBVOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVOpSpecs do
      let opName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Op")
      let funcName := mkIdent (.str (.str .anonymous "Core") s!"bv{s}{spec.opName}Func")
      elabCommand (← `(def $opName : Expression.Expr := ($funcName).opExpr))

open Lean Elab Command in
elab "DefBVSafeOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVSafeOpSpecs do
      let opName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Op")
      let funcName := mkIdent (.str (.str .anonymous "Core") s!"bv{s}{spec.opName}Func")
      elabCommand (← `(def $opName : Expression.Expr := ($funcName).opExpr))

open Lean Elab Command in
elab "DefBVSafeDivOpFuncExprs" "[" sizes:num,* "]" : command => do
  for size in sizes.getElems do
    let s := size.getNat.repr
    for spec in BVSafeDivOpSpecs do
      let opName := mkIdent (.str .anonymous s!"bv{s}{spec.opName}Op")
      let funcName := mkIdent (.str (.str .anonymous "Core") s!"bv{s}{spec.opName}Func")
      elabCommand (← `(def $opName : Expression.Expr := ($funcName).opExpr))

end -- public meta section

public section

instance : Inhabited CoreLParams.Metadata where
  default := ()

DefBVOpFuncExprs [1, 8, 16, 32, 64]
DefBVSafeOpFuncExprs [1, 8, 16, 32, 64]
DefBVSafeDivOpFuncExprs [1, 8, 16, 32, 64]

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
def intSafeDivTOp : Expression.Expr := (@intSafeDivTFunc CoreLParams _ _).opExpr
def intModTOp : Expression.Expr := (@intModTFunc CoreLParams _).opExpr
def intSafeModTOp : Expression.Expr := (@intSafeModTFunc CoreLParams _ _).opExpr
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
def strPrefixOfOp : Expression.Expr := strPrefixOfFunc.opExpr
def strSuffixOfOp : Expression.Expr := strSuffixOfFunc.opExpr
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
def mapConstOp : Expression.Expr := mapConstFunc.opExpr
def mapSelectOp : Expression.Expr := mapSelectFunc.opExpr
def mapUpdateOp : Expression.Expr := mapUpdateFunc.opExpr
def seqLengthOp : Expression.Expr := seqLengthFunc.opExpr
def seqEmptyOp (elemTy : Option LMonoTy := none) : Expression.Expr :=
  match elemTy with
  | none => seqEmptyFunc.opExpr
  | some ty => .op default "Sequence.empty" (some (seqTy ty))
def seqAppendOp : Expression.Expr := seqAppendFunc.opExpr
def seqSelectOp : Expression.Expr := seqSelectFunc.opExpr
def seqBuildOp : Expression.Expr := seqBuildFunc.opExpr
def seqUpdateOp : Expression.Expr := seqUpdateFunc.opExpr
def seqContainsOp : Expression.Expr := seqContainsFunc.opExpr
def seqTakeOp : Expression.Expr := seqTakeFunc.opExpr
def seqDropOp : Expression.Expr := seqDropFunc.opExpr

def mkTriggerGroup (ts : List Expression.Expr) : Expression.Expr :=
  ts.foldl (fun g t => .app () (.app () addTriggerOp t) g) emptyTriggerGroupOp

def mkTriggerExpr (ts : List (List Expression.Expr)) : Expression.Expr :=
  let groups := ts.map mkTriggerGroup
  groups.foldl (fun gs g => .app () (.app () addTriggerGroupOp g) gs) emptyTriggersOp

/--
Get all the built-in functions supported by Strata Core.
-/
def builtinFunctions : Array String :=
  Core.Factory.toArray.map (fun f => CoreIdent.toPretty f.name)

end
end Core

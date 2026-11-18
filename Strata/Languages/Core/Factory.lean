/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command

public import Strata.Languages.Core.Expressions
public meta import Strata.Languages.Core.Identifiers
public import Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
public import Strata.Languages.Core.AggregateTypesFactory
import all Strata.Languages.Core.AggregateTypesFactory
import Strata.DL.Util.BitVec
import Strata.Util.StringNodupProps
import all Strata.Util.StringNodup
-- Lets the kernel compute the names built with `s!"Bv{size}..."`.
import all Init.Data.Repr
public meta import Strata.DL.Lambda.IntBoolFactory
---------------------------------------------------------------------

namespace Core
open Lambda LTy.Syntax LExpr.SyntaxMono Core.Syntax

public section

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
   t[∀a. Sequence %a],
   t[∀a. Set %a]]

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
                cbv; grind)))
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
                cbv; grind)))

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
              | inl h => subst h; cbv; grind
              | inr h => subst h; cbv; grind)))

end -- public meta section

public section

-- Supported bitvector widths. This set is repeated in the name-registration and
-- op-expr lists below (all three must agree) and must match the widths exposed by the
-- surface syntax — the `W…` markers and `bv{…}` tokens in `DDMTransform/Grammar.lean`,
-- their handling in `Translate.lean`, and `lmonoTyToCoreType`/`lconstToExpr` in
-- `FormatCore.lean`. `BvWidthPrinterTest` checks the factory and printer agree.
ExpandBVOpFuncDefs[1, 8, 16, 32, 64, 128]
ExpandBVSafeOpFuncDefs[1, 8, 16, 32, 64, 128]
ExpandBVSafeDivOpFuncDefs[1, 8, 16, 32, 64, 128]

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

-- The following string operations are left uninterpreted at the Core level
-- (like `Str.Substr`); the SMT backend interprets them via their SMT-LIB names.
def strContainsFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Str.Contains" mty[string] mty[string] mty[bool]

def strIndexOfFunc : WFLFunc CoreLParams :=
  polyUneval "Str.IndexOf" []
    [("x", mty[string]), ("y", mty[string]), ("i", mty[int])] mty[int]

def strReplaceFunc : WFLFunc CoreLParams :=
  ternaryFuncUneval "Str.Replace" mty[string] mty[string] mty[string]

/-- `Str.At(s, i)`: the one-character string at code-point index `i` of `s`, and `""` when `i`
    is out of range, as SMT-LIB's `str.at`. Evaluated on literals so interpreters can read
    characters; the two inputs have different types, hence `heteroBinaryOp`. -/
def strAtFunc : WFLFunc CoreLParams :=
  heteroBinaryOp "Str.At" (fun (s : String) (i : Int) =>
    if 0 ≤ i ∧ i < s.length then (s.toList[i.toNat]!).toString else "")

-- `Str.Lt`/`Str.Le` carry concrete evaluators so the interpreter can reduce
-- string comparisons. The evaluators use code-point lexicographic order and
-- must agree with the SMT-LIB `str.<`/`str.<=` operators emitted by the encoder.
def strLtFunc : WFLFunc CoreLParams :=
  binaryOp "Str.Lt" (fun (s t : String) => decide (s < t))

def strLeFunc : WFLFunc CoreLParams :=
  binaryOp "Str.Le" (fun (s t : String) => decide (s ≤ t))

-- Conversions between one-character strings and code points, and between strings and
-- non-negative integers, as SMT-LIB's `str.to_code`, `str.from_code`, `str.from_int` and
-- `str.to_int`. All four evaluate on literals, with SMT-LIB's conventions for the cases
-- outside their domain, so the interpreter and the solver agree.

/-- `Str.ToCode(s)`: the code point of `s` when `s` has exactly one character, else `-1`. -/
def strToCodeFunc : WFLFunc CoreLParams :=
  unaryOp "Str.ToCode" (fun (s : String) =>
    match s.toList with
    | [c] => Int.ofNat c.toNat
    | _ => -1)

/-- `Str.FromCode(n)`: the one-character string with code point `n` when `0 ≤ n ≤ 0x2FFFF`,
    else `""`. A Lean `Char` cannot hold a surrogate (`0xD800`-`0xDFFF`), which SMT-LIB's
    alphabet contains, so the evaluator does not fold those: the guard leaves the term to the
    solver, which gives it a one-character string. -/
def strFromCodeFunc : WFLFunc CoreLParams :=
  unaryOp "Str.FromCode" (fun (n : Int) =>
    if 0 ≤ n ∧ n ≤ 0x2FFFF ∧ n.toNat.isValidChar then (Char.ofNat n.toNat).toString else "")
    (guard := fun n => !(0xD800 ≤ n ∧ n ≤ 0xDFFF))

/-- `Str.FromInt(n)`: the decimal digits of `n` when `n ≥ 0`, else `""`. -/
def strFromIntFunc : WFLFunc CoreLParams :=
  unaryOp "Str.FromInt" (fun (n : Int) => if 0 ≤ n then toString n else "")

/-- `Str.ToInt(s)`: the value of `s` read as decimal digits (`0`-`9` only, leading zeros
    allowed) when `s` is non-empty and all digits, else `-1`. Not `String.toNat?`, which
    accepts `_` separators. -/
def strToIntFunc : WFLFunc CoreLParams :=
  unaryOp "Str.ToInt" (fun (s : String) =>
    if s.isEmpty ∨ !s.all Char.isDigit then -1
    else Int.ofNat (s.foldl (fun acc c => 10 * acc + (c.toNat - '0'.toNat)) 0))

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

/-- The operators whose arguments the SMT encoder accepts only as literals: `re.loop`
    takes its bounds as SMT indices. A call applying one to a variable cannot be
    encoded. -/
def literalIndexOps : List String := ["Re.Loop"]

def reUnionFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Re.Union" mty[regex] mty[regex] mty[regex]

def reInterFunc : WFLFunc CoreLParams :=
  binaryFuncUneval "Re.Inter" mty[regex] mty[regex] mty[regex]

def reCompFunc : WFLFunc CoreLParams :=
  unaryFuncUneval "Re.Comp" mty[regex] mty[regex]

def reNoneFunc : WFLFunc CoreLParams :=
  nullaryUneval "Re.None" mty[regex]

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

@[reducible] def bvExtractFunc (size hi lo : Nat) : WFLFunc CoreLParams :=
  unaryOp (inTy := .bitvec size) (outTy := .bitvec (hi + 1 - lo)) s!"Bv{size}.Extract_{hi}_{lo}"
    (fun (b : BitVec size) => b.extractLsb' lo (hi + 1 - lo)) (hInTy := rfl) (hOutTy := rfl)

@[reducible] def bvToUIntFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryOp (inTy := .bitvec size) (outTy := .int) s!"Bv{size}.ToUInt"
    (fun (b : BitVec size) => (b.toNat : Int)) (hInTy := rfl) (hOutTy := rfl)

@[reducible] def bvToIntFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryOp (inTy := .bitvec size) (outTy := .int) s!"Bv{size}.ToInt"
    (fun (b : BitVec size) => b.toInt) (hInTy := rfl) (hOutTy := rfl)

@[reducible] def intToBvFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryOp (inTy := .int) (outTy := .bitvec size) s!"Int.ToBv{size}"
    (fun (i : Int) => BitVec.ofInt size i) (hInTy := rfl) (hOutTy := rfl)

def bv8ConcatFunc  := bvConcatFunc 8
def bv16ConcatFunc := bvConcatFunc 16
def bv32ConcatFunc := bvConcatFunc 32

@[reducible] def bv1ToUIntFunc   := bvToUIntFunc 1
@[reducible] def bv8ToUIntFunc   := bvToUIntFunc 8
@[reducible] def bv16ToUIntFunc  := bvToUIntFunc 16
@[reducible] def bv32ToUIntFunc  := bvToUIntFunc 32
@[reducible] def bv64ToUIntFunc  := bvToUIntFunc 64
@[reducible] def bv128ToUIntFunc := bvToUIntFunc 128

@[reducible] def bv1ToIntFunc   := bvToIntFunc 1
@[reducible] def bv8ToIntFunc   := bvToIntFunc 8
@[reducible] def bv16ToIntFunc  := bvToIntFunc 16
@[reducible] def bv32ToIntFunc  := bvToIntFunc 32
@[reducible] def bv64ToIntFunc  := bvToIntFunc 64
@[reducible] def bv128ToIntFunc := bvToIntFunc 128

@[reducible] def int1ToBvFunc   := intToBvFunc 1
@[reducible] def int8ToBvFunc   := intToBvFunc 8
@[reducible] def int16ToBvFunc  := intToBvFunc 16
@[reducible] def int32ToBvFunc  := intToBvFunc 32
@[reducible] def int64ToBvFunc  := intToBvFunc 64
@[reducible] def int128ToBvFunc := intToBvFunc 128

@[reducible] def bv8Extract_7_7_Func    := bvExtractFunc  8  7  7
@[reducible] def bv16Extract_15_15_Func := bvExtractFunc 16 15 15
@[reducible] def bv16Extract_7_0_Func   := bvExtractFunc 16  7  0
@[reducible] def bv32Extract_31_31_Func := bvExtractFunc 32 31 31
@[reducible] def bv32Extract_15_0_Func  := bvExtractFunc 32 15  0
@[reducible] def bv32Extract_7_0_Func   := bvExtractFunc 32  7  0
@[reducible] def bv64Extract_31_0_Func  := bvExtractFunc 64 31  0
@[reducible] def bv64Extract_15_0_Func  := bvExtractFunc 64 15  0
@[reducible] def bv64Extract_7_0_Func   := bvExtractFunc 64  7  0

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
  strContainsFunc,
  strIndexOfFunc,
  strReplaceFunc,
  strAtFunc,
  strLtFunc,
  strLeFunc,
  strToCodeFunc,
  strFromCodeFunc,
  strFromIntFunc,
  strToIntFunc,
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

  setEmptyFunc,
  setContainsFunc,
  setInsertFunc,
  setRemoveFunc,
  setUnionFunc,
  setIntersectFunc,
  setDifferenceFunc,

  seqLengthFunc,
  seqEmptyFunc,
  seqAppendFunc,
  seqSelectFunc,
  seqSelectUnsafeFunc,
  seqBuildFunc,
  seqUpdateFunc,
  seqUpdateUnsafeFunc,
  seqContainsFunc,
  seqTakeFunc,
  seqTakeUnsafeFunc,
  seqDropFunc,
  seqDropUnsafeFunc,

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
] ++ (ExpandBVOpFuncNames [1,8,16,32,64,128])
  ++ (ExpandBVSafeOpFuncNames [1,8,16,32,64,128])
  ++ (ExpandBVSafeDivOpFuncNames [1,8,16,32,64,128])

/-- The function names in the mapped factory array are pairwise distinct. The
    array is first rewritten into plain lists, so the kernel does not evaluate
    the array operations. -/
theorem WFFactoryArray_func_name_nodup :
    List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) := by
  simp only [WFFactoryArray, Array.toList_map, Array.toList_appendList,
    List.map_append, List.map_map]
  exact Strata.StringNodup.nodup_of_strictlyIncreasing_sortFuel _
    (by decide +kernel)

/-- The function names in the factory array are pairwise distinct, stated in
    the form `WFLFactory.ofArray` takes. -/
theorem WFFactoryArray_name_nodup :
    List.Nodup (WFFactoryArray.toList.map (·.func.name.name)) := by
  simpa only [Array.toList_map, List.map_map, Function.comp_def] using
    WFFactoryArray_func_name_nodup

@[expose]
def WFFactory : Lambda.WFLFactory CoreLParams :=
  WFLFactory.ofArray (name_nodup := WFFactoryArray_name_nodup) WFFactoryArray

@[expose]
def Factory : @Factory CoreLParams := WFLFactory.toFactory WFFactory

def FactoryFuncNames : List String :=
  (WFFactoryArray.map (·.func.name.name)).toList

/-- Decidable predicate: is `s` the name of a built-in factory function? -/
def isNameInFactory (s : String) : Bool := s ∈ FactoryFuncNames

/-! ### Membership lemmas for specific built-in ops

Used by transforms (e.g. `LoopElim`) that synthesize references to standard
ops to discharge downstream `factoryDeclared`-style preconditions. -/

/-- The name of every function in `WFFactoryArray` is a factory name. -/
private theorem isNameInFactory_of_mem (f : WFLFunc CoreLParams)
    (h : f ∈ WFFactoryArray) :
    Core.isNameInFactory f.func.name.name = Bool.true :=
  decide_eq_true (Array.mem_map_of_mem (f := (·.func.name.name)) h).val

/-- Proves `f ∈ WFFactoryArray` for a function `f` written out in the array,
    as opposed to one of the generated bit-vector operations. -/
local macro "factory_mem" : tactic => `(tactic| (
  simp only [WFFactoryArray, ← Array.mem_toList_iff, Array.toList_appendList]
  refine List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ ?_))
  simp only [List.mem_cons, true_or, or_true]))

/-- `Bool.Not` is the name of a built-in factory function. -/
theorem boolNot_isNameInFactory :
    Core.isNameInFactory "Bool.Not" = Bool.true :=
  isNameInFactory_of_mem (boolNotFunc (T := CoreLParams)) (by factory_mem)

/-- `Int.Lt` is the name of a built-in factory function. -/
theorem intLt_isNameInFactory :
    Core.isNameInFactory "Int.Lt" = Bool.true :=
  isNameInFactory_of_mem (intLtFunc (T := CoreLParams)) (by factory_mem)

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
  default := (default : ExprSourceLoc)

DefBVOpFuncExprs [1, 8, 16, 32, 64, 128]
DefBVSafeOpFuncExprs [1, 8, 16, 32, 64, 128]
DefBVSafeDivOpFuncExprs [1, 8, 16, 32, 64, 128]

/-- The three Bv↔Int cast operators, as width-parameterized `opExpr`s.

    Unlike the bitwise and comparison operators (whose per-width names
    `DefBVOpFuncExprs` generates) these take the width as an argument, because
    `bvToUIntFunc`/`bvToIntFunc`/`intToBvFunc` are already width-generic. A
    caller that needs a name rather than an application can use these directly
    instead of rebuilding an `.op` expression with a hand-written arrow type. -/
def bvToUIntOp (size : Nat) : Expression.Expr := (bvToUIntFunc size).opExpr
def bvToIntOp (size : Nat) : Expression.Expr := (bvToIntFunc size).opExpr
def intToBvOp (size : Nat) : Expression.Expr := (intToBvFunc size).opExpr

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
  default := (default : ExprSourceLoc)

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
def strContainsOp : Expression.Expr := strContainsFunc.opExpr
def strIndexOfOp : Expression.Expr := strIndexOfFunc.opExpr
def strReplaceOp : Expression.Expr := strReplaceFunc.opExpr
def strAtOp : Expression.Expr := strAtFunc.opExpr
def strLtOp : Expression.Expr := strLtFunc.opExpr
def strLeOp : Expression.Expr := strLeFunc.opExpr
def strToCodeOp : Expression.Expr := strToCodeFunc.opExpr
def strFromCodeOp : Expression.Expr := strFromCodeFunc.opExpr
def strFromIntOp : Expression.Expr := strFromIntFunc.opExpr
def strToIntOp : Expression.Expr := strToIntFunc.opExpr
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
/-- `Set.empty` takes no value arguments, so its element type cannot be inferred from a
    call site. Pass `elemTy` to annotate the op with the concrete `Set τ`; without it the
    type variable reaches the SMT encoder unresolved. Mirrors `seqEmptyOp`. -/
def setEmptyOp (elemTy : Option LMonoTy := none) : Expression.Expr :=
  match elemTy with
  | none => setEmptyFunc.opExpr
  | some ty => .op default "Set.empty" (some (setTy ty))
def setContainsOp : Expression.Expr := setContainsFunc.opExpr
def setInsertOp : Expression.Expr := setInsertFunc.opExpr
def setRemoveOp : Expression.Expr := setRemoveFunc.opExpr
def setUnionOp : Expression.Expr := setUnionFunc.opExpr
def setIntersectOp : Expression.Expr := setIntersectFunc.opExpr
def setDifferenceOp : Expression.Expr := setDifferenceFunc.opExpr

def seqLengthOp : Expression.Expr := seqLengthFunc.opExpr
def seqEmptyOp (elemTy : Option LMonoTy := none) : Expression.Expr :=
  match elemTy with
  | none => seqEmptyFunc.opExpr
  | some ty => .op default "Sequence.empty" (some (seqTy ty))
def seqAppendOp : Expression.Expr := seqAppendFunc.opExpr
def seqSelectOp : Expression.Expr := seqSelectFunc.opExpr
def seqSelectUnsafeOp : Expression.Expr := seqSelectUnsafeFunc.opExpr
def seqBuildOp : Expression.Expr := seqBuildFunc.opExpr
def seqUpdateOp : Expression.Expr := seqUpdateFunc.opExpr
def seqUpdateUnsafeOp : Expression.Expr := seqUpdateUnsafeFunc.opExpr
def seqContainsOp : Expression.Expr := seqContainsFunc.opExpr
def seqTakeOp : Expression.Expr := seqTakeFunc.opExpr
def seqTakeUnsafeOp : Expression.Expr := seqTakeUnsafeFunc.opExpr
def seqDropOp : Expression.Expr := seqDropFunc.opExpr
def seqDropUnsafeOp : Expression.Expr := seqDropUnsafeFunc.opExpr

def mkTriggerGroup (ts : List Expression.Expr) : Expression.Expr :=
  ts.foldl (fun g t => .app (ExprSourceLoc.synthesized "factory") (.app (ExprSourceLoc.synthesized
      "factory") addTriggerOp t) g) emptyTriggerGroupOp

def mkTriggerExpr (ts : List (List Expression.Expr)) : Expression.Expr :=
  let groups := ts.map mkTriggerGroup
  groups.foldl (fun gs g => .app (ExprSourceLoc.synthesized "factory") (.app
      (ExprSourceLoc.synthesized "factory") addTriggerGroupOp g) gs) emptyTriggersOp

/--
Get all the built-in functions supported by Strata Core.
-/
def builtinFunctions : Array String :=
  Core.Factory.toArray.map (fun f => CoreIdent.toPretty f.name)

end
end Core

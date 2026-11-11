/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReachBridge
import all Strata.Languages.Core.InterpreterReach
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LExpr
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.FactoryProps

/-! # The built-in operators of `Core.Factory` computed on literals

The operators of `Core.Factory` whose concrete evaluator computes every call on literals
(`ComputableOp`): integer arithmetic without division, integer comparisons, the Boolean
connectives, the string operations with concrete evaluators, and the bit-vector operations
without a guard at every width the factory defines, named by `isComputableBuiltin`. Division,
remainder and shifts are excluded: their concrete evaluators leave a zero divisor or an
out-of-range shift undecided, while the reference model gives such calls a value.

Key definitions: `computableScalarOps`, `computableBVOps`, `isComputableBuiltin`,
`isComputableBuiltinFn`. Key theorem: `computableOp_of_builtin`. -/

namespace Core

open Imperative Lambda

public section

/-! ## Built-in operators the evaluator computes on literals -/

/-- The literal decoder of a primitive Lean type decodes every literal of the corresponding
    Core type. -/
private def DecodesLits (inTy : LMonoTy) {InV : Type} [LambdaLeanType inTy InV] : Prop :=
  ∀ (m : ExpressionMetadata) (c : LConst), c.ty = inTy →
    ∃ a, LambdaLeanType.cevalTy (ty := inTy) (ValTy := InV) CoreLParams (.const m c) = some a

/-- The literal builder of a primitive Lean type builds literals of the corresponding Core
    type. -/
private def BuildsLits (outTy : LMonoTy) {OutV : Type} [LambdaLeanType outTy OutV] : Prop :=
  ∀ (md : ExpressionMetadata) (w : OutV), ∃ m c,
    LambdaLeanType.mkConst (ty := outTy) CoreLParams md w = .const m c ∧ c.ty = outTy

/-- The literal decoder and builder of a primitive Lean type decode and build exactly the literals
    of the corresponding Core type. -/
private class LitCodec (ty : LMonoTy) (V : Type) [LambdaLeanType ty V] : Prop where
  /-- Every literal of `ty` decodes. -/
  decodes : DecodesLits (InV := V) ty
  /-- Every built literal has type `ty`. -/
  builds : BuildsLits (OutV := V) ty

/-- Integer literals decode. -/
private theorem decodesLits_int : DecodesLits (InV := Int) .int := by
  intro m c hc
  cases c <;> first | exact ⟨_, rfl⟩ | simp [LConst.ty, LMonoTy.int, LMonoTy.bool,
    LMonoTy.real, LMonoTy.string] at hc

/-- Boolean literals decode. -/
private theorem decodesLits_bool : DecodesLits (InV := Bool) .bool := by
  intro m c hc
  cases c <;> first | exact ⟨_, rfl⟩ | simp [LConst.ty, LMonoTy.int, LMonoTy.bool,
    LMonoTy.real, LMonoTy.string] at hc

/-- String literals decode. -/
private theorem decodesLits_string : DecodesLits (InV := String) .string := by
  intro m c hc
  cases c <;> first | exact ⟨_, rfl⟩ | simp [LConst.ty, LMonoTy.int, LMonoTy.bool,
    LMonoTy.real, LMonoTy.string] at hc

/-- Bit-vector literals of width `n` decode. -/
private theorem decodesLits_bitvec (n : Nat) : DecodesLits (InV := BitVec n) (.bitvec n) := by
  intro m c hc
  cases c with
  | bitvecConst n' b =>
    simp only [LConst.ty, LMonoTy.bitvec.injEq] at hc
    subst hc
    exact ⟨b, by simp [LambdaLeanType.cevalTy, LExpr.denoteBitVec]⟩
  | _ => simp [LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.real, LMonoTy.string] at hc

/-- A `unaryOp` over primitive types whose decoder decodes every literal of its input type and
    whose builder builds literals of its output type is computed on literals. -/
private theorem computableOp_unaryOp {inTy outTy : LMonoTy} {InV OutV : Type} [ToString OutV]
    [LambdaLeanType inTy InV] [LambdaLeanType outTy OutV] [hdec : LitCodec inTy InV]
    [hmk : LitCodec outTy OutV] {n : CoreLParams.Identifier} {f : InV → OutV} {pre hI hO hp} :
    ComputableOp (unaryOp n f pre hI hO hp).func := by
  refine ⟨rfl, rfl, rfl, ⟨_, rfl, ?_⟩⟩
  change CevalTotal _ _
  intro md _ args h
  cases h with
  | cons h1 h2 =>
  cases h2
  obtain ⟨m, c, rfl, hc⟩ := h1
  obtain ⟨a, ha⟩ := hdec.decodes m c hc
  obtain ⟨m', c', hmc, hc'⟩ := hmk.builds md (f a)
  exact ⟨m', c', by simp only [ha, hmc], hc'⟩

/-- A `binaryOp` over primitive types without a guard, whose decoder decodes every literal of its
    input type and whose builder builds literals of its output type, is computed on literals. -/
private theorem computableOp_binaryOp {inTy outTy : LMonoTy} {InV OutV : Type} [ToString OutV]
    [LambdaLeanType inTy InV] [LambdaLeanType outTy OutV] [hdec : LitCodec inTy InV]
    [hmk : LitCodec outTy OutV] {n : CoreLParams.Identifier} {g : InV → InV → OutV}
    {pre hI hO hp} :
    ComputableOp (binaryOp n g (fun _ => true) pre hI hO hp).func := by
  refine ⟨rfl, rfl, rfl, ⟨_, rfl, ?_⟩⟩
  change CevalTotal _ _
  intro md _ args h
  cases h with
  | cons h1 h2 =>
  cases h2 with
  | cons h3 h4 =>
  cases h4
  obtain ⟨m, c, rfl, hc⟩ := h1
  obtain ⟨m2, c2, rfl, hc2⟩ := h3
  obtain ⟨a, ha⟩ := hdec.decodes m c hc
  obtain ⟨b, hb⟩ := hdec.decodes m2 c2 hc2
  obtain ⟨m', c', hmc, hc'⟩ := hmk.builds md (g a b)
  exact ⟨m', c', by simp only [ha, hb, hmc, ↓reduceIte], hc'⟩

/-- A short-circuiting Boolean connective is computed on literals. -/
private theorem computableOp_shortCircuitOp {n : CoreLParams.Identifier} {absorb decided : Bool} :
    ComputableOp (shortCircuitOp n absorb decided).func := by
  refine ⟨rfl, rfl, rfl, ⟨_, rfl, ?_⟩⟩
  simp only [show Strata.DL.Util.FuncAttr.hasShortCircuit
    (shortCircuitOp (T := CoreLParams) n absorb decided).func.attr = true from rfl, ↓reduceIte]
  refine ⟨nofun, ?_, fun md _ a rest ha hlen => ?_⟩
  · show ∀ ty ∈ [LMonoTy.bool, LMonoTy.bool], ty = LMonoTy.bool
    decide
  · cases ha with
    | cons h1 h2 =>
    obtain ⟨m, c, rfl, hc⟩ := h1
    obtain ⟨b, hb⟩ := decodesLits_bool m c hc
    obtain ⟨y, rfl⟩ : ∃ y, rest = [y] := by
      cases rest with
      | nil => cases hlen
      | cons y t => cases t with
        | nil => exact ⟨y, rfl⟩
        | cons _ _ => cases hlen
    by_cases hab : b = absorb
    · refine ⟨_, ?_, .inl ⟨md, .boolConst decided, rfl, rfl⟩⟩
      simp only [hb, hab, beq_self_eq_true, ↓reduceIte]
      rfl
    · exact ⟨y, by simp only [hb, beq_iff_eq, hab, ↓reduceIte], .inr (List.mem_singleton_self _)⟩

/-- Integer literals build. -/
private theorem buildsLits_int : BuildsLits (OutV := Int) .int := fun md _ => ⟨md, _, rfl, rfl⟩

/-- Boolean literals build. -/
private theorem buildsLits_bool : BuildsLits (OutV := Bool) .bool := fun md _ => ⟨md, _, rfl, rfl⟩

/-- String literals build. -/
private theorem buildsLits_string : BuildsLits (OutV := String) .string :=
  fun md _ => ⟨md, _, rfl, rfl⟩

/-- Bit-vector literals of width `n` build. -/
private theorem buildsLits_bitvec (n : Nat) : BuildsLits (OutV := BitVec n) (.bitvec n) :=
  fun md _ => ⟨md, _, rfl, rfl⟩

/-- Integer literals are coded by `Int`. -/
private instance : LitCodec .int Int := ⟨decodesLits_int, buildsLits_int⟩

/-- Boolean literals are coded by `Bool`. -/
private instance : LitCodec .bool Bool := ⟨decodesLits_bool, buildsLits_bool⟩

/-- String literals are coded by `String`. -/
private instance : LitCodec .string String := ⟨decodesLits_string, buildsLits_string⟩

/-- Bit-vector literals of width `n` are coded by `BitVec n`. -/
private instance (n : Nat) : LitCodec (.bitvec n) (BitVec n) :=
  ⟨decodesLits_bitvec n, buildsLits_bitvec n⟩

/-- The operators of `Core.Factory`, other than the bit-vector ones, its concrete evaluators
    compute on literals: integer arithmetic without division, integer comparisons, the Boolean
    connectives, and the string operations with concrete evaluators. -/
@[expose] def computableScalarOps : List String :=
  ["Int.Add", "Int.Sub", "Int.Mul", "Int.Neg", "Int.Lt", "Int.Le", "Int.Gt", "Int.Ge",
    "Bool.And", "Bool.Or", "Bool.Implies", "Bool.Equiv", "Bool.Not", "Str.Length", "Str.Concat",
    "Str.PrefixOf", "Str.SuffixOf", "Str.Lt", "Str.Le"]

/-- The bit-vector operators of `Core.Factory`, at every width it defines, its concrete evaluators
    compute on literals: arithmetic without division, bitwise operations, comparisons, overflow
    predicates and the preconditioned arithmetic. Division, remainder and shifts are guarded. -/
@[expose] def computableBVOps : List String :=
  ["Neg", "Add", "Sub", "Mul", "Not", "And", "Or", "Xor", "ULt", "ULe", "UGt", "UGe", "SLt",
    "SLe", "SGt", "SGe", "SNegOverflow", "SAddOverflow", "SSubOverflow", "SMulOverflow",
    "SDivOverflow", "UNegOverflow", "UAddOverflow", "USubOverflow", "UMulOverflow", "SafeAdd",
    "SafeSub", "SafeMul", "SafeNeg", "SafeUAdd", "SafeUSub", "SafeUMul", "SafeUNeg"]

/-- **The built-in operators the evaluator computes on literals**, by name: those of
    `computableScalarOps`, and those of `computableBVOps` at the widths `1`, `8`, `16`, `32`, `64`,
    `128`. -/
@[expose] def isComputableBuiltin (name : String) : Bool :=
  computableScalarOps.contains name ||
    ["1", "8", "16", "32", "64", "128"].any fun w =>
      computableBVOps.any fun op => name == "Bv" ++ w ++ "." ++ op

/-- **The built-in functions the evaluator computes on literals**: those with a concrete evaluator
    whose name `isComputableBuiltin` admits. -/
@[expose] def isComputableBuiltinFn (fn : LFunc CoreLParams) : Bool :=
  fn.concreteEval.isSome && isComputableBuiltin fn.name.name

/-- The first half of the functions of `Core.Factory`'s underlying array listed by
    hand. -/
private def scalarFns0 : List (WFLFunc CoreLParams) :=
  [intAddFunc (T := CoreLParams), intSubFunc (T := CoreLParams),
   intMulFunc (T := CoreLParams), intDivFunc (T := CoreLParams),
   intSafeDivFunc (T := CoreLParams), intModFunc (T := CoreLParams),
   intSafeModFunc (T := CoreLParams), intDivTFunc (T := CoreLParams),
   intSafeDivTFunc (T := CoreLParams), intModTFunc (T := CoreLParams),
   intSafeModTFunc (T := CoreLParams), intNegFunc (T := CoreLParams),
   intLtFunc (T := CoreLParams), intLeFunc (T := CoreLParams), intGtFunc (T := CoreLParams),
   intGeFunc (T := CoreLParams), realAddFunc, realSubFunc, realMulFunc, realDivFunc,
   realNegFunc, realLtFunc, realLeFunc, realGtFunc, realGeFunc,
   boolAndFunc (T := CoreLParams), boolOrFunc (T := CoreLParams),
   boolImpliesFunc (T := CoreLParams), boolEquivFunc (T := CoreLParams),
   boolNotFunc (T := CoreLParams), strLengthFunc, strConcatFunc, strSubstrFunc,
   strToRegexFunc, strInRegexFunc, strPrefixOfFunc, strSuffixOfFunc, strContainsFunc,
   strIndexOfFunc, strReplaceFunc, strAtFunc, strLtFunc, strLeFunc, reAllFunc, reAllCharFunc,
   reRangeFunc, reConcatFunc, reStarFunc, rePlusFunc, reLoopFunc, reUnionFunc, reInterFunc,
   reCompFunc, reNoneFunc, mapConstFunc]

/-- Every function of the first half of the non-generated part of `Core.Factory`'s
    underlying array that `isComputableBuiltinFn` admits is computed on literals. -/
private theorem computableOp_scalar0 :
    ∀ wf ∈ scalarFns0,
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  unfold scalarFns0
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- The second half of the functions of `Core.Factory`'s underlying array listed by
    hand. -/
private def scalarFns1 : List (WFLFunc CoreLParams) :=
  [mapSelectFunc, mapUpdateFunc, setEmptyFunc, setContainsFunc, setInsertFunc, setRemoveFunc,
   setUnionFunc, setIntersectFunc, setDifferenceFunc, seqLengthFunc, seqEmptyFunc,
   seqAppendFunc, seqSelectFunc, seqSelectUnsafeFunc, seqBuildFunc, seqUpdateFunc,
   seqUpdateUnsafeFunc, seqContainsFunc, seqTakeFunc, seqTakeUnsafeFunc, seqDropFunc,
   seqDropUnsafeFunc, emptyTriggersFunc, addTriggerGroupFunc, emptyTriggerGroupFunc,
   addTriggerFunc, bv8ConcatFunc, bv16ConcatFunc, bv32ConcatFunc, bv1ToUIntFunc,
   bv8ToUIntFunc, bv16ToUIntFunc, bv32ToUIntFunc, bv64ToUIntFunc, bv128ToUIntFunc,
   bv1ToIntFunc, bv8ToIntFunc, bv16ToIntFunc, bv32ToIntFunc, bv64ToIntFunc, bv128ToIntFunc,
   int1ToBvFunc, int8ToBvFunc, int16ToBvFunc, int32ToBvFunc, int64ToBvFunc, int128ToBvFunc,
   bv8Extract_7_7_Func, bv16Extract_15_15_Func, bv16Extract_7_0_Func, bv32Extract_31_31_Func,
   bv32Extract_15_0_Func, bv32Extract_7_0_Func, bv64Extract_31_0_Func, bv64Extract_15_0_Func,
   bv64Extract_7_0_Func]

/-- Every function of the second half of the non-generated part of `Core.Factory`'s
    underlying array that `isComputableBuiltinFn` admits is computed on literals. -/
private theorem computableOp_scalar1 :
    ∀ wf ∈ scalarFns1,
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  unfold scalarFns1
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every generated bit-vector function of width 1 that `isComputableBuiltinFn` admits is computed
    on literals. -/
private theorem computableOp_bv1 :
    ∀ wf ∈ (ExpandBVOpFuncNames [1] ++ ExpandBVSafeOpFuncNames [1] ++
      ExpandBVSafeDivOpFuncNames [1] : List (WFLFunc CoreLParams)),
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  simp only [List.cons_append, List.nil_append]
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every generated bit-vector function of width 8 that `isComputableBuiltinFn` admits is computed
    on literals. -/
private theorem computableOp_bv8 :
    ∀ wf ∈ (ExpandBVOpFuncNames [8] ++ ExpandBVSafeOpFuncNames [8] ++
      ExpandBVSafeDivOpFuncNames [8] : List (WFLFunc CoreLParams)),
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  simp only [List.cons_append, List.nil_append]
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every generated bit-vector function of width 16 that `isComputableBuiltinFn` admits is computed
    on literals. -/
private theorem computableOp_bv16 :
    ∀ wf ∈ (ExpandBVOpFuncNames [16] ++ ExpandBVSafeOpFuncNames [16] ++
      ExpandBVSafeDivOpFuncNames [16] : List (WFLFunc CoreLParams)),
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  simp only [List.cons_append, List.nil_append]
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every generated bit-vector function of width 32 that `isComputableBuiltinFn` admits is computed
    on literals. -/
private theorem computableOp_bv32 :
    ∀ wf ∈ (ExpandBVOpFuncNames [32] ++ ExpandBVSafeOpFuncNames [32] ++
      ExpandBVSafeDivOpFuncNames [32] : List (WFLFunc CoreLParams)),
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  simp only [List.cons_append, List.nil_append]
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every generated bit-vector function of width 64 that `isComputableBuiltinFn` admits is computed
    on literals. -/
private theorem computableOp_bv64 :
    ∀ wf ∈ (ExpandBVOpFuncNames [64] ++ ExpandBVSafeOpFuncNames [64] ++
      ExpandBVSafeDivOpFuncNames [64] : List (WFLFunc CoreLParams)),
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  simp only [List.cons_append, List.nil_append]
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every generated bit-vector function of width 128 that `isComputableBuiltinFn` admits is computed
    on literals. -/
private theorem computableOp_bv128 :
    ∀ wf ∈ (ExpandBVOpFuncNames [128] ++ ExpandBVSafeOpFuncNames [128] ++
      ExpandBVSafeDivOpFuncNames [128] : List (WFLFunc CoreLParams)),
      isComputableBuiltinFn wf.func = true → ComputableOp wf.func := by
  simp only [List.cons_append, List.nil_append]
  repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
  · exact List.forall_mem_nil _
  all_goals
    first
    | exact fun h => absurd h (by decide +kernel)
    | exact fun _ => computableOp_binaryOp
    | exact fun _ => computableOp_unaryOp
    | exact fun _ => computableOp_shortCircuitOp

/-- Every function of `Core.Factory`'s underlying array that `isComputableBuiltinFn` admits is
    computed on literals. -/
private theorem computableOp_of_wf :
    ∀ wf ∈ Core.WFFactoryArray.toList, isComputableBuiltinFn wf.func = true →
      ComputableOp wf.func := by
  intro wf hwf
  simp only [Core.WFFactoryArray, Array.toList_appendList, List.mem_append] at hwf
  rcases hwf with ((h | h) | h) | h
  · rcases List.mem_append.1 (show wf ∈ scalarFns0 ++ scalarFns1 from h) with h | h
    · exact computableOp_scalar0 wf h
    · exact computableOp_scalar1 wf h
  all_goals
    replace h : wf ∈ (ExpandBVOpFuncNames [1] ++ ExpandBVOpFuncNames [8] ++
        ExpandBVOpFuncNames [16] ++ ExpandBVOpFuncNames [32] ++ ExpandBVOpFuncNames [64] ++
        ExpandBVOpFuncNames [128] : List (WFLFunc CoreLParams)) ∨
      wf ∈ (ExpandBVSafeOpFuncNames [1] ++ ExpandBVSafeOpFuncNames [8] ++
        ExpandBVSafeOpFuncNames [16] ++ ExpandBVSafeOpFuncNames [32] ++
        ExpandBVSafeOpFuncNames [64] ++
        ExpandBVSafeOpFuncNames [128] : List (WFLFunc CoreLParams)) ∨
      wf ∈ (ExpandBVSafeDivOpFuncNames [1] ++ ExpandBVSafeDivOpFuncNames [8] ++
        ExpandBVSafeDivOpFuncNames [16] ++ ExpandBVSafeDivOpFuncNames [32] ++
        ExpandBVSafeDivOpFuncNames [64] ++
        ExpandBVSafeDivOpFuncNames [128] : List (WFLFunc CoreLParams)) := by
      first | exact .inl h | exact .inr (.inl h) | exact .inr (.inr h)
    simp only [List.mem_append] at h
    rcases h with (((((h | h) | h) | h) | h) | h) | (((((h | h) | h) | h) | h) | h) |
      (((((h | h) | h) | h) | h) | h)
  all_goals
    first
    | exact computableOp_bv1 wf (List.mem_append_left _ (List.mem_append_left _ h))
    | exact computableOp_bv1 wf (List.mem_append_left _ (List.mem_append_right _ h))
    | exact computableOp_bv1 wf (List.mem_append_right _ h)
    | exact computableOp_bv8 wf (List.mem_append_left _ (List.mem_append_left _ h))
    | exact computableOp_bv8 wf (List.mem_append_left _ (List.mem_append_right _ h))
    | exact computableOp_bv8 wf (List.mem_append_right _ h)
    | exact computableOp_bv16 wf (List.mem_append_left _ (List.mem_append_left _ h))
    | exact computableOp_bv16 wf (List.mem_append_left _ (List.mem_append_right _ h))
    | exact computableOp_bv16 wf (List.mem_append_right _ h)
    | exact computableOp_bv32 wf (List.mem_append_left _ (List.mem_append_left _ h))
    | exact computableOp_bv32 wf (List.mem_append_left _ (List.mem_append_right _ h))
    | exact computableOp_bv32 wf (List.mem_append_right _ h)
    | exact computableOp_bv64 wf (List.mem_append_left _ (List.mem_append_left _ h))
    | exact computableOp_bv64 wf (List.mem_append_left _ (List.mem_append_right _ h))
    | exact computableOp_bv64 wf (List.mem_append_right _ h)
    | exact computableOp_bv128 wf (List.mem_append_left _ (List.mem_append_left _ h))
    | exact computableOp_bv128 wf (List.mem_append_left _ (List.mem_append_right _ h))
    | exact computableOp_bv128 wf (List.mem_append_right _ h)

/-- Every function of `Core.Factory` that `isComputableBuiltinFn` admits is computed on literals
    (`ComputableOp`). -/
theorem computableOp_of_builtin {fn : LFunc CoreLParams} (h : fn ∈ Core.Factory.toArray)
    (hn : isComputableBuiltinFn fn = true) : ComputableOp fn := by
  obtain ⟨wf, hwf, rfl⟩ :=
    Array.mem_map.mp (Lambda.Factory.ofArray_mem (a := Core.WFFactoryArray.map (·.func)) h)
  exact computableOp_of_wf wf (Array.mem_def.mp hwf) hn

end

end Core

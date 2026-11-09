/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Util.FuncAttr
import all Strata.Languages.Core.Factory
import all Strata.Languages.Core.FactoryWF
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent

public section

/-! # Bitvector evaluation properties

How Core's `Bv16` operators interpret and evaluate on `Core.Factory`: the
interpretation laws `bv16ULe_opInterp`, `bv16And_opInterp`, `bv16Xor_opInterp`
that every consistent model satisfies, and the evaluation laws `eval_bv16ULe`,
`eval_bv16And`, `eval_bv16Xor`. These facts expose the bitvector semantics needed
by Hoare proofs over translated Core programs.
-/

namespace Core

open Imperative

/-! ## Width-parametric bitvector operations -/

/-- A bitvector predicate represented as a concrete Lambda function. -/
def bvPredicate (width : Nat) (name : CoreIdent)
    (op : BitVec width → BitVec width → Bool) : Lambda.WFLFunc CoreLParams :=
  Lambda.binaryOp (inTy := .bitvec width) (outTy := .bool) name op
    (hInTy := by rfl) (hOutTy := by rfl) (h_precond := by simp)

/-- A binary bitvector operation represented as a concrete Lambda function. -/
def bvBinary (width : Nat) (name : CoreIdent)
    (op : BitVec width → BitVec width → BitVec width) : Lambda.WFLFunc CoreLParams :=
  Lambda.binaryOp (inTy := .bitvec width) (outTy := .bitvec width) name op
    (hInTy := by rfl) (hOutTy := by rfl) (h_precond := by simp)

/-- The width-indexed unsigned-less-than-or-equal function descriptor. -/
def bvULe (width : Nat) : Lambda.WFLFunc CoreLParams :=
  bvPredicate width ⟨s!"Bv{width}.ULe", ()⟩ BitVec.ule

/-! ## `Bv16` factory membership -/

/-- `Bv16.ULe` resolves in the concrete `Core.Factory` to `bv16ULeFunc`. -/
private theorem coreFactory_bv16ULe :
    Core.Factory["Bv16.ULe"]? = some bv16ULeFunc.func := by
  have hname : bv16ULeFunc.func.name.name = "Bv16.ULe" := rfl
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : bv16ULeFunc.func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16ULeFunc, ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory, ← hname]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-- `Bv16.And` resolves to its generated function in `Core.Factory`. -/
private theorem coreFactory_bv16And :
    Core.Factory["Bv16.And"]? = some bv16AndFunc.func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : bv16AndFunc.func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16AndFunc, ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-- `Bv16.Xor` resolves to its generated function in `Core.Factory`. -/
private theorem coreFactory_bv16Xor :
    Core.Factory["Bv16.Xor"]? = some bv16XorFunc.func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : bv16XorFunc.func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16XorFunc, ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-! ## Width-parametric interpretation -/

/-- The concrete evaluator of a binary bitvector function built by `binaryOp`, with any
output type, maps two width-`width` bitvector literals to the literal of its Lean operation
applied to them. -/
private theorem concreteEval_bvOp (width : Nat) (name : CoreIdent) {c : Lambda.LMonoTy}
    {OutV : Type} [ToString OutV] [Lambda.LambdaLeanType c OutV]
    (op : BitVec width → BitVec width → OutV) (hO : c.freeVars = []) (a b : BitVec width) :
    (Lambda.binaryOp (T := CoreLParams) (inTy := .bitvec width) (outTy := c) name op
        (hInTy := rfl) (hOutTy := hO) (h_precond := fun _ h => by simp at h)).func.concreteEval.bind
      (fun ce => ce () [.bitvecConst () width a, .bitvecConst () width b]) =
      some (Lambda.LambdaLeanType.mkConst CoreLParams () (op a b)) := by
  have hda : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width a : Expression.Expr) = some a := by
    simp [Lambda.LExpr.denoteBitVec]
  have hdb : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width b : Expression.Expr) = some b := by
    simp [Lambda.LExpr.denoteBitVec]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bitvec width)
      (ValTy := BitVec width) CoreLParams = Lambda.LExpr.denoteBitVec width := rfl
  simp only [Lambda.binaryOp, Option.bind_some, hcev, hda, hdb, ite_true]

/-- Any registered concrete bitvector predicate has its Lean semantics in every
consistent interpretation of `Core.Factory`, at any bitwidth. -/
private theorem bvPredicate_opInterp
    (width : Nat) (name : CoreIdent) (op : BitVec width → BitVec width → Bool)
    (model : Lambda.Interp Core.Factory)
    (hF : Core.Factory[name.name]? = some (bvPredicate width name op).func) :
    model.opInterp name.name
        (Lambda.LSort.mkArrow .bool [.bitvec width, .bitvec width]) = op := by
  funext a b
  exact (opInterp_of_concreteEval model hF rfl (concreteEval_bvOp width name op rfl a b)
    (fun _ => .bool) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons .const (.cons .const .nil)) .const).symm

/-- Any registered concrete binary bitvector operation has its Lean semantics in every
consistent interpretation of `Core.Factory`, at any bitwidth. -/
private theorem bvBinary_opInterp
    (width : Nat) (name : CoreIdent) (op : BitVec width → BitVec width → BitVec width)
    (model : Lambda.Interp Core.Factory)
    (hF : Core.Factory[name.name]? = some (bvBinary width name op).func) :
    model.opInterp name.name
        (Lambda.LSort.mkArrow (.bitvec width) [.bitvec width, .bitvec width]) = op := by
  funext a b
  exact (opInterp_of_concreteEval model hF rfl (concreteEval_bvOp width name op rfl a b)
    (fun _ => .bool) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons .const (.cons .const .nil)) .const).symm

/-- `Bv{width}.ULe` is unsigned comparison in every consistent interpretation
whenever that width is registered in `Core.Factory`. -/
theorem bvULe_opInterp
    (width : Nat) (model : Lambda.Interp Core.Factory)
    (hF : Core.Factory[s!"Bv{width}.ULe"]? = some (bvULe width).func) :
    model.opInterp s!"Bv{width}.ULe"
        (Lambda.LSort.mkArrow .bool [.bitvec width, .bitvec width])
      = fun (a b : BitVec width) => BitVec.ule a b := by
  exact bvPredicate_opInterp width ⟨s!"Bv{width}.ULe", ()⟩ BitVec.ule model hF

/-- `Bv16.ULe` is unsigned comparison in every consistent interpretation of
`Core.Factory`. -/
theorem bv16ULe_opInterp (model : Lambda.Interp Core.Factory) :
    model.opInterp "Bv16.ULe"
        (Lambda.LSort.mkArrow .bool [.bitvec 16, .bitvec 16])
      = fun (a b : BitVec 16) => BitVec.ule a b := by
  have hF : Core.Factory[(⟨"Bv16.ULe", ()⟩ : CoreIdent).name]? =
      some (bvPredicate 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule).func := by
    simpa only [show bv16ULeFunc =
      bvPredicate 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule from rfl] using coreFactory_bv16ULe
  exact bvPredicate_opInterp 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule model hF

/-- `Bv16.And` is bitwise conjunction in every consistent interpretation of `Core.Factory`. -/
theorem bv16And_opInterp (model : Lambda.Interp Core.Factory) :
    model.opInterp "Bv16.And"
        (Lambda.LSort.mkArrow (.bitvec 16) [.bitvec 16, .bitvec 16])
      = fun (a b : BitVec 16) => BitVec.and a b := by
  have hF : Core.Factory[(⟨"Bv16.And", ()⟩ : CoreIdent).name]? =
      some (bvBinary 16 ⟨"Bv16.And", ()⟩ BitVec.and).func := by
    simpa only [show bv16AndFunc =
      bvBinary 16 ⟨"Bv16.And", ()⟩ BitVec.and from rfl] using coreFactory_bv16And
  exact bvBinary_opInterp 16 ⟨"Bv16.And", ()⟩ BitVec.and model hF

/-- `Bv16.Xor` is bitwise exclusive-or in every consistent interpretation of `Core.Factory`. -/
theorem bv16Xor_opInterp (model : Lambda.Interp Core.Factory) :
    model.opInterp "Bv16.Xor"
        (Lambda.LSort.mkArrow (.bitvec 16) [.bitvec 16, .bitvec 16])
      = fun (a b : BitVec 16) => BitVec.xor a b := by
  have hF : Core.Factory[(⟨"Bv16.Xor", ()⟩ : CoreIdent).name]? =
      some (bvBinary 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor).func := by
    simpa only [show bv16XorFunc =
      bvBinary 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor from rfl] using coreFactory_bv16Xor
  exact bvBinary_opInterp 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor model hF

/-! ## Evaluation of `Bv16` operators

Core's evaluator (`Expression.eval`) is denotational, so on a runtime factory over
`Core.Factory` a `Bv16` operator applied to two bitvector values evaluates to the
standard operation. -/

/-- `Bv16.ULe` applied to two bitvectors evaluates to unsigned comparison. -/
theorem eval_bv16ULe {f : Expression.Factory}
    {m m' : ExpressionMetadata} (hf : f.factory = Core.Factory)
    {σ : CoreStore} {x y : Expression.Expr} {a b : BitVec 16}
    (hx : Expression.eval f σ x = some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 a))
    (hy : Expression.eval f σ y = some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 b)) :
    Expression.eval f σ (.app m (.app m' bv16ULeFunc.opExpr x) y) =
      some (Lambda.SemValue.ofBool f.model.tcInterp (BitVec.ule a b)) := by
  obtain ⟨F, model⟩ := f
  obtain rfl : F = Core.Factory := hf
  exact eval_app2_op "Bv16.ULe" (a := .bitvec 16) (b := .bitvec 16) (c := .bool) rfl rfl rfl hx hy
    (congrFun (congrFun (bv16ULe_opInterp model) a) b)

/-- `Bv16.And` applied to two bitvectors evaluates to bitwise conjunction. -/
theorem eval_bv16And {f : Expression.Factory}
    {m m' : ExpressionMetadata} (hf : f.factory = Core.Factory)
    {σ : CoreStore} {x y : Expression.Expr} {a b : BitVec 16}
    (hx : Expression.eval f σ x = some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 a))
    (hy : Expression.eval f σ y = some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 b)) :
    Expression.eval f σ (.app m (.app m' bv16AndFunc.opExpr x) y) =
      some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 (BitVec.and a b)) := by
  obtain ⟨F, model⟩ := f
  obtain rfl : F = Core.Factory := hf
  exact eval_app2_op "Bv16.And" (a := .bitvec 16) (b := .bitvec 16) (c := .bitvec 16)
    rfl rfl rfl hx hy
    (congrFun (congrFun (bv16And_opInterp model) a) b)

/-- `Bv16.Xor` applied to two bitvectors evaluates to bitwise exclusive-or. -/
theorem eval_bv16Xor {f : Expression.Factory}
    {m m' : ExpressionMetadata} (hf : f.factory = Core.Factory)
    {σ : CoreStore} {x y : Expression.Expr} {a b : BitVec 16}
    (hx : Expression.eval f σ x = some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 a))
    (hy : Expression.eval f σ y = some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 b)) :
    Expression.eval f σ (.app m (.app m' bv16XorFunc.opExpr x) y) =
      some (Lambda.SemValue.ofBitVec f.model.tcInterp 16 (BitVec.xor a b)) := by
  obtain ⟨F, model⟩ := f
  obtain rfl : F = Core.Factory := hf
  exact eval_app2_op "Bv16.Xor" (a := .bitvec 16) (b := .bitvec 16) (c := .bitvec 16)
    rfl rfl rfl hx hy
    (congrFun (congrFun (bv16Xor_opInterp model) a) b)

end Core

end -- public section

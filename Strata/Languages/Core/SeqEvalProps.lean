/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.IntEvalProps
public import Strata.Languages.Core.BoolEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteCompute
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import Strata.DL.Lambda.FactoryProps
import all Strata.Languages.Core.Factory
import all Strata.Languages.Core.AggregateTypesFactory

/-! # Sequence operator interpretation properties

A model interprets `Sequence.length`, `Sequence.select` and `Sequence.select!` as some
functions on the lists a sequence sort denotes. Every model satisfies the factory's axioms
(`Lambda.Interp.axiomsSatisfied`), so the facts those axioms state hold of the
interpretations in every model, which is what a proof about a sequence the program does not
build needs.

Key results:
- `Core.seqLengthOf`, `Core.seqSelectOf` and `Core.seqSelectBangOf` name a model's length and
  element functions at an element sort;
- `Core.seqLength_nonneg`: a length is nonnegative;
- `Core.seqSelectBang_eq_select`: `select!` and `select` agree in range;
- `Core.eval_seqLength`, `Core.eval_seqSelect` and `Core.eval_seqSelectBang` give Core's
  evaluation of the three operators;
- `Core.coreFactory_seqLength`, `Core.coreFactory_seqSelect` and
  `Core.coreFactory_seqSelectBang` resolve them in `Core.Factory`.
-/

public section

namespace Core

open _root_.Lambda

/-! ## The operators in `Core.Factory` -/

/-- A function of `WFFactoryArray` resolves in `Core.Factory` under its own name. -/
private theorem coreFactory_get?_of_wf {wf : Lambda.WFLFunc CoreLParams}
    (hmem : wf.func ∈ WFFactoryArray.map (·.func)) :
    (Core.Factory)[wf.func.name.name]? = some wf.func := by
  have hCore : Core.Factory = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  rw [hCore]
  exact Lambda.Factory.get?_ofArray_of_mem hmem WFFactoryArray_func_name_nodup

/-- `Sequence.length` resolves in the concrete `Core.Factory` to `seqLengthFunc`. -/
theorem coreFactory_seqLength :
    (Core.Factory)["Sequence.length"]? = some seqLengthFunc.func :=
  coreFactory_get?_of_wf (wf := seqLengthFunc) (by
    refine Array.mem_map.mpr ⟨seqLengthFunc, ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Sequence.select` resolves in the concrete `Core.Factory` to `seqSelectFunc`. -/
theorem coreFactory_seqSelect :
    (Core.Factory)["Sequence.select"]? = some seqSelectFunc.func :=
  coreFactory_get?_of_wf (wf := seqSelectFunc) (by
    refine Array.mem_map.mpr ⟨seqSelectFunc, ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Sequence.select!` resolves in the concrete `Core.Factory` to `seqSelectUnsafeFunc`. -/
theorem coreFactory_seqSelectBang :
    (Core.Factory)["Sequence.select!"]? = some seqSelectUnsafeFunc.func :=
  coreFactory_get?_of_wf (wf := seqSelectUnsafeFunc) (by
    refine Array.mem_map.mpr ⟨seqSelectUnsafeFunc, ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-! ## The interpretations -/

/-- The length a model gives a sequence of element sort `a`. -/
abbrev seqLengthOf {F : Lambda.Factory CoreLParams} (model : Lambda.Interp F) (a : LSort)
    (s : SortDenote model.tcInterp (.tcons "Sequence" [a])) : Int :=
  model.opInterp "Sequence.length" (LSort.mkArrow .int [.tcons "Sequence" [a]]) s

/-- The element a model's `Sequence.select` gives a sequence of element sort `a` at index
    `i`. -/
abbrev seqSelectOf {F : Lambda.Factory CoreLParams} (model : Lambda.Interp F) (a : LSort)
    (s : SortDenote model.tcInterp (.tcons "Sequence" [a])) (i : Int) :
    SortDenote model.tcInterp a :=
  model.opInterp "Sequence.select" (LSort.mkArrow a [.tcons "Sequence" [a], .int]) s i

/-- The element a model's `Sequence.select!` gives a sequence of element sort `a` at index
    `i`. -/
abbrev seqSelectBangOf {F : Lambda.Factory CoreLParams} (model : Lambda.Interp F) (a : LSort)
    (s : SortDenote model.tcInterp (.tcons "Sequence" [a])) (i : Int) :
    SortDenote model.tcInterp a :=
  model.opInterp "Sequence.select!" (LSort.mkArrow a [.tcons "Sequence" [a], .int]) s i

/-- **A length is nonnegative**, in every model of a factory that resolves `Sequence.length`
    and `Int.Ge` to Core's built-ins: the axiom `length(s) >= 0` of `Sequence.length`. -/
theorem seqLength_nonneg {F : Lambda.Factory CoreLParams} (model : Lambda.Interp F)
    (hlen : F["Sequence.length"]? = some seqLengthFunc.func)
    (hge : F["Int.Ge"]? = some (Lambda.intGeFunc (T := CoreLParams)).func)
    (a : LSort) (s : SortDenote model.tcInterp (.tcons "Sequence" [a])) :
    0 ≤ seqLengthOf model a s := by
  have hax := model.axiomsSatisfied "Sequence.length" (Factory.getElem?_some_implies_mem hlen)
  rw [Factory.getElem?_some_getElem hlen] at hax
  simp only [seqLengthFunc, polyLitOp, List.mem_singleton, forall_eq] at hax
  let fv : FreeVarVal CoreLParams model.tcInterp :=
    fun _ s => @default _ (@SortDenote.instInhabited model.tcInterp model.allInhabited s)
  -- The axiom at the element sort, its quantifier at `s`, then its body.
  have h := hax (fun _ => a) fv (LExpr.typeCheck_to_HasTypeA rfl)
  have hv := Eq.mp (denote_true_iff_of_Denotes (by denotes)) h
  rw [classical_decide_eq_true] at hv
  have hb := Eq.mp (denote_true_iff_of_Denotes (by denotes)) (hv s)
  exact of_decide_eq_true
    ((intGe_opInterp_of_lookup model hge (seqLengthOf model a s) 0).symm.trans hb)

/-- **`select!` and `select` agree in range**, in every model of a factory that resolves
    `Sequence.select` and the connectives and comparisons of its axiom to Core's built-ins: the
    axiom `0 <= i < length(s) ==> select!(s, i) == select(s, i)` of `Sequence.select`. -/
theorem seqSelectBang_eq_select {F : Lambda.Factory CoreLParams} (model : Lambda.Interp F)
    (hsel : F["Sequence.select"]? = some seqSelectFunc.func)
    (hand : F["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func)
    (hle : F["Int.Le"]? = some (Lambda.intLeFunc (T := CoreLParams)).func)
    (hlt : F["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func)
    (a : LSort) (s : SortDenote model.tcInterp (.tcons "Sequence" [a])) (i : Int)
    (h0 : 0 ≤ i) (hi : i < seqLengthOf model a s) :
    seqSelectBangOf model a s i = seqSelectOf model a s i := by
  have hax := model.axiomsSatisfied "Sequence.select" (Factory.getElem?_some_implies_mem hsel)
  rw [Factory.getElem?_some_getElem hsel] at hax
  simp only [seqSelectFunc, polyLitOp, List.mem_singleton, forall_eq] at hax
  let fv : FreeVarVal CoreLParams model.tcInterp :=
    fun _ s => @default _ (@SortDenote.instInhabited model.tcInterp model.allInhabited s)
  -- The axiom at the element sort, its two quantifiers at `s` and `i`, then its body.
  have h := hax (fun _ => a) fv (LExpr.typeCheck_to_HasTypeA rfl)
  have hv := Eq.mp (denote_true_iff_of_Denotes (by denotes)) h
  rw [classical_decide_eq_true] at hv
  have hv2 := Eq.mp (denote_true_iff_of_Denotes (by denotes)) (hv s)
  rw [classical_decide_eq_true] at hv2
  have hb := Eq.mp (denote_true_iff_of_Denotes (by denotes)) (hv2 i)
  dsimp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map, denoteConst, LConst.ty] at hb
  -- The guard: the comparisons and the conjunction as the model interprets them.
  have e1 := intLe_opInterp_of_lookup model hle 0 i
  have e2 := intLt_opInterp_of_lookup model hlt i (seqLengthOf model a s)
  have e3 := boolAnd_opInterp_of_lookup model hand (decide (0 ≤ i))
    (decide (i < seqLengthOf model a s))
  dsimp only [LSort.mkArrow, List.foldr, seqLengthOf] at e1 e2 e3
  rw [show (Int.ofNat 0) = 0 from rfl, e1, e2, e3] at hb
  have hi' : i < model.opInterp "Sequence.length"
      (LSort.tcons "arrow" [LSort.tcons "Sequence" [a], LSort.int]) s := hi
  simp only [h0, hi', decide_true, Bool.and_self] at hb
  exact @of_decide_eq_true _ (Classical.propDecidable _) hb

/-! ## Evaluation -/

/-- A sequence of a ground element type is ground. -/
theorem seqTy_isGround {a : LMonoTy} (ha : a.IsGround) :
    (LMonoTy.tcons "Sequence" [a]).IsGround := by
  simp only [LMonoTy.IsGround, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LSort.toMonoTy,
    LSort.toMonoTy.map] at ha ⊢
  rw [ha]

/-- `Sequence.length(x)` evaluates to the length the model gives the sequence `x` evaluates
    to. -/
theorem eval_seqLength {f : Expression.Factory} {m m' : ExpressionMetadata} {a : LMonoTy}
    (ha : a.IsGround) {σ : CoreStore} {x : Expression.Expr}
    {s : SortDenote f.model.tcInterp (.tcons "Sequence" [a.substTyVars f.tyVarVal])}
    (hx : Expression.eval f σ x =
      some ⟨f.model.tcInterp, .tcons "Sequence" [a.substTyVars f.tyVarVal], s⟩) :
    Expression.eval f σ
        (.app m (.op m' ⟨"Sequence.length", ()⟩ (some (.arrow (.tcons "Sequence" [a]) .int))) x) =
      some (SemValue.ofInt f.model.tcInterp (seqLengthOf f.model (a.substTyVars f.tyVarVal) s)) :=
  eval_app1_op "Sequence.length" (seqTy_isGround ha) rfl hx rfl

/-- `Sequence.select(x, y)` evaluates to the element the model's `select` gives at the
    sequence and the index `x` and `y` evaluate to. -/
theorem eval_seqSelect {f : Expression.Factory} {m m' m'' : ExpressionMetadata} {a : LMonoTy}
    (ha : a.IsGround) {σ : CoreStore} {x y : Expression.Expr}
    {s : SortDenote f.model.tcInterp (.tcons "Sequence" [a.substTyVars f.tyVarVal])} {i : Int}
    (hx : Expression.eval f σ x =
      some ⟨f.model.tcInterp, .tcons "Sequence" [a.substTyVars f.tyVarVal], s⟩)
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp i)) :
    Expression.eval f σ (.app m (.app m' (.op m'' ⟨"Sequence.select", ()⟩
        (some (.arrow (.tcons "Sequence" [a]) (.arrow .int a)))) x) y) =
      some ⟨f.model.tcInterp, a.substTyVars f.tyVarVal,
        seqSelectOf f.model (a.substTyVars f.tyVarVal) s i⟩ :=
  eval_app2_op "Sequence.select" (seqTy_isGround ha) rfl ha hx hy rfl

/-- `Sequence.select!(x, y)` evaluates to the element the model's `select!` gives at the
    sequence and the index `x` and `y` evaluate to. -/
theorem eval_seqSelectBang {f : Expression.Factory} {m m' m'' : ExpressionMetadata}
    {a : LMonoTy} (ha : a.IsGround) {σ : CoreStore} {x y : Expression.Expr}
    {s : SortDenote f.model.tcInterp (.tcons "Sequence" [a.substTyVars f.tyVarVal])} {i : Int}
    (hx : Expression.eval f σ x =
      some ⟨f.model.tcInterp, .tcons "Sequence" [a.substTyVars f.tyVarVal], s⟩)
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp i)) :
    Expression.eval f σ (.app m (.app m' (.op m'' ⟨"Sequence.select!", ()⟩
        (some (.arrow (.tcons "Sequence" [a]) (.arrow .int a)))) x) y) =
      some ⟨f.model.tcInterp, a.substTyVars f.tyVarVal,
        seqSelectBangOf f.model (a.substTyVars f.tyVarVal) s i⟩ :=
  eval_app2_op "Sequence.select!" (seqTy_isGround ha) rfl ha hx hy rfl

end Core

end -- public section

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.Languages.Core.Factory

/-! # Integer operator interpretation properties

Key results:
- `Core.intGe_opInterp` identifies `Int.Ge` with integer comparison;
- `Core.intAdd_opInterp` and `Core.intMul_opInterp` identify built-in arithmetic;
- `Core.intAdd_opInterp_of_lookup`, `Core.intSub_opInterp_of_lookup`,
  `Core.intMul_opInterp_of_lookup`, and `Core.intGt_opInterp_of_lookup` provide
  the corresponding facts for factories extending `Core.Factory`;
- `Core.denote_intAdd_of_lookup`, `Core.denote_intSub_of_lookup`,
  `Core.denote_intMul_of_lookup`, and `Core.denote_intGt_of_lookup` lift them
  to the denotation of an operator applied to two integer-valued arguments.
-/

public section

namespace Core

open _root_.Lambda

/-- `Int.Ge`'s interpretation at `int, int → bool` is `≥` in every consistent model. -/
theorem intGe_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Ge"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool)
      = decide (a ≥ b) := by
  have hmem : "Int.Ge" ∈ Core.Factory :=
    Lambda.Factory.getElem?_some_implies_mem Core.coreFactory_intGe
  have hget : Core.Factory["Int.Ge"]'hmem = (Lambda.intGeFunc (T := Core.CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem Core.coreFactory_intGe
  have hsome : (Core.Factory["Int.Ge"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Ge" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b]
      = some (.boolConst () (decide (a ≥ b))) := by
    have hda : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool) (ValTy := Bool) Core.CoreLParams
        = @Lambda.LExpr.boolConst Core.CoreLParams.mono := rfl
    have key : (Lambda.intGeFunc (T := Core.CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b])
        = some (.boolConst () (decide (a ≥ b))) := by
      simp only [Lambda.intGeFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, ite_true]
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.boolConst () (decide (a ≥ b))) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () (decide (a ≥ b))) .bool := .const
  have h_eq := h_inst h_args h_result
  change decide (a ≥ b) = model.opInterp "Int.Ge"
    (Lambda.LSort.mkArrow .bool [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Add`'s interpretation at `int, int → int` is `+` in every consistent model. -/
theorem intAdd_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Add"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int)
      = a + b := by
  have hmem : "Int.Add" ∈ Core.Factory :=
    Lambda.Factory.getElem?_some_implies_mem Core.coreFactory_intAdd
  have hget : Core.Factory["Int.Add"]'hmem = (Lambda.intAddFunc (T := Core.CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem Core.coreFactory_intAdd
  have hsome : (Core.Factory["Int.Add"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Add" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] = some (.intConst () (a + b)) := by
    have hda : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = @Lambda.LExpr.intConst Core.CoreLParams.mono := rfl
    have key : (Lambda.intAddFunc (T := Core.CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b]) = some (.intConst () (a + b)) := by
      simp only [Lambda.intAddFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, ite_true]
      rfl
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .int
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.intConst () (a + b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.intConst () (a + b)) .int := .const
  have h_eq := h_inst h_args h_result
  change ((a + b : Int)) = model.opInterp "Int.Add"
    (Lambda.LSort.mkArrow .int [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Mul`'s interpretation at `int, int → int` is `*` in every consistent model. -/
theorem intMul_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Mul"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int)
      = a * b := by
  have hmem : "Int.Mul" ∈ Core.Factory :=
    Lambda.Factory.getElem?_some_implies_mem Core.coreFactory_intMul
  have hget : Core.Factory["Int.Mul"]'hmem = (Lambda.intMulFunc (T := Core.CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem Core.coreFactory_intMul
  have hsome : (Core.Factory["Int.Mul"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Mul" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] = some (.intConst () (a * b)) := by
    have hda : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.int) (ValTy := Int) Core.CoreLParams
        = @Lambda.LExpr.intConst Core.CoreLParams.mono := rfl
    have key : (Lambda.intMulFunc (T := Core.CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b]) = some (.intConst () (a * b)) := by
      simp only [Lambda.intMulFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, ite_true]
      rfl
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have h_vt : Lambda.TyVarVal := fun _ => .int
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.intConst () a, .intConst () b] (.intConst () (a * b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.intConst () (a * b)) .int := .const
  have h_eq := h_inst h_args h_result
  change ((a * b : Int)) = model.opInterp "Int.Mul"
    (Lambda.LSort.mkArrow .int [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Add` keeps its standard interpretation in any factory that resolves
    it to Core's built-in addition function. -/
theorem intAdd_opInterp_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Add"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a + b := by
  have hmem : "Int.Add" ∈ factory :=
    Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : factory["Int.Add"]'hmem = (Lambda.intAddFunc (T := CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (factory["Int.Add"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Add" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] =
      some (.intConst () (a + b)) := by
    have hda : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        @Lambda.LExpr.intConst CoreLParams.mono := rfl
    have key : (Lambda.intAddFunc (T := CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b]) =
        some (.intConst () (a + b)) := by
      simp only [Lambda.intAddFunc, Lambda.binaryOp, Option.bind_some,
        hcev, hmk, hda, hdb, ite_true]
      rfl
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have vt : Lambda.TyVarVal := fun _ => .int
  have fv : Lambda.FreeVarVal CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic vt fv () Lambda.Subst.empty
    [.intConst () a, .intConst () b] (.intConst () (a + b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (.intConst () (a + b)) .int := .const
  have h_eq := h_inst h_args h_result
  change (a + b) = model.opInterp "Int.Add"
    (Lambda.LSort.mkArrow .int [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Sub` keeps its standard interpretation in any factory that resolves
    it to Core's built-in subtraction function. -/
theorem intSub_opInterp_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Sub"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a - b := by
  have hmem : "Int.Sub" ∈ factory :=
    Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : factory["Int.Sub"]'hmem = (Lambda.intSubFunc (T := CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (factory["Int.Sub"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Sub" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] =
      some (.intConst () (a - b)) := by
    have hda : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        @Lambda.LExpr.intConst CoreLParams.mono := rfl
    have key : (Lambda.intSubFunc (T := CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b]) =
        some (.intConst () (a - b)) := by
      simp only [Lambda.intSubFunc, Lambda.binaryOp, Option.bind_some,
        hcev, hmk, hda, hdb, ite_true]
      rfl
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have vt : Lambda.TyVarVal := fun _ => .int
  have fv : Lambda.FreeVarVal CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic vt fv () Lambda.Subst.empty
    [.intConst () a, .intConst () b] (.intConst () (a - b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (.intConst () (a - b)) .int := .const
  have h_eq := h_inst h_args h_result
  change (a - b) = model.opInterp "Int.Sub"
    (Lambda.LSort.mkArrow .int [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Mul` keeps its standard interpretation in any factory that resolves
    it to Core's built-in multiplication function. -/
theorem intMul_opInterp_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Mul"]? = some (Lambda.intMulFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Mul"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a * b := by
  have hmem : "Int.Mul" ∈ factory :=
    Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : factory["Int.Mul"]'hmem = (Lambda.intMulFunc (T := CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (factory["Int.Mul"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Mul" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] =
      some (.intConst () (a * b)) := by
    have hda : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        @Lambda.LExpr.intConst CoreLParams.mono := rfl
    have key : (Lambda.intMulFunc (T := CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b]) =
        some (.intConst () (a * b)) := by
      simp only [Lambda.intMulFunc, Lambda.binaryOp, Option.bind_some,
        hcev, hmk, hda, hdb, ite_true]
      rfl
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have vt : Lambda.TyVarVal := fun _ => .int
  have fv : Lambda.FreeVarVal CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic vt fv () Lambda.Subst.empty
    [.intConst () a, .intConst () b] (.intConst () (a * b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (.intConst () (a * b)) .int := .const
  have h_eq := h_inst h_args h_result
  change (a * b) = model.opInterp "Int.Mul"
    (Lambda.LSort.mkArrow .int [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- `Int.Gt` has integer greater-than semantics in any factory that resolves it
    to Core's built-in comparison function. -/
theorem intGt_opInterp_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Gt"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = decide (a > b) := by
  have hmem : "Int.Gt" ∈ factory :=
    Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : factory["Int.Gt"]'hmem = (Lambda.intGtFunc (T := CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (factory["Int.Gt"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Int.Gt" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.intConst () a, .intConst () b] =
      some (.boolConst () (decide (a > b))) := by
    have hda : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () a : Core.Expression.Expr) = some a := rfl
    have hdb : Lambda.LExpr.denoteInt
        (Lambda.LExpr.intConst () b : Core.Expression.Expr) = some b := rfl
    have hcev : Lambda.LambdaLeanType.cevalTy
        (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams =
        Lambda.LExpr.denoteInt := rfl
    have hmk : Lambda.LambdaLeanType.mkConst
        (ty := Lambda.LMonoTy.bool) (ValTy := Bool) CoreLParams =
        @Lambda.LExpr.boolConst CoreLParams.mono := rfl
    have key : (Lambda.intGtFunc (T := CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.intConst () a, .intConst () b]) =
        some (.boolConst () (decide (a > b))) := by
      simp only [Lambda.intGtFunc, Lambda.binaryOp, Option.bind_some,
        hcev, hmk, hda, hdb, ite_true]
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have vt : Lambda.TyVarVal := fun _ => .int
  have fv : Lambda.FreeVarVal CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic vt fv () Lambda.Subst.empty
    [.intConst () a, .intConst () b] (.boolConst () (decide (a > b))) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := CoreLParams) [])
      [.intConst () a, .intConst () b] [Lambda.LMonoTy.int, Lambda.LMonoTy.int] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (.boolConst () (decide (a > b))) .bool := .const
  have h_eq := h_inst h_args h_result
  change decide (a > b) = model.opInterp "Int.Gt"
    (Lambda.LSort.mkArrow .bool [.int, .int]) a b at h_eq
  exact h_eq.symm

/-- In any factory that resolves `Int.Add` to Core's built-in addition,
    `int.add(e₁, e₂)` denotes `a + b` when `e₁` and `e₂` denote `a` and `b`. -/
theorem denote_intAdd_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intAddOp e₁) e₂) .int)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intAddOp e₁) e₂) .int h = a + b := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intAddOp
      (.arrow .int (.arrow .int .int)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intAddOp e₁) (.arrow .int .int) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intAddOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intAdd_opInterp_of_lookup model hlookup a b

/-- In any factory that resolves `Int.Sub` to Core's built-in subtraction,
    `int.sub(e₁, e₂)` denotes `a - b` when `e₁` and `e₂` denote `a` and `b`. -/
theorem denote_intSub_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intSubOp e₁) e₂) .int)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intSubOp e₁) e₂) .int h = a - b := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intSubOp
      (.arrow .int (.arrow .int .int)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intSubOp e₁) (.arrow .int .int) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intSubOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intSub_opInterp_of_lookup model hlookup a b

/-- In any factory that resolves `Int.Mul` to Core's built-in multiplication,
    `int.mul(e₁, e₂)` denotes `a * b` when `e₁` and `e₂` denote `a` and `b`. -/
theorem denote_intMul_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Mul"]? = some (Lambda.intMulFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intMulOp e₁) e₂) .int)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intMulOp e₁) e₂) .int h = a * b := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intMulOp
      (.arrow .int (.arrow .int .int)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intMulOp e₁) (.arrow .int .int) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intMulOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intMul_opInterp_of_lookup model hlookup a b

/-- In any factory that resolves `Int.Gt` to Core's built-in comparison,
    `int.gt(e₁, e₂)` denotes `decide (a > b)` when `e₁` and `e₂` denote `a`
    and `b`. -/
theorem denote_intGt_of_lookup {factory : Expression.Factory}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intGtOp e₁) e₂) .bool)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intGtOp e₁) e₂) .bool h : Bool) = decide (a > b) := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intGtOp
      (.arrow .int (.arrow .int .bool)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intGtOp e₁) (.arrow .int .bool) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intGtOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intGt_opInterp_of_lookup model hlookup a b

end Core

end -- public section

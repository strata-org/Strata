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

/-! # Integer operator interpretation properties

Key results:
- `Core.intGe_opInterp` identifies `Int.Ge` with integer comparison;
- `Core.intAdd_opInterp` identifies `Int.Add` with integer addition;
- `Core.intMul_opInterp` identifies `Int.Mul` with integer multiplication.
-/

public section

namespace Core

open Lambda

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
      simp only [Lambda.intGeFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, if_true]
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
      simp only [Lambda.intAddFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, if_true]
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
      simp only [Lambda.intMulFunc, Lambda.binaryOp, Option.bind_some, hcev, hmk, hda, hdb, if_true]
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

end Core

end -- public section

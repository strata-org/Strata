/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ExpressionsProps
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

/-! # Concrete bitvector evaluator properties

Fuel-level and `evalFully` laws for concrete bitvector operations on
`Core.Factory`. These facts expose the bitvector semantics needed by Hoare
proofs over translated Core programs.
-/

namespace Core

open Imperative Lambda

/-! ## Equality with bitvector constants -/

/-- Core expressions have unit metadata, so erasing metadata is the identity. -/
private theorem eraseMetadata_id (v : Expression.Expr) : v.eraseMetadata = v := by
  induction v <;> simp_all [Lambda.LExpr.eraseMetadata, Lambda.LExpr.replaceMetadata]

/-- Metadata-insensitive equality is ordinary equality for Core expressions. -/
private theorem expr_eq_of_eqModuloMeta {v w : Expression.Expr}
    (h : Lambda.LExpr.eqModuloMeta v w = true) : v = w := by
  unfold Lambda.LExpr.eqModuloMeta at h
  rw [eraseMetadata_id, eraseMetadata_id] at h
  exact (Lambda.LExpr.beq_eq v w).mp h

/-- If `eql` equates a Core value with a bitvector constant, the expressions are equal. -/
theorem eq_bitvecConst_of_eql_true (F : Expression.Factory) {n : Nat} {w : BitVec n}
    {v : Expression.Expr}
    (h : Lambda.LExpr.eql F v (Lambda.LExpr.bitvecConst () n w) = some true) :
    v = Lambda.LExpr.bitvecConst () n w := by
  by_cases hmm : Lambda.LExpr.eqModuloMeta v (Lambda.LExpr.bitvecConst () n w) = true
  · exact expr_eq_of_eqModuloMeta hmm
  · unfold Lambda.LExpr.eql at h
    rw [if_neg hmm] at h
    cases v with
    | const m c1 =>
      cases c1 <;> simp_all <;>
        (obtain ⟨rfl, hb⟩ := h; have hbw := eq_of_heq hb; subst hbw; cases m; rfl)
    | abs _ _ _ _ => simp_all
    | app _ _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    | fvar _ _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    | bvar _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    | op _ _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    | quant _ _ _ _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    | ite _ _ _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    | eq _ _ _ => simp_all [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]

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

/-- The width-indexed bitwise-and function descriptor. -/
def bvAnd (width : Nat) : Lambda.WFLFunc CoreLParams :=
  bvBinary width ⟨s!"Bv{width}.And", ()⟩ BitVec.and

/-- The width-indexed bitwise-xor function descriptor. -/
def bvXor (width : Nat) : Lambda.WFLFunc CoreLParams :=
  bvBinary width ⟨s!"Bv{width}.Xor", ()⟩ BitVec.xor

/-! ## `Bv16` factory membership used by compatibility wrappers -/

set_option maxRecDepth 8000 in
/-- `Bv16.ULe` resolves in the concrete `Core.Factory` to `bv16ULeFunc`. -/
private theorem coreFactory_bv16ULe :
    Core.Factory["Bv16.ULe"]? = some bv16ULeFunc.func := by
  have hname : bv16ULeFunc.func.name.name = "Bv16.ULe" := rfl
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : bv16ULeFunc.func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16ULeFunc, ?_, rfl⟩
    unfold WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList, List.mem_append, List.mem_cons]
    grind
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory, ← hname]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

set_option maxRecDepth 8000 in
/-- `Bv16.And` resolves to its generated function in `Core.Factory`. -/
private theorem coreFactory_bv16And :
    Core.Factory["Bv16.And"]? = some bv16AndFunc.func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : bv16AndFunc.func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16AndFunc, ?_, rfl⟩
    unfold WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList, List.mem_append, List.mem_cons]
    grind
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

set_option maxRecDepth 8000 in
/-- `Bv16.Xor` resolves to its generated function in `Core.Factory`. -/
private theorem coreFactory_bv16Xor :
    Core.Factory["Bv16.Xor"]? = some bv16XorFunc.func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : bv16XorFunc.func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16XorFunc, ?_, rfl⟩
    unfold WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList, List.mem_append, List.mem_cons]
    grind
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-! ## Width-parametric evaluation -/

private theorem eval_bvPredicate_value
    (width : Nat) (name : CoreIdent) (op : BitVec width → BitVec width → Bool)
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr)
    (fuel : Nat) (a b : BitVec width)
    (hF : f[name.name]? = some (bvPredicate width name op).func)
    (hx : Lambda.LExpr.eval fuel f σ x =
      (Lambda.LExpr.bitvecConst () width a, .value true))
    (hy : Lambda.LExpr.eval fuel f σ y =
      (Lambda.LExpr.bitvecConst () width b, .value true)) :
    Lambda.LExpr.eval (fuel + 1) f σ
        (.app () (.app () (bvPredicate width name op).opExpr x) y)
      = (Lambda.LExpr.boolConst () (op a b), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (bvPredicate width name op).opExpr x) y)
      = some ((bvPredicate width name op).opExpr, [x, y],
        (bvPredicate width name op).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      bvPredicate, Lambda.binaryOp]
    rw [hF]
    simp [bvPredicate, Lambda.binaryOp]
  have hcan : Lambda.LExpr.isValue f
      (.app () (.app () (bvPredicate width name op).opExpr x) y) = false := by
    simp only [Lambda.LExpr.isValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
      Lambda.LFuncDefined.opExpr, bvPredicate, Lambda.binaryOp]
    rw [hF]
    simp [bvPredicate, Lambda.binaryOp]
  have hcanbv : ∀ (a : BitVec width),
      Lambda.LExpr.isValue f
        (Lambda.LExpr.bitvecConst () width a : Expression.Expr) = true := by
    intro a
    exact Lambda.isValue_const_true f () (.bitvecConst width a)
  have hcanb : ∀ (b : Bool),
      Lambda.LExpr.isValue f (Lambda.LExpr.boolConst () b : Expression.Expr) = true := by
    intro b
    exact Lambda.isValue_const_true f () (.boolConst b)
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by simp [hcan]), hcall]
  dsimp only
  rw [Lambda.LExpr.shortCircuitCall?_of_not_attr _
    (by simp [Strata.DL.Util.FuncAttr.hasShortCircuit, bvPredicate, Lambda.binaryOp])]
  dsimp only
  simp only [bvPredicate, Lambda.binaryOp]
  rw [dif_neg (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfValue #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [Lambda.LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bitvec width)
      (ValTy := BitVec width) CoreLParams = Lambda.LExpr.denoteBitVec width := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool)
      (ValTy := Bool) CoreLParams = @Lambda.LExpr.boolConst CoreLParams.mono := rfl
  simp only [hcev, hmk]
  have hda : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width a : Expression.Expr) = some a := by
    simp [Lambda.LExpr.denoteBitVec]
  have hdb : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width b : Expression.Expr) = some b := by
    simp [Lambda.LExpr.denoteBitVec]
  rw [if_pos (by simp [hcanbv])]
  simp only [hda, hdb, if_true]
  rw [Lambda.eval_value_identity fuel f σ _ (hcanb _)]
  simp [Lambda.LExpr.combineEvalResValueFlag_eq_pair,
    Lambda.LExpr.EvalResult.combineValueFlag]

set_option maxRecDepth 8000 in
private theorem eval_bvBinary_value
    (width : Nat) (name : CoreIdent)
    (op : BitVec width → BitVec width → BitVec width)
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr)
    (fuel : Nat) (a b : BitVec width)
    (hF : f[name.name]? = some (bvBinary width name op).func)
    (hx : Lambda.LExpr.eval fuel f σ x =
      (Lambda.LExpr.bitvecConst () width a, .value true))
    (hy : Lambda.LExpr.eval fuel f σ y =
      (Lambda.LExpr.bitvecConst () width b, .value true)) :
    Lambda.LExpr.eval (fuel + 1) f σ
        (.app () (.app () (bvBinary width name op).opExpr x) y)
      = (Lambda.LExpr.bitvecConst () width (op a b), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (bvBinary width name op).opExpr x) y)
      = some ((bvBinary width name op).opExpr, [x, y],
        (bvBinary width name op).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      bvBinary, Lambda.binaryOp]
    rw [hF]
    simp [bvBinary, Lambda.binaryOp]
  have hcan : Lambda.LExpr.isValue f
      (.app () (.app () (bvBinary width name op).opExpr x) y) = false := by
    simp only [Lambda.LExpr.isValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
      Lambda.LFuncDefined.opExpr, bvBinary, Lambda.binaryOp]
    rw [hF]
    simp [bvBinary, Lambda.binaryOp]
  have hcanbv : ∀ (a : BitVec width),
      Lambda.LExpr.isValue f
        (Lambda.LExpr.bitvecConst () width a : Expression.Expr) = true := by
    intro a
    exact Lambda.isValue_const_true f () (.bitvecConst width a)
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by simp [hcan]), hcall]
  dsimp only
  rw [Lambda.LExpr.shortCircuitCall?_of_not_attr _
    (by simp [Strata.DL.Util.FuncAttr.hasShortCircuit, bvBinary, Lambda.binaryOp])]
  dsimp only
  simp only [bvBinary, Lambda.binaryOp]
  rw [dif_neg (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfValue #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [Lambda.LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bitvec width)
      (ValTy := BitVec width) CoreLParams = Lambda.LExpr.denoteBitVec width := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bitvec width)
      (ValTy := BitVec width) CoreLParams =
        (fun m b => @Lambda.LExpr.bitvecConst CoreLParams.mono m width b) := rfl
  simp only [hcev, hmk]
  have hda : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width a : Expression.Expr) = some a := by
    simp [Lambda.LExpr.denoteBitVec]
  have hdb : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width b : Expression.Expr) = some b := by
    simp [Lambda.LExpr.denoteBitVec]
  rw [if_pos (by simp [hcanbv])]
  simp only [hda, hdb, if_true]
  rw [Lambda.eval_value_identity fuel f σ _ (hcanbv _)]
  simp [Lambda.LExpr.combineEvalResValueFlag_eq_pair,
    Lambda.LExpr.EvalResult.combineValueFlag]

/-- A registered bitvector predicate evaluates at any bitwidth by applying its
Lean operation to the operand values. The lookup premise records that the
chosen operation is actually present in `Core.Factory`. -/
theorem coreEval_bvPredicate
    (width : Nat) (name : CoreIdent) (op : BitVec width → BitVec width → Bool)
    (hF : Core.Factory[name.name]? = some (bvPredicate width name op).func)
    (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec width)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () width a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () width b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bvPredicate width name op).opExpr x) y)
      = some (Lambda.LExpr.boolConst () (op a b)) := by
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  obtain ⟨ny, hny, _⟩ := Lambda.evalFully_some_exists Core.Factory σ y _ hy
  have hx_max := Lambda.eval_value_true_mono_le Core.Factory σ nx (max nx ny)
    (Nat.le_max_left _ _) x _ hnx
  have hy_max := Lambda.eval_value_true_mono_le Core.Factory σ ny (max nx ny)
    (Nat.le_max_right _ _) y _ hny
  have hstep := eval_bvPredicate_value width name op Core.Factory σ x y
    (max nx ny) a b hF hx_max hy_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

/-- A registered binary bitvector operation evaluates at any bitwidth by
applying its Lean operation to the operand values. -/
private theorem coreEval_bvBinary
    (width : Nat) (name : CoreIdent)
    (op : BitVec width → BitVec width → BitVec width)
    (hF : Core.Factory[name.name]? = some (bvBinary width name op).func)
    (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec width)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () width a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () width b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bvBinary width name op).opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () width (op a b)) := by
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  obtain ⟨ny, hny, _⟩ := Lambda.evalFully_some_exists Core.Factory σ y _ hy
  have hx_max := Lambda.eval_value_true_mono_le Core.Factory σ nx (max nx ny)
    (Nat.le_max_left _ _) x _ hnx
  have hy_max := Lambda.eval_value_true_mono_le Core.Factory σ ny (max nx ny)
    (Nat.le_max_right _ _) y _ hny
  have hstep := eval_bvBinary_value width name op Core.Factory σ x y
    (max nx ny) a b hF hx_max hy_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

/-- `Bv{width}.ULe` evaluates to unsigned comparison whenever that width is
registered in `Core.Factory`. -/
theorem coreEval_bvULe
    (width : Nat) (hF : Core.Factory[s!"Bv{width}.ULe"]? = some (bvULe width).func)
    (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec width)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () width a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () width b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bvULe width).opExpr x) y)
      = some (Lambda.LExpr.boolConst () (BitVec.ule a b)) := by
  exact coreEval_bvPredicate width ⟨s!"Bv{width}.ULe", ()⟩ BitVec.ule
    hF σ x y a b hx hy

/-- `Bv{width}.And` evaluates to bitwise conjunction whenever that width is
registered in `Core.Factory`. -/
theorem coreEval_bvAnd
    (width : Nat) (hF : Core.Factory[s!"Bv{width}.And"]? = some (bvAnd width).func)
    (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec width)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () width a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () width b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bvAnd width).opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () width (BitVec.and a b)) := by
  exact coreEval_bvBinary width ⟨s!"Bv{width}.And", ()⟩ BitVec.and
    hF σ x y a b hx hy

/-- `Bv{width}.Xor` evaluates to bitwise exclusive-or whenever that width is
registered in `Core.Factory`. -/
theorem coreEval_bvXor
    (width : Nat) (hF : Core.Factory[s!"Bv{width}.Xor"]? = some (bvXor width).func)
    (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec width)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () width a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () width b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bvXor width).opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () width (BitVec.xor a b)) := by
  exact coreEval_bvBinary width ⟨s!"Bv{width}.Xor", ()⟩ BitVec.xor
    hF σ x y a b hx hy

/-! ## Bv16 compatibility wrappers -/

/-- `Bv16.ULe` evaluates to unsigned comparison. -/
theorem coreEval_bv16ULe (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () bv16ULeFunc.opExpr x) y)
      = some (Lambda.LExpr.boolConst () (BitVec.ule a b)) := by
  change Lambda.LExpr.evalFully Core.Factory σ
      (.app () (.app ()
        (bvPredicate 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule).opExpr x) y) = _
  have hF : Core.Factory[(⟨"Bv16.ULe", ()⟩ : CoreIdent).name]? =
      some (bvPredicate 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule).func := by
    simpa only [show bv16ULeFunc =
      bvPredicate 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule from rfl] using coreFactory_bv16ULe
  exact coreEval_bvPredicate 16 ⟨"Bv16.ULe", ()⟩ BitVec.ule hF σ x y a b hx hy

/-- `Bv16.And` evaluates to bitwise conjunction. -/
theorem coreEval_bv16And (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ (.app () (.app () bv16AndFunc.opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () 16 (BitVec.and a b)) := by
  change Lambda.LExpr.evalFully Core.Factory σ
      (.app () (.app () (bvBinary 16 ⟨"Bv16.And", ()⟩ BitVec.and).opExpr x) y) = _
  have hF : Core.Factory[(⟨"Bv16.And", ()⟩ : CoreIdent).name]? =
      some (bvBinary 16 ⟨"Bv16.And", ()⟩ BitVec.and).func := by
    simpa only [show bv16AndFunc =
      bvBinary 16 ⟨"Bv16.And", ()⟩ BitVec.and from rfl] using coreFactory_bv16And
  exact coreEval_bvBinary 16 ⟨"Bv16.And", ()⟩ BitVec.and hF σ x y a b hx hy

/-- `Bv16.Xor` evaluates to bitwise exclusive-or. -/
theorem coreEval_bv16Xor (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ (.app () (.app () bv16XorFunc.opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () 16 (BitVec.xor a b)) := by
  change Lambda.LExpr.evalFully Core.Factory σ
      (.app () (.app () (bvBinary 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor).opExpr x) y) = _
  have hF : Core.Factory[(⟨"Bv16.Xor", ()⟩ : CoreIdent).name]? =
      some (bvBinary 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor).func := by
    simpa only [show bv16XorFunc =
      bvBinary 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor from rfl] using coreFactory_bv16Xor
  exact coreEval_bvBinary 16 ⟨"Bv16.Xor", ()⟩ BitVec.xor hF σ x y a b hx hy

/-! ## Width-parametric interpretation -/

/-- A registered bitvector predicate's concrete evaluator maps two width-`width`
bitvector literals to the Boolean literal obtained by applying its Lean operation. -/
private theorem concreteEval_bvPredicate
    (width : Nat) (name : CoreIdent) (op : BitVec width → BitVec width → Bool)
    (ceval : Unit → List Expression.Expr → Option Expression.Expr)
    (hc : (bvPredicate width name op).func.concreteEval = some ceval)
    (a b : BitVec width) :
    ceval () [.bitvecConst () width a, .bitvecConst () width b]
      = some (.boolConst () (op a b)) := by
  have hda : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width a : Expression.Expr) = some a := by
    simp [Lambda.LExpr.denoteBitVec]
  have hdb : Lambda.LExpr.denoteBitVec width
      (Lambda.LExpr.bitvecConst () width b : Expression.Expr) = some b := by
    simp [Lambda.LExpr.denoteBitVec]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bitvec width)
      (ValTy := BitVec width) CoreLParams = Lambda.LExpr.denoteBitVec width := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool)
      (ValTy := Bool) CoreLParams = @Lambda.LExpr.boolConst CoreLParams.mono := rfl
  have key : (bvPredicate width name op).func.concreteEval.bind
      (fun ce => ce () [.bitvecConst () width a, .bitvecConst () width b])
      = some (.boolConst () (op a b)) := by
    simp only [bvPredicate, Lambda.binaryOp, Option.bind_some, hcev, hmk,
      hda, hdb, if_true]
  rw [hc, Option.bind_some] at key
  exact key

/-
Proof: consistency transfers the registered concrete evaluator equation to the
model interpretation; typed bitvector constants instantiate that equation at
an arbitrary width.
-/
/-- Any registered concrete bitvector predicate has its Lean semantics in every
consistent interpretation of `Core.Factory`, at any bitwidth. -/
private theorem bvPredicate_opInterp
    (width : Nat) (name : CoreIdent) (op : BitVec width → BitVec width → Bool)
    (model : Lambda.Interp Core.Factory)
    (hF : Core.Factory[name.name]? = some (bvPredicate width name op).func) :
    model.opInterp name.name
        (Lambda.LSort.mkArrow .bool [.bitvec width, .bitvec width]) = op := by
  have hmem : name.name ∈ Core.Factory :=
    Lambda.Factory.getElem?_some_implies_mem hF
  have hget : Core.Factory[name.name]'hmem = (bvPredicate width name op).func :=
    Lambda.Factory.getElem?_some_getElem hF
  have hsome : (Core.Factory[name.name]'hmem).concreteEval.isSome = true := by
    rw [hget]
    rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 name.name hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  funext a b
  have h_eval := concreteEval_bvPredicate width name op ceval h_ceval_eq a b
  have h_vt : Lambda.TyVarVal := fun _ => .bool
  have h_fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Lambda.Subst.empty
      [.bitvecConst () width a, .bitvecConst () width b]
      (.boolConst () (op a b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.bitvecConst () width a, .bitvecConst () width b]
      [Lambda.LMonoTy.bitvec width, Lambda.LMonoTy.bitvec width] :=
    .cons .const (.cons .const .nil)
  have h_result : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () (op a b)) .bool := .const
  have h_eq := h_inst h_args h_result
  change op a b = model.opInterp name.name
    (Lambda.LSort.mkArrow .bool [.bitvec width, .bitvec width]) a b at h_eq
  exact h_eq.symm

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

end Core

end -- public section

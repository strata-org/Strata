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

public section

/-! # Concrete bitvector evaluator properties

Fuel-level and `evalFully` laws for concrete bitvector operations on
`Core.Factory`. These facts expose the bitvector semantics needed by Hoare
proofs over translated Core programs.

Key results:
- `coreEval_bv16ULe`, `coreEval_bv16And`, and `coreEval_bv16Xor` evaluate
  unsigned comparison and bitwise operations;
- `eq_bitvecConst_of_eql_true` recovers equality with a bitvector constant.
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

/-! ## `Bv16.ULe` factory membership -/

set_option maxRecDepth 8000 in
/-- `Bv16.ULe` resolves in the concrete `Core.Factory` to `bv16ULeFunc`. -/
private theorem coreFactory_bv16ULe :
    (Core.Factory)["Bv16.ULe"]? = some (bv16ULeFunc).func := by
  have hname : (bv16ULeFunc).func.name.name = "Bv16.ULe" := rfl
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : (bv16ULeFunc).func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨bv16ULeFunc, ?_, rfl⟩
    unfold WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList, List.mem_append, List.mem_cons]
    grind
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory, ← hname]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-! ## One-step reduction of `Bv16.ULe` on bitvector values -/

/-- If `x` and `y` reduce to 16-bit bitvector values `a`, `b` at fuel `n`, then the
    `Bv16.ULe x y` application reduces to `boolConst (BitVec.ule a b)` at fuel `n+1`. -/
private theorem eval_bv16ULe_value_of_bvs
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr)
    (n : Nat) (a b : BitVec 16)
    (hF : f["Bv16.ULe"]? = some (bv16ULeFunc).func)
    (hx : Lambda.LExpr.eval n f σ x = (Lambda.LExpr.bitvecConst () 16 a, .value true))
    (hy : Lambda.LExpr.eval n f σ y = (Lambda.LExpr.bitvecConst () 16 b, .value true)) :
    Lambda.LExpr.eval (n + 1) f σ
        (.app () (.app () (bv16ULeFunc).opExpr x) y)
      = (Lambda.LExpr.boolConst () (BitVec.ule a b), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (bv16ULeFunc).opExpr x) y)
      = some ((bv16ULeFunc).opExpr, [x, y], (bv16ULeFunc).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      bv16ULeFunc, Lambda.binaryOp]
    rw [hF]
    simp [bv16ULeFunc, Lambda.binaryOp]
  have hcan : Lambda.LExpr.isCanonicalValue f
      (.app () (.app () (bv16ULeFunc).opExpr x) y) = false := by
    simp only [Lambda.LExpr.isCanonicalValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      bv16ULeFunc, Lambda.binaryOp]
    rw [hF]
    simp [bv16ULeFunc, Lambda.binaryOp]
  have hcanbv : ∀ (a : BitVec 16),
      Lambda.LExpr.isCanonicalValue f (Lambda.LExpr.bitvecConst () 16 a : Expression.Expr) = true := by
    intro a; simp [Lambda.LExpr.isCanonicalValue, Lambda.LExpr.bitvecConst]
  have hcanb : ∀ (b : Bool),
      Lambda.LExpr.isCanonicalValue f (Lambda.LExpr.boolConst () b : Expression.Expr) = true := by
    intro b; simp [Lambda.LExpr.isCanonicalValue, Lambda.LExpr.boolConst]
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by simp [hcan]), hcall]
  simp only [bv16ULeFunc, Lambda.binaryOp]
  rw [dif_neg (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfCanonical #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [Lambda.LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bitvec 16) (ValTy := BitVec 16) CoreLParams
      = Lambda.LExpr.denoteBitVec 16 := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool) (ValTy := Bool) CoreLParams
      = @Lambda.LExpr.boolConst CoreLParams.mono := rfl
  simp only [hcev, hmk]
  have hda : Lambda.LExpr.denoteBitVec 16 (Lambda.LExpr.bitvecConst () 16 a : Expression.Expr) = some a := by
    simp [Lambda.LExpr.denoteBitVec]
  have hdb : Lambda.LExpr.denoteBitVec 16 (Lambda.LExpr.bitvecConst () 16 b : Expression.Expr) = some b := by
    simp [Lambda.LExpr.denoteBitVec]
  rw [if_pos (by simp [hcanbv])]
  simp only [hda, hdb]
  simp only [if_true]
  rw [Lambda.eval_canonical_identity n f σ _ (hcanb _)]
  simp [Lambda.LExpr.combineEvalResValueFlag_eq_pair, Lambda.LExpr.EvalResult.combineValueFlag]

/-! ## `evalFully`-level wrappers (used by the contract proofs) -/

/-- **`bv16.uLe(x, y)` on `Core.Factory`.** If `x`, `y` fully evaluate to 16-bit
    bitvector values `a`, `b`, the comparison fully evaluates to `boolConst (ule a b)`. -/
theorem coreEval_bv16ULe (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x = some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y = some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bv16ULeFunc).opExpr x) y)
      = some (Lambda.LExpr.boolConst () (BitVec.ule a b)) := by
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  obtain ⟨ny, hny, _⟩ := Lambda.evalFully_some_exists Core.Factory σ y _ hy
  have hx_max := Lambda.eval_value_true_mono_le Core.Factory σ nx (max nx ny)
    (Nat.le_max_left _ _) x _ hnx
  have hy_max := Lambda.eval_value_true_mono_le Core.Factory σ ny (max nx ny)
    (Nat.le_max_right _ _) y _ hny
  have hstep := eval_bv16ULe_value_of_bvs Core.Factory σ x y (max nx ny) a b
    coreFactory_bv16ULe hx_max hy_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

/-! ## Binary bitwise operations -/

/-- A generic 16-bit binary operation represented as a Lambda function. -/
private def bv16Binary (name : CoreIdent)
    (op : BitVec 16 → BitVec 16 → BitVec 16) : Lambda.WFLFunc CoreLParams :=
  Lambda.binaryOp (inTy := .bitvec 16) (outTy := .bitvec 16) name op
    (hInTy := by decide) (hOutTy := by decide) (h_precond := by simp)

set_option maxRecDepth 8000 in
/-- A fully applied generic Bv16 binary operation reduces by applying its Lean
operation to two bitvector values. -/
private theorem eval_bv16Binary_value
    (name : CoreIdent) (op : BitVec 16 → BitVec 16 → BitVec 16)
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr)
    (n : Nat) (a b : BitVec 16)
    (hF : f[name.name]? = some (bv16Binary name op).func)
    (hcan : Lambda.LExpr.isCanonicalValue f
      (.app () (.app () (bv16Binary name op).opExpr x) y) = false)
    (hx : Lambda.LExpr.eval n f σ x = (Lambda.LExpr.bitvecConst () 16 a, .value true))
    (hy : Lambda.LExpr.eval n f σ y = (Lambda.LExpr.bitvecConst () 16 b, .value true)) :
    Lambda.LExpr.eval (n + 1) f σ
        (.app () (.app () (bv16Binary name op).opExpr x) y)
      = (Lambda.LExpr.bitvecConst () 16 (op a b), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (bv16Binary name op).opExpr x) y)
      = some ((bv16Binary name op).opExpr, [x, y], (bv16Binary name op).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      bv16Binary, Lambda.binaryOp]
    rw [hF]
    simp [bv16Binary, Lambda.binaryOp]
  have hcanbv : ∀ (a : BitVec 16),
      Lambda.LExpr.isCanonicalValue f
        (Lambda.LExpr.bitvecConst () 16 a : Expression.Expr) = true := by
    intro a
    exact Lambda.isCanonicalValue_const_true f () (.bitvecConst 16 a)
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by simp [hcan]), hcall]
  simp only [bv16Binary, Lambda.binaryOp]
  rw [dif_neg (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfCanonical #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [Lambda.LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bitvec 16)
      (ValTy := BitVec 16) CoreLParams = Lambda.LExpr.denoteBitVec 16 := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bitvec 16)
      (ValTy := BitVec 16) CoreLParams =
        (fun m b => @Lambda.LExpr.bitvecConst CoreLParams.mono m 16 b) := rfl
  simp only [hcev, hmk]
  have hda : Lambda.LExpr.denoteBitVec 16
      (Lambda.LExpr.bitvecConst () 16 a : Expression.Expr) = some a := by
    simp [Lambda.LExpr.denoteBitVec]
  have hdb : Lambda.LExpr.denoteBitVec 16
      (Lambda.LExpr.bitvecConst () 16 b : Expression.Expr) = some b := by
    simp [Lambda.LExpr.denoteBitVec]
  rw [if_pos (by simp [hcanbv])]
  simp only [hda, hdb]
  simp only [if_true]
  rw [Lambda.eval_canonical_identity n f σ _ (hcanbv _)]
  simp [Lambda.LExpr.combineEvalResValueFlag_eq_pair,
    Lambda.LExpr.EvalResult.combineValueFlag]

/-- Lift the fuel-level generic Bv16 binary operation law to `evalFully`. -/
private theorem coreEval_bv16Binary
    (name : CoreIdent) (op : BitVec 16 → BitVec 16 → BitVec 16)
    (hF : Core.Factory[name.name]? = some (bv16Binary name op).func)
    (hcan : ∀ x y : Expression.Expr,
      Lambda.LExpr.isCanonicalValue Core.Factory
        (.app () (.app () (bv16Binary name op).opExpr x) y) = false)
    (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ
        (.app () (.app () (bv16Binary name op).opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () 16 (op a b)) := by
  obtain ⟨nx, hnx, _⟩ := Lambda.evalFully_some_exists Core.Factory σ x _ hx
  obtain ⟨ny, hny, _⟩ := Lambda.evalFully_some_exists Core.Factory σ y _ hy
  have hx_max := Lambda.eval_value_true_mono_le Core.Factory σ nx (max nx ny)
    (Nat.le_max_left _ _) x _ hnx
  have hy_max := Lambda.eval_value_true_mono_le Core.Factory σ ny (max nx ny)
    (Nat.le_max_right _ _) y _ hny
  have hstep := eval_bv16Binary_value name op Core.Factory σ x y (max nx ny) a b
    hF (hcan x y) hx_max hy_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

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

set_option maxRecDepth 8000 in
/-- A fully applied generic Bv16 binary operation is reducible rather than a
canonical partial application. -/
private theorem bv16Binary_not_canonical
    (name : CoreIdent) (op : BitVec 16 → BitVec 16 → BitVec 16)
    (hF : Core.Factory[name.name]? = some (bv16Binary name op).func)
    (x y : Expression.Expr) :
    Lambda.LExpr.isCanonicalValue Core.Factory
      (.app () (.app () (bv16Binary name op).opExpr x) y) = false := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) Core.Factory
      (.app () (.app () (bv16Binary name op).opExpr x) y) true
      = some ((bv16Binary name op).opExpr, [x, y], (bv16Binary name op).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      bv16Binary, Lambda.binaryOp]
    rw [hF]
    simp [bv16Binary, Lambda.binaryOp]
  rw [Lambda.LExpr.isCanonicalValue.eq_def]
  simp only
  split
  · rename_i fst args fn hc
    have heq : (fst, args, fn) =
        ((bv16Binary name op).opExpr, [x, y], (bv16Binary name op).func) :=
      Option.some.inj (hc.symm.trans hcall)
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hhead : (((bv16Binary name op).func.isConstr ||
        [x, y].length.blt (bv16Binary name op).func.inputs.length) : Bool) = false := by
      change (false || Nat.blt 2 2) = false
      rfl
    rw [hhead]
    rfl
  · rename_i hc
    rw [hc] at hcall

/-- `bv16.and(x, y)` evaluates to the bitwise conjunction of its operands. -/
theorem coreEval_bv16And (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ (.app () (.app () bv16AndFunc.opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () 16 (BitVec.and a b)) := by
  change Lambda.LExpr.evalFully Core.Factory σ
      (.app () (.app () (bv16Binary ⟨"Bv16.And", ()⟩ BitVec.and).opExpr x) y) = _
  have hF : Core.Factory[(⟨"Bv16.And", ()⟩ : CoreIdent).name]? =
      some (bv16Binary ⟨"Bv16.And", ()⟩ BitVec.and).func := by
    simpa only [show bv16AndFunc =
      bv16Binary ⟨"Bv16.And", ()⟩ BitVec.and from rfl] using coreFactory_bv16And
  exact coreEval_bv16Binary ⟨"Bv16.And", ()⟩ BitVec.and hF
    (bv16Binary_not_canonical ⟨"Bv16.And", ()⟩ BitVec.and hF) σ x y a b hx hy

/-- `bv16.xor(x, y)` evaluates to the bitwise exclusive-or of its operands. -/
theorem coreEval_bv16Xor (σ : CoreStore) (x y : Expression.Expr) (a b : BitVec 16)
    (hx : Lambda.LExpr.evalFully Core.Factory σ x =
      some (Lambda.LExpr.bitvecConst () 16 a))
    (hy : Lambda.LExpr.evalFully Core.Factory σ y =
      some (Lambda.LExpr.bitvecConst () 16 b)) :
    Lambda.LExpr.evalFully Core.Factory σ (.app () (.app () bv16XorFunc.opExpr x) y)
      = some (Lambda.LExpr.bitvecConst () 16 (BitVec.xor a b)) := by
  change Lambda.LExpr.evalFully Core.Factory σ
      (.app () (.app () (bv16Binary ⟨"Bv16.Xor", ()⟩ BitVec.xor).opExpr x) y) = _
  have hF : Core.Factory[(⟨"Bv16.Xor", ()⟩ : CoreIdent).name]? =
      some (bv16Binary ⟨"Bv16.Xor", ()⟩ BitVec.xor).func := by
    simpa only [show bv16XorFunc =
      bv16Binary ⟨"Bv16.Xor", ()⟩ BitVec.xor from rfl] using coreFactory_bv16Xor
  exact coreEval_bv16Binary ⟨"Bv16.Xor", ()⟩ BitVec.xor hF
    (bv16Binary_not_canonical ⟨"Bv16.Xor", ()⟩ BitVec.xor hF) σ x y a b hx hy



end Core

end -- public section

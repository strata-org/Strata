/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.Semantics
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Util.FuncAttr
public import Strata.Languages.Core.FactoryWF

/-!
## `Imperative.WellFormedSemanticEval*` instances for Core

This module supplies the `WellFormedSemanticEvalVal`/`Var`/`ExprCongr`/`Bool`
proofs against the Core evaluator (`Lambda.LExpr.evalFully`).
At the end of the file there is the full instantiation of `Imperative.WellFormedSemanticsEval`
which is a bundle of all well-formednesses of Core expression evaluator.
-/

---------------------------------------------------------------------

public section

namespace Core

open Imperative

@[expose] abbrev CoreEval := SemanticEval Expression
@[expose] abbrev CoreStore := SemanticStore Expression

/-- `Lambda.LExpr.evalFully` only outputs canonical values (delegates to the
    generic `Lambda.evalFully_outputs_canonical`). -/
theorem Lambda.LExpr.evalFully_outputs_canonical (f : Expression.Factory)
    (σ : CoreStore) (e : Expression.Expr) (v' : Expression.Expr)
    (heval : Lambda.LExpr.evalFully f σ e = some v') :
    Lambda.LExpr.isCanonicalValue f v' = true :=
  Lambda.evalFully_outputs_canonical f σ e v' heval

/-- The Core evaluator's value behavior is well-formed: `evalFully` returns only
    canonical values on well-formed stores, and is the identity on values. -/
@[expose] def coreEvaluator_WellFormedSemanticEvalVal (f : Expression.Factory) :
    WellFormedSemanticEvalVal (P := Expression) f where
  outputsAreValues := fun v v' σ _hwfs heval =>
    Lambda.LExpr.evalFully_outputs_canonical f σ v v' heval
  identityOnValues := fun v' σ hv => by
    simp only [HasVal.value] at hv
    show Lambda.LExpr.evalFully f σ v' = some v'
    exact Lambda.evalFully_value_identity f σ v' hv

/-- The Core evaluator resolves free variables via the store: evaluating a free
    variable yields its store binding (on well-formed stores). -/
@[expose] def coreEvaluator_WellFormedSemanticEvalVar (f : Expression.Factory) :
    WellFormedSemanticEvalVar (P := Expression) f := by
  intro e v σ hwfs hget
  cases e with
  | fvar m x ty =>
    simp only [HasFvar.getFvar] at hget; cases hget
    show Lambda.LExpr.evalFully f σ (.fvar m v ty) = σ v
    exact Lambda.evalFully_fvar_store f σ (fun x val hx => hwfs x val hx) m v ty
  | _ => simp [HasFvar.getFvar] at hget

/-- The Core evaluator satisfies expression congruence: if two well-formed stores
    agree on all free variables of an expression, `evalFully` produces the same
    result. This is the `WellFormedSemanticEvalExprCongr` property for Core. -/
theorem coreEvaluator_WellFormedSemanticEvalExprCongr (f : Expression.Factory)
    (hWF : Lambda.FactoryWF f) :
    WellFormedSemanticEvalExprCongr (P := Expression) f := by
  intro e σ σ' _h_wfs h_wfs' hagree
  exact Lambda.evalFully_env_congr
    (fun a b h => by cases a; cases b; simp_all)
    f σ σ' hWF
    (fun x v hx => Lambda.isCanonicalValue_getVars_nil f v (h_wfs' x v hx))
    e hagree

/-- The Core evaluator is monotone under store extension: a successful `evalFully`
    is preserved when the store retains every binding it held. This is the
    `WellFormedSemanticEvalMono` property for Core, discharged by the concrete
    `Lambda.evalFully_mono`. -/
theorem coreEvaluator_WellFormedSemanticEvalMono (f : Expression.Factory) :
    WellFormedSemanticEvalMono (P := Expression) f :=
  fun e v σ σ' hext heval => Lambda.evalFully_mono f σ σ' hext e v heval

open Lambda in
/-- Characterization of `eval (n+1) (not e)` as a `.value true` result:  it is
    `.value true` iff `eval n e` was itself `.value true` on a `boolConst β`.
    (This mirrors the old `.value`-flavored iff, but the new
    `.value b`/`combineValueFlag` machinery forces `argsAllFull = true`, i.e. the
    inner evaluation must itself have been fully reduced.) -/
theorem eval_boolNot_value_iff
    (f : Expression.Factory) (σ : CoreStore) (e : Expression.Expr) (n : Nat) (v : Expression.Expr)
    (hBN : f["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func) :
    Lambda.LExpr.eval (n + 1) f σ (.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e)
        = (v, .value true)
      ↔ ∃ β : Bool, Lambda.LExpr.eval n f σ e = (Lambda.LExpr.boolConst () β, .value true) ∧
          v = Lambda.LExpr.boolConst () (!β) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e)
      = some ((Lambda.boolNotFunc (T := CoreLParams)).opExpr, [e],
              (Lambda.boolNotFunc (T := CoreLParams)).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.boolNotFunc, Lambda.unaryOp]
    rw [hBN]
    simp [Lambda.boolNotFunc, Lambda.unaryOp]
  have hcan : Lambda.LExpr.isCanonicalValue f
      (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e) = false := by
    simp only [Lambda.LExpr.isCanonicalValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.boolNotFunc, Lambda.unaryOp]
    rw [hBN]
    simp [Lambda.boolNotFunc, Lambda.unaryOp]
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by simp [hcan]), hcall]
  simp only [Lambda.boolNotFunc, Lambda.unaryOp]
  rw [dif_neg (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfCanonical #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.or_false, Bool.and_true]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.bool) (ValTy := Bool) CoreLParams
      = Lambda.LExpr.denoteBool := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool) (ValTy := Bool) CoreLParams
      = @Lambda.LExpr.boolConst CoreLParams.mono := rfl
  simp only [hcev, hmk]
  have hdbc : ∀ (m : Unit) (b : Bool),
      Lambda.LExpr.denoteBool (Lambda.LExpr.boolConst m b : Expression.Expr) = some b := by
    intro m b; rfl
  have hcanb : ∀ (m : Unit) (b : Bool),
      Lambda.LExpr.isCanonicalValue f (Lambda.LExpr.boolConst m b : Expression.Expr) = true := by
    intro m b; simp [Lambda.LExpr.isCanonicalValue, Lambda.LExpr.boolConst]
  have hdb : ∀ (x : Expression.Expr) (b : Bool),
      Lambda.LExpr.denoteBool x = some b → x = Lambda.LExpr.boolConst () b := by
    intro x b hx
    cases x with
    | const m c =>
      cases c with
      | boolConst b0 =>
        simp only [Lambda.LExpr.denoteBool, Option.some.injEq] at hx
        subst hx; rfl
      | _ => simp [Lambda.LExpr.denoteBool] at hx
    | _ => simp [Lambda.LExpr.denoteBool] at hx
  by_cases hcv : Lambda.LExpr.isCanonicalValue f (Lambda.LExpr.eval n f σ e).fst = true
  · rw [if_pos hcv]
    rcases hd : (Lambda.LExpr.eval n f σ e).fst.denoteBool with _ | β
    · simp only []
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨β, hβ, _⟩
        have hβfst : (Lambda.LExpr.eval n f σ e).fst = Lambda.LExpr.boolConst () β := by
          rw [hβ]
        rw [hβfst, hdbc () β] at hd
        exact absurd hd (by simp)
    · simp only []
      rw [Lambda.eval_canonical_identity n f σ _ (hcanb _ _)]
      simp only [Lambda.LExpr.combineEvalResValueFlag_eq_pair,
        Lambda.LExpr.EvalResult.combineValueFlag]
      constructor
      · intro h
        simp only [Prod.mk.injEq] at h
        obtain ⟨hfst, hsnd⟩ := h
        have hvt : (Lambda.LExpr.eval n f σ e).snd.isValueTrue = true := by
          cases hsplit : (Lambda.LExpr.eval n f σ e).snd with
          | value b =>
            cases b with
            | true => rfl
            | false =>
              rw [hsplit] at hsnd
              simp [Lambda.LExpr.EvalResult.isValueTrue] at hsnd
          | outOfFuel =>
            rw [hsplit] at hsnd
            simp [Lambda.LExpr.EvalResult.isValueTrue] at hsnd
          | nonvalue =>
            rw [hsplit] at hsnd
            simp [Lambda.LExpr.EvalResult.isValueTrue] at hsnd
        have hsndVal : (Lambda.LExpr.eval n f σ e).snd = .value true := by
          cases hsplit : (Lambda.LExpr.eval n f σ e).snd with
          | value b =>
            cases b with
            | true => rfl
            | false => rw [hsplit] at hvt; simp [Lambda.LExpr.EvalResult.isValueTrue] at hvt
          | outOfFuel => rw [hsplit] at hvt; simp [Lambda.LExpr.EvalResult.isValueTrue] at hvt
          | nonvalue => rw [hsplit] at hvt; simp [Lambda.LExpr.EvalResult.isValueTrue] at hvt
        refine ⟨β, ?_, hfst.symm⟩
        have hpair : Lambda.LExpr.eval n f σ e =
            ((Lambda.LExpr.eval n f σ e).fst, (Lambda.LExpr.eval n f σ e).snd) := by rfl
        rw [hpair, hdb _ _ hd, hsndVal]
      · rintro ⟨β', hβ', hv⟩
        have hβ'fst : (Lambda.LExpr.eval n f σ e).fst = Lambda.LExpr.boolConst () β' := by
          rw [hβ']
        have hβ'snd : (Lambda.LExpr.eval n f σ e).snd = .value true := by
          rw [hβ']
        rw [hβ'fst, hdbc () β'] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        rw [hv]
        simp [hβ'snd, Lambda.LExpr.EvalResult.isValueTrue]
  · rw [if_neg hcv]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨β, hβ, _⟩
      have hβfst : (Lambda.LExpr.eval n f σ e).fst = Lambda.LExpr.boolConst () β := by
        rw [hβ]
      rw [hβfst, hcanb () β] at hcv
      exact absurd hcv (by simp)

open Lambda in
/-- The Core evaluator (`evalFully`) is well-formed with respect to boolean
    negation: `e` evaluates to `true` iff `not e` evaluates to `false`, and
    dually.  This holds given only that `Bool.Not` resolves in the factory to
    the `boolNotFunc` (`hBN`).

    The reverse direction (`not e ↦ β ⟹ e ↦ !β`) uses the fact that
    `.value true` witnesses are stable under `eval`: monotonicity
    (`eval_value_true_mono`) implies that any `.value true` witness produces
    the SAME result as `evalFully` (via `evalFully_of_value_true`).  -/
theorem coreEvaluator_WellFormedSemanticEvalBool (f : Expression.Factory)
    (hBN : f["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func) :
    Imperative.WellFormedSemanticEvalBool (P := Expression) f := by
  intro σ e
  have hcanT : Lambda.LExpr.isCanonicalValue f Core.true = true := by
    simp [Core.true, Lambda.LExpr.boolConst, Lambda.LExpr.isCanonicalValue]
  have hcanF : Lambda.LExpr.isCanonicalValue f Core.false = true := by
    simp [Core.false, Lambda.LExpr.boolConst, Lambda.LExpr.isCanonicalValue]
  have hevT : Lambda.LExpr.evalFully f σ Core.true = some Core.true :=
    Lambda.evalFully_value_identity f σ Core.true hcanT
  have hevF : Lambda.LExpr.evalFully f σ Core.false = some Core.false :=
    Lambda.evalFully_value_identity f σ Core.false hcanF
  have hsTF : (some Core.true : Option Expression.Expr) ≠ some Core.false := by
    simp [Core.true, Core.false, Lambda.LExpr.boolConst]
  have hsFT : (some Core.false : Option Expression.Expr) ≠ some Core.true := by
    simp [Core.true, Core.false, Lambda.LExpr.boolConst]
  have hApp : ∀ (e0 : Expression.Expr),
      (Lambda.LExpr.evalFully f σ e0 = some Core.true ↔
        Lambda.LExpr.evalFully f σ
          (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
            = some Core.false) ∧
      (Lambda.LExpr.evalFully f σ e0 = some Core.false ↔
        Lambda.LExpr.evalFully f σ
          (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
            = some Core.true) := by
    intro e0
    have hcanA : Lambda.LExpr.isCanonicalValue f
        (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0) = false := by
      simp only [Lambda.LExpr.isCanonicalValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
        Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
        Lambda.boolNotFunc, Lambda.unaryOp]
      rw [hBN]
      simp [Lambda.boolNotFunc, Lambda.unaryOp]
    have hFwd : ∀ (β : Bool) (n : Nat),
        Lambda.LExpr.eval n f σ e0 = (Lambda.LExpr.boolConst () β, .value true) →
        (∀ k, k < n → (Lambda.LExpr.eval k f σ e0).snd ≠ .value true) →
        Lambda.LExpr.evalFully f σ
          (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
            = some (Lambda.LExpr.boolConst () (!β)) := by
      intro β n hn hlt
      have hstep : Lambda.LExpr.eval (n + 1) f σ
          (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
            = (Lambda.LExpr.boolConst () (!β), .value true) :=
        (eval_boolNot_value_iff f σ e0 n _ hBN).mpr ⟨β, hn, rfl⟩
      have hnotlt : ∀ k, k < n + 1 →
          (Lambda.LExpr.eval k f σ
            (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)).snd
              ≠ .value true := by
        intro k hk
        cases k with
        | zero => simp [Lambda.LExpr.eval, hcanA]
        | succ j =>
          intro hval
          have hpair : Lambda.LExpr.eval (j + 1) f σ
              (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
                = ((Lambda.LExpr.eval (j + 1) f σ
                    (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)).fst,
                   .value true) := by
            rw [← hval]
          obtain ⟨β', hβ'pair, _⟩ := (eval_boolNot_value_iff f σ e0 j _ hBN).mp hpair
          exact hlt j (by omega) (by rw [hβ'pair])
      exact Lambda.evalFullyAux_of_eval f σ _ (n + 1) _ hstep 0 (by omega)
        (fun k _ hk => hnotlt k hk)
    have hRev' : ∀ (β_out : Bool),
        Lambda.LExpr.evalFully f σ
          (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
            = some (Lambda.LExpr.boolConst () β_out) →
        Lambda.LExpr.evalFully f σ e0 =
          some (Lambda.LExpr.boolConst () (!β_out)) := by
      intro β_out h
      obtain ⟨m, hm, _⟩ :=
        Lambda.evalFully_some_exists f σ _ (Lambda.LExpr.boolConst () β_out) h
      cases m with
      | zero =>
        exfalso
        have hfst : (Lambda.LExpr.eval 0 f σ
          (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)).fst
            = Lambda.LExpr.boolConst () β_out := by rw [hm]
        simp only [Lambda.LExpr.eval, hcanA] at hfst
        simp [Lambda.LExpr.boolConst] at hfst
      | succ j =>
        obtain ⟨β, hβpair, hval⟩ := (eval_boolNot_value_iff f σ e0 j _ hBN).mp hm
        have hβeq : β_out = !β := by
          have := hval
          simp [Lambda.LExpr.boolConst] at this
          exact this
        subst hβeq
        have hbb : (!(!β)) = β := by cases β <;> rfl
        rw [hbb]
        exact Lambda.evalFully_of_value_true f σ e0 j (Lambda.LExpr.boolConst () β) hβpair
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨n, hn, hlt⟩ := Lambda.evalFully_some_exists f σ e0 Core.true h
      have hpair : Lambda.LExpr.eval n f σ e0 =
          (Lambda.LExpr.boolConst () true, .value true) := by
        have := hn
        simp only [Core.true, Lambda.LExpr.boolConst] at this
        exact this
      have := hFwd true n hpair (fun k hk => hlt k hk)
      simpa [Core.false, Lambda.LExpr.boolConst] using this
    · have := hRev' false (by simpa [Core.false, Lambda.LExpr.boolConst] using h)
      simpa [Core.true, Lambda.LExpr.boolConst] using this
    · obtain ⟨n, hn, hlt⟩ := Lambda.evalFully_some_exists f σ e0 Core.false h
      have hpair : Lambda.LExpr.eval n f σ e0 =
          (Lambda.LExpr.boolConst () false, .value true) := by
        have := hn
        simp only [Core.false, Lambda.LExpr.boolConst] at this
        exact this
      have := hFwd false n hpair (fun k hk => hlt k hk)
      simpa [Core.true, Lambda.LExpr.boolConst] using this
    · have := hRev' true (by simpa [Core.true, Lambda.LExpr.boolConst] using h)
      simpa [Core.false, Lambda.LExpr.boolConst] using this
  cases e with
  | const m c =>
    cases c with
    | boolConst b =>
      cases b with
      | true =>
        exact ⟨⟨fun _ => hevF, fun _ => hevT⟩,
               ⟨fun h => absurd (hevT.symm.trans h) hsTF,
                fun h => absurd (hevF.symm.trans h) hsFT⟩⟩
      | false =>
        exact ⟨⟨fun h => absurd (hevF.symm.trans h) hsFT,
                fun h => absurd (hevT.symm.trans h) hsTF⟩,
               ⟨fun _ => hevT, fun _ => hevF⟩⟩
    | intConst i => exact hApp _
    | strConst s => exact hApp _
    | realConst r => exact hApp _
    | bitvecConst n bv => exact hApp _
  | op m o ty => exact hApp _
  | bvar m i => exact hApp _
  | fvar m x ty => exact hApp _
  | abs m pn ty b => exact hApp _
  | quant m k pn ty tr b => exact hApp _
  | app m fn arg => exact hApp _
  | ite m cc t el => exact hApp _
  | eq m e1 e2 => exact hApp _

set_option maxRecDepth 8000 in
/-- `Bool.Not` resolves in the concrete `Core.Factory` to `boolNotFunc`. -/
theorem coreFactory_boolNot :
    (Core.Factory)["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func := by
  have hname : (Lambda.boolNotFunc (T := CoreLParams)).func.name.name = "Bool.Not" := rfl
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : (Lambda.boolNotFunc (T := CoreLParams)).func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.boolNotFunc (T := CoreLParams), ?_, rfl⟩
    unfold WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList,
      List.mem_append, List.mem_cons, or_true, true_or]
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory, ← hname]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-- Specialization of `coreEvaluator_WellFormedSemanticEvalBool` to the concrete
    `Core.Factory`. -/
theorem coreFactory_WellFormedSemanticEvalBool :
    Imperative.WellFormedSemanticEvalBool (P := Expression) Core.Factory :=
  coreEvaluator_WellFormedSemanticEvalBool Core.Factory coreFactory_boolNot



/-!
## `WellFormedSemanticEvalInt` for Core
-/

open Lambda in
/-- Sufficient condition for `eval (n+1)` on `Int.Lt x y` to reduce to a
    concrete `boolConst`: when both `x` and `y` reduce to integer numerals at
    fuel `n` with `.value true`, then the outer application reduces to
    `boolConst (a < b)` at fuel `n+1`. -/
theorem eval_intLt_value_of_numerals
    (f : Expression.Factory) (σ : CoreStore) (x y : Expression.Expr)
    (n : Nat) (a b : Int)
    (hILt : f["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func)
    (hx : Lambda.LExpr.eval n f σ x = (Lambda.LExpr.intConst () a, .value true))
    (hy : Lambda.LExpr.eval n f σ y = (Lambda.LExpr.intConst () b, .value true)) :
    Lambda.LExpr.eval (n + 1) f σ
        (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y)
      = (Lambda.LExpr.boolConst () (decide (a < b)), .value true) := by
  have hcall : Lambda.Factory.callOfLFunc (T := CoreLParams) f
      (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y)
      = some ((Lambda.intLtFunc (T := CoreLParams)).opExpr, [x, y],
              (Lambda.intLtFunc (T := CoreLParams)).func) := by
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go,
      Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr, Lambda.intLtFunc, Lambda.binaryOp]
    rw [hILt]
    simp [Lambda.intLtFunc, Lambda.binaryOp]
  have hcan : Lambda.LExpr.isCanonicalValue f
      (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y) = false := by
    simp only [Lambda.LExpr.isCanonicalValue, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr,
      Lambda.intLtFunc, Lambda.binaryOp]
    rw [hILt]
    simp [Lambda.intLtFunc, Lambda.binaryOp]
  have hcani : ∀ (a : Int),
      Lambda.LExpr.isCanonicalValue f (Lambda.LExpr.intConst () a : Expression.Expr) = true := by
    intro a; simp [Lambda.LExpr.isCanonicalValue, Lambda.LExpr.intConst]
  have hcanb : ∀ (b : Bool),
      Lambda.LExpr.isCanonicalValue f (Lambda.LExpr.boolConst () b : Expression.Expr) = true := by
    intro b; simp [Lambda.LExpr.isCanonicalValue, Lambda.LExpr.boolConst]
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by simp [hcan]), hcall]
  simp only [Lambda.intLtFunc, Lambda.binaryOp]
  rw [dif_neg (by simp)]
  have hf1 : Strata.DL.Util.FuncAttr.findEvalIfConstr #[] = none := by decide
  have hf2 : Strata.DL.Util.FuncAttr.findEvalIfCanonical #[] = none := by decide
  simp only [hf1, hf2, List.map, List.all, Bool.and_true]
  rw [hx, hy]
  simp only [Lambda.LExpr.EvalResult.isValueTrue, Bool.and_true]
  have hcev : Lambda.LambdaLeanType.cevalTy (ty := Lambda.LMonoTy.int) (ValTy := Int) CoreLParams
      = Lambda.LExpr.denoteInt := rfl
  have hmk : Lambda.LambdaLeanType.mkConst (ty := Lambda.LMonoTy.bool) (ValTy := Bool) CoreLParams
      = @Lambda.LExpr.boolConst CoreLParams.mono := rfl
  simp only [hcev, hmk]
  have hdenote : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () a : Expression.Expr) = some a := rfl
  have hdenote' : Lambda.LExpr.denoteInt (Lambda.LExpr.intConst () b : Expression.Expr) = some b := rfl
  rw [if_pos (by simp [hcani])]
  simp only [hdenote, hdenote']
  simp only [if_true]
  rw [Lambda.eval_canonical_identity n f σ _ (hcanb _)]
  simp [Lambda.LExpr.combineEvalResValueFlag_eq_pair, Lambda.LExpr.EvalResult.combineValueFlag]

open Lambda in
/-- The Core evaluator satisfies `WellFormedSemanticEvalInt` when the factory
    resolves `Int.Lt` to `intLtFunc`. -/
theorem coreEvaluator_WellFormedSemanticEvalInt (f : Expression.Factory)
    (hILt : f["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func) :
    Imperative.WellFormedSemanticEvalInt (P := Expression) f where
  ltReduces := by
    intro σ x y nx ny hx hnx hy hny
    -- Extract that nx = .intConst _ a, ny = .intConst _ b from isNumeral.
    have hnx_shape : ∃ a : Int, nx = Lambda.LExpr.intConst () a := by
      cases nx with
      | const m c =>
        cases c with
        | intConst i => exact ⟨i, rfl⟩
        | _ => simp [Core.isNumeral, HasInt.isNumeral] at hnx
      | _ => simp [Core.isNumeral, HasInt.isNumeral] at hnx
    have hny_shape : ∃ b : Int, ny = Lambda.LExpr.intConst () b := by
      cases ny with
      | const m c =>
        cases c with
        | intConst i => exact ⟨i, rfl⟩
        | _ => simp [Core.isNumeral, HasInt.isNumeral] at hny
      | _ => simp [Core.isNumeral, HasInt.isNumeral] at hny
    obtain ⟨a, rfl⟩ := hnx_shape
    obtain ⟨b, rfl⟩ := hny_shape
    -- Now obtain concrete fuel witnesses for the eval reductions.
    obtain ⟨nx', hx', _⟩ := Lambda.evalFully_some_exists f σ x _ hx
    obtain ⟨ny', hy', _⟩ := Lambda.evalFully_some_exists f σ y _ hy
    -- Fuel monotonicity: lift each eval to any ≥ fuel.
    have hmono : ∀ (e : Expression.Expr) (v : Expression.Expr) (m d : Nat),
        Lambda.LExpr.eval m f σ e = (v, .value true) →
        Lambda.LExpr.eval (m + d) f σ e = (v, .value true) := by
      intro e v m d he
      induction d with
      | zero => simpa using he
      | succ d' ih => exact Lambda.eval_value_true_mono f σ _ _ _ ih
    obtain ⟨dx, hdx⟩ :=
      Nat.exists_eq_add_of_le (Nat.le_max_left nx' ny' : nx' ≤ max nx' ny')
    obtain ⟨dy, hdy⟩ :=
      Nat.exists_eq_add_of_le (Nat.le_max_right nx' ny' : ny' ≤ max nx' ny')
    have hx_n : Lambda.LExpr.eval (max nx' ny') f σ x =
        (Lambda.LExpr.intConst () a, .value true) := by
      rw [hdx]; exact hmono x _ nx' dx hx'
    have hy_n : Lambda.LExpr.eval (max nx' ny') f σ y =
        (Lambda.LExpr.intConst () b, .value true) := by
      rw [hdy]; exact hmono y _ ny' dy hy'
    -- Apply the helper.
    have hstep : Lambda.LExpr.eval (max nx' ny' + 1) f σ
        (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y)
        = (Lambda.LExpr.boolConst () (decide (a < b)), .value true) :=
      eval_intLt_value_of_numerals f σ x y (max nx' ny') a b hILt hx_n hy_n
    -- Determine tt/ff based on the truth of `a < b`.
    by_cases hab : a < b
    · left
      have h_out : Lambda.LExpr.eval (max nx' ny' + 1) f σ
          (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y)
          = (Core.true, .value true) := by
        rw [hstep, decide_eq_true hab]; rfl
      show Lambda.LExpr.evalFully f σ
          (@HasIntOps.lt Core.Expression _ _ _ _ x y) = some Core.true
      change Lambda.LExpr.evalFully f σ
          (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y) = _
      exact Lambda.evalFully_of_value_true f σ _ _ _ h_out
    · right
      have h_out : Lambda.LExpr.eval (max nx' ny' + 1) f σ
          (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y)
          = (Core.false, .value true) := by
        rw [hstep, decide_eq_false hab]; rfl
      show Lambda.LExpr.evalFully f σ
          (@HasIntOps.lt Core.Expression _ _ _ _ x y) = some Core.false
      change Lambda.LExpr.evalFully f σ
          (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y) = _
      exact Lambda.evalFully_of_value_true f σ _ _ _ h_out

set_option maxRecDepth 8000 in
/-- `Int.Lt` resolves in the concrete `Core.Factory` to `intLtFunc`. -/
theorem coreFactory_intLt :
    (Core.Factory)["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func := by
  have hname : (Lambda.intLtFunc (T := CoreLParams)).func.name.name = "Int.Lt" := rfl
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : (Lambda.intLtFunc (T := CoreLParams)).func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.intLtFunc (T := CoreLParams), ?_, rfl⟩
    unfold WFFactoryArray
    simp only [Array.mem_def, Array.toList_appendList,
      List.mem_append, List.mem_cons, or_true, true_or]
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory, ← hname]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-- The Core evaluator commutes with variable renaming under target-definedness,
    discharged by the generic `Lambda.rename_commute`.  The `WellFormedStore σ'`
    guard supplies the canonical-store premise `rename_commute` consumes;
    `CoreIdent = Lambda.Identifier Unit`, so the name-injectivity premise holds
    trivially.  The generic `SubstVarsDefined`/`substStoreExpr` (phrased via
    `HasFvar.getFvar`) yield the Lambda-level `VarOnly`/`TargetsDefined`/`substStoreExpr`
    (phrased via the `fvar` pattern) for Core, because
    `HasFvar.getFvar (.fvar _ v _) = some v`. -/
theorem coreEvaluator_WellFormedSemanticEvalRename (f : Expression.Factory)
    (hWF : Lambda.FactoryWF f) :
    WellFormedSemanticEvalRename (P := Expression) f := by
  intro e σ' sm hwfs hVarsDef
  have hIdent : ∀ a b : CoreIdent, a.name = b.name → a = b := by
    intro a b h; cases a; cases b; cases h; rfl
  have hwfs' : ∀ x v, σ' x = some v → Lambda.LExpr.isCanonicalValue f v = true := by
    intro x v hx
    have := hwfs x v hx
    simpa only [HasVal.value] using this
  have hVar' : Lambda.VarOnly (Tbase := CoreLParams) sm := by
    intro k w hk
    obtain ⟨y, hy, _⟩ := hVarsDef k w hk
    cases w with
    | fvar m z ty => exact ⟨m, z, ty, rfl⟩
    | _ => simp only [HasFvar.getFvar, reduceCtorEq] at hy
  have hTgt' : Lambda.TargetsDefined (Tbase := CoreLParams) σ' sm := by
    intro k m x ty hk
    obtain ⟨y, hy, hdef⟩ := hVarsDef k (.fvar m x ty) hk
    simp only [HasFvar.getFvar, Option.some.injEq] at hy
    subst hy; exact hdef
  have hpb : substStoreExpr σ' sm = Lambda.substStoreExpr (Tbase := CoreLParams) σ' sm := by
    funext x
    unfold substStoreExpr Lambda.substStoreExpr
    cases hf : Map.find? sm x with
    | none => rfl
    | some w => cases w <;> rfl
  show Lambda.LExpr.evalFully f σ' (Lambda.LExpr.substFvars e sm)
      = Lambda.LExpr.evalFully f (substStoreExpr σ' sm) e
  rw [hpb]
  exact Lambda.rename_commute hIdent f σ' hWF hwfs' sm hVar' hTgt' e

/-!
## Instance of the full `WellFormedSemanticEval` bundle
--/

def coreEvaluator_WellFormedSemanticEval (f : Expression.Factory)
    (hWF : Lambda.FactoryWF f)
    (hBN : f["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    (hILt : f["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func) :
    Imperative.WellFormedSemanticEval (P := Expression) f where
  bool := coreEvaluator_WellFormedSemanticEvalBool f hBN
  val := coreEvaluator_WellFormedSemanticEvalVal f
  var := coreEvaluator_WellFormedSemanticEvalVar f
  exprCongr := coreEvaluator_WellFormedSemanticEvalExprCongr f hWF
  int := coreEvaluator_WellFormedSemanticEvalInt f hILt
  mono := coreEvaluator_WellFormedSemanticEvalMono f
  rename := coreEvaluator_WellFormedSemanticEvalRename f hWF

/-- Specialization of `coreEvaluator_WellFormedSemanticEval` to the concrete
    `Core.Factory`, which is unconditionally well-formed and resolves
    `Bool.Not` to `boolNotFunc` and `Int.Lt` to `intLtFunc`. -/
theorem coreFactory_WellFormedSemanticEval :
    Imperative.WellFormedSemanticEval (P := Expression) Core.Factory :=
  coreEvaluator_WellFormedSemanticEval Core.Factory Core.Factory_wf
    coreFactory_boolNot coreFactory_intLt

end Core

end -- public section

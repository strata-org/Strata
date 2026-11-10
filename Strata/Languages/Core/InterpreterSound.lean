/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter
public import Strata.DL.Imperative.InterpreterSound
import all Strata.Languages.Core.Interpreter
public import Strata.Languages.Core.InterpreterProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.FactoryProps
public import Strata.Languages.Core.InterpreterEvalSound

/-! # Core's eval-dependent soundness cases and soundness hypotheses

The engine evaluates expressions with the fuel-bounded `Core.evalBounded` on runtime stores,
while the reference relation's premise is `Expression.eval … = some v`, the denotational
evaluator (`Lambda.LExpr.denoteEval`) on semantic stores. The two are related by
`BoundedEvalSoundAt`: a value the bounded evaluator commits to denotes the reference value.

Key results:
* `stepStmtE_init_det`: a deterministic `.init` whose right-hand side the engine committed to a
  value is a `StepStmtE` reference step; `stepStmtE_init_det_of_evalFactoryWF` at factories
  meeting `EvalFactoryWF`.
* The `Imperative.InterpLangTyped` instance for `Expression`.
* `factoryWF_coreFactory`: `Core.Factory` satisfies the factory condition `FactoryWF` of the
  soundness theorems; `factoryWF_of_lambdaFactoryWF`: so does every factory that binds
  `"Bool.Not"` to `Lambda.boolNotFunc`. -/

namespace Core

open Imperative _root_.Lambda

public section

variable (EvalCmd : EvalCmdParamE Expression Command (Event Expression))
  (fuel : Nat) (F : Expression.Factory) (ρ : Imperative.IEnv Expression)

variable (π : String → Option Procedure)

/-- A deterministic `init x : ty := e` whose right-hand side the bounded evaluator reduces to
    `v`, with `v` a value of type `ty` and `σ'` the store that initializes `x` to `v`, is a
    reference `StepStmtE` step with no events to the store `σ'`, given that the bounded evaluator
    is sound at the factory (`BoundedEvalSoundAt`) and evaluation reads variables from the store
    (`WellFormedSemanticEvalVar`) there. -/
theorem stepStmtE_init_det (hEval : BoundedEvalSoundAt Expression F)
    (x : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr)
    (md : MetaData Expression) (r : Expression.Expr) (v : Expression.Val)
    (σ' : SemanticStore Expression)
    (hd : RStore.Denoting F ρ.store.get) (hrf : ρ.factory = F.factory)
    (varWF : WellFormedSemanticEvalVar (P := Expression) F)
    (heval : evalBounded fuel ρ.factory ρ.store.get e = some r) (hr : InterpLang.Denotes F r v)
    (hinit : InitState Expression (InterpLang.absStore F ρ.store.get) x v σ')
    (hty : HasVal.valueOfTy F v ty) :
    StepStmtE (P := Expression) (CmdT := Command) (EvalCommandE π)
      (.stmt (.cmd (.cmd (.init x ty (.det e) md))) (ρ.abs F)) []
      (.terminal { ρ.abs F with store := σ' }) := by
  obtain ⟨w, hw, hdw⟩ :=
    hEval fuel ρ.store.get _ e r (storeDenotes_absStore hd)
      (by show evalBounded _ F.factory _ _ = _; rw [← hrf]; exact heval)
  cases Option.some.inj (hdw.symm.trans hr)
  exact .step_cmd (.cmd_sem (.eval_init hw hinit hty varWF))

/-- A deterministic `init x : ty := e` whose right-hand side the bounded evaluator reduces to
    `v`, with `v` a value of type `ty` and `σ'` the store that initializes `x` to `v`, is a
    reference `StepStmtE` step with no events to the store `σ'`, given that the functions of the
    factory meet the conditions under which the bounded evaluator is sound (`EvalFactoryWF`, which
    `evalFactoryWF_of_userFuncs` gives program factories) and evaluation reads variables from the
    store (`WellFormedSemanticEvalVar`) there. -/
theorem stepStmtE_init_det_of_evalFactoryWF (hEvalF : EvalFactoryWF F.factory)
    (x : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr)
    (md : MetaData Expression) (r : Expression.Expr) (v : Expression.Val)
    (σ' : SemanticStore Expression)
    (hd : RStore.Denoting F ρ.store.get) (hrf : ρ.factory = F.factory)
    (varWF : WellFormedSemanticEvalVar (P := Expression) F)
    (heval : evalBounded fuel ρ.factory ρ.store.get e = some r) (hr : InterpLang.Denotes F r v)
    (hinit : InitState Expression (InterpLang.absStore F ρ.store.get) x v σ')
    (hty : HasVal.valueOfTy F v ty) :
    StepStmtE (P := Expression) (CmdT := Command) (EvalCommandE π)
      (.stmt (.cmd (.cmd (.init x ty (.det e) md))) (ρ.abs F)) []
      (.terminal { ρ.abs F with store := σ' }) :=
  stepStmtE_init_det fuel F ρ π (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) x ty e md r v σ' hd
    hrf varWF heval hr hinit hty

/-! ## Core's side of whole-run soundness

Core's instances of the generic whole-run soundness hypotheses. -/

instance : Imperative.InterpLangTyped Expression := ⟨replayValueOps_typedSound⟩

/-- A factory that binds `"Bool.Not"` to `Lambda.boolNotFunc` satisfies the factory condition `FactoryWF` of the soundness theorems: Boolean negation,
    variable lookup and agreement on stores that agree on an expression's free variables are
    well-formed there. -/
theorem factoryWF_of_lambdaFactoryWF (f : Expression.Factory)
    (hBN : f.factory.BindsTo "Bool.Not" (Lambda.boolNotFunc (T := CoreLParams)).func) :
    Imperative.FactoryWF (P := Expression) f :=
  ⟨coreEvaluator_WellFormedSemanticEvalBool f hBN, coreEvaluator_WellFormedSemanticEvalVar f,
    coreEvaluator_WellFormedSemanticEvalExprCongr f⟩

/-- `Core.Factory` satisfies the factory condition `FactoryWF` of the soundness theorems. -/
theorem factoryWF_coreFactory (f : Expression.Factory) (hf : f.factory = Core.Factory) :
    Imperative.FactoryWF (P := Expression) f :=
  factoryWF_of_lambdaFactoryWF f (hf ▸ coreFactory_boolNot)

end -- public section

end Core

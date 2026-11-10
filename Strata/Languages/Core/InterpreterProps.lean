/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.Interpreter
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.LExprEvalFully
import Strata.DL.Lambda.LExprEvalFuelProps
import all Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.DL.Imperative.InterpreterSound
public import Strata.DL.Imperative.InterpreterSemanticsSpec
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.InterpreterDomainProps
import Strata.DL.Imperative.InterpreterCallProps

/-! # Properties of Core's instantiation of the monadic interpreter

Lemmas about the definitions of `Core/Interpreter.lean`: the bounded evaluator, the call-aware
stepper and run loop, and Core's executable value checks.

Key theorems:
* `evalBounded_refines_evalFully`: a value the bounded evaluator commits to is the one the
  fixpoint evaluator `evalFully` returns; `evalBounded_intConst`: it returns an integer literal
  unchanged at every fuel; `boundedEvalMono_core`, `boundedEvalComplete_core`: it is upward
  fuel-monotone and reaches every `Expression.eval` value of a literal or a variable
  (`EvalCompleteFragment`) at some fuel.
* `replayStepCmd_cmd`, `runCoreInterp_eq`: unfolding equations of the stepper and run loop.
* `isValue_hasVal`, `replayValueOps_typedSound`, `valueOfTy_of_ops`: Core's executable value and
  type checks are sound for its semantic ones. -/

namespace Core
open Imperative
public section

/-! ## The bounded evaluator and the stepper -/

/-- **The bounded evaluator refines the fixpoint evaluator.**
    A fully-reduced bounded result is exactly what `evalFully` returns. -/
theorem evalBounded_refines_evalFully
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) (s : RStore Expression)
    (e v : Expression.Expr) (h : evalBounded fuel F s e = some v) :
    Lambda.LExpr.evalFully F s e = some v := by
  obtain ⟨-, he, -⟩ := evalBounded_eq_some_iff.1 h
  grind [Lambda.evalFully_of_value_true]

/-- `replayStepCmd` on a base command runs `stepBaseCmdStore` and presents the
    resulting store as a `.terminal` config.  Monad-generic. -/
@[simp] theorem replayStepCmd_cmd {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (π : String → Option Procedure) (depth fuel : Nat)
    (env : IEnv Expression) (base : Imperative.Cmd Expression) :
    replayStepCmd (m := m) π depth fuel env (.cmd base)
      = (stepBaseCmdStore fuel env.factory env.store base >>=
          fun store => pure (.terminal { env with store := store })) :=
  Calls.stepCmd_cmd ..

/-- `runCoreInterp` is the Imperative driver over the Core `replayStepCmd` stepper. -/
@[simp] theorem runCoreInterp_eq {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (π : String → Option Procedure) (fuel : Nat)
    (cfg : IConfig Expression Command) (d : Nat) :
    runCoreInterp (m := m) π fuel cfg d = runInterp (replayStepCmd π d) fuel cfg := (rfl)

end
end Core

namespace Core
open Imperative
public section
section CoreLang

/-! ## Evaluation of literals -/

/-- `evalBounded` returns a literal unchanged at every fuel. -/
theorem evalBounded_const (n : Nat) (f : @Lambda.Factory CoreLParams)
    (σ : RStore Expression) (m : ExpressionMetadata) (c : Lambda.LConst) :
    evalBounded n f σ (.const m c) = some (.const m c) :=
  evalBounded_eq_some_iff.2 ⟨evalTypedDomain_const σ m c, by
    cases n <;> simp [Lambda.LExpr.eval, Lambda.LExpr.isValue.eq_def], typeCheckWith_const .., rfl⟩

/-- `evalBounded` returns an integer literal unchanged at every fuel. -/
theorem evalBounded_intConst (n : Nat) (f : @Lambda.Factory CoreLParams)
    (σ : RStore Expression) (k : Int) :
    evalBounded n f σ (.intConst () k) = some (.intConst () k) :=
  evalBounded_const n f σ () (.intConst k)

/-! ## Fuel monotonicity and completeness of the bounded evaluator -/

/-- Core's bounded evaluator is upward fuel-monotone: a value it returns at some fuel it also
    returns at every larger fuel. -/
theorem boundedEvalMono_core : Imperative.BoundedEvalMono Expression := fun _ _ _ _ _ _ hle h => by
  obtain ⟨hd, he, ht⟩ := evalBounded_eq_some_iff.1 h
  exact evalBounded_eq_some_iff.2 ⟨hd, by grind [Lambda.eval_value_true_mono_le], ht⟩

/-- The expressions on which Core's bounded evaluator is complete for `Expression.eval`: literals
    and variables. -/
inductive EvalCompleteFragment : Expression.Expr → Prop where
  /-- A literal. -/
  | const (m : ExpressionMetadata) (c : Lambda.LConst) : EvalCompleteFragment (.const m c)
  /-- A variable, with any annotation. -/
  | fvar (m : ExpressionMetadata) (x : CoreIdent) (ty : Option Lambda.LMonoTy) :
      EvalCompleteFragment (.fvar m x ty)

/-- Core's bounded evaluator reaches, at some fuel, a value expression denoting every
    `Expression.eval` value of a literal or a variable (`EvalCompleteFragment`), on a runtime
    store of values (`isValue`) denoting the semantic store whose operators are annotated with
    instances of their functions' types (`opsInstantiated`). -/
theorem boundedEvalComplete_core (f : Expression.Factory) (σr : RStore Expression)
    (σ : SemanticStore Expression) (e : Expression.Expr) (v : Expression.Val)
    (hσ : StoreDenotes f σr σ)
    (hval : ∀ x r, σr x = some r → Lambda.LExpr.isValue f.factory r = true)
    (hops : ∀ x r, σr x = some r → opsInstantiated f.factory r = true)
    (he : EvalCompleteFragment e) (hv : Expression.eval f σ e = some v) :
    ∃ n r, InterpLang.boundedEval (P := Expression) n (InterpLang.rfactory f) σr e = some r ∧
      InterpLang.Denotes f r v := by
  cases he with
  | const m c =>
    have hc : Expression.eval f σ (.const m c) = some (Lambda.SemValue.ofConst _ c) :=
      Lambda.LExpr.denoteEval_const
    exact ⟨0, _, evalBounded_const 0 _ σr m c, Option.some.inj (hc.symm.trans hv) ▸
      denotes_literal Lambda.LExpr.denoteEval_const⟩
  | fvar m x ty =>
    obtain ⟨w, hw, htc⟩ := Lambda.LExpr.denoteEval_defines hv x
      (by simp [Lambda.getVars_eq_freeVars_idents, Lambda.LExpr.freeVars])
    obtain rfl := Option.some.inj ((Lambda.LExpr.denoteEval_fvar hw htc).symm.trans hv)
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 fun h => by simp [(hσ.1 x).2 h] at hw
    refine ⟨1, r, ?_, hσ.2 x r w hr hw⟩
    have hnv : Lambda.LExpr.isValue f.factory (.fvar m x ty : Expression.Expr) = false := by
      simp [Lambda.LExpr.isValue.eq_def, Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
        Lambda.getLFuncCall.go]
    have hnc : f.factory.callOfLFunc (.fvar m x ty : Expression.Expr) = none := by
      simp [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    have hdom := evalTypedDomain_fvar (m := m) (ty := ty) hr (by
      simpa [denotes_typeCheck (hσ.2 x r w hr hw), isGroundTy_iff] using
        Lambda.LSort.toMonoTy_isGround w.sort)
    show evalBounded 1 f.factory σr _ = some r
    refine evalBounded_eq_some_iff.2 ⟨hdom, ?_, (denotes_iff.1 (hσ.2 x r w hr hw)).2.1,
      evalOpsChecked_fvar hr (hops x r hr)⟩
    simp only [Lambda.LExpr.eval, hnv, hnc, Lambda.LExpr.evalCore, hr, hval x r hr]
    rfl

end CoreLang
end
end Core

namespace Core
open Imperative _root_.Lambda
public section

/-! ## The executable value checks -/

/-- Every value a Core runtime expression denotes satisfies Core's semantic value predicate
    (`HasVal.value`), so the executable value check is sound for it. -/
theorem isValue_hasVal (f : Expression.Factory) (r : Expression.Expr) (v : Expression.Val)
    (hd : InterpLang.Denotes f r v) : HasVal.value f v :=
  Lambda.LExpr.denoteEval_tc (denotes_iff.1 hd).2.2

/-- A Core expression equal to the Boolean literal of `b` up to metadata is that literal with some
    metadata. -/
theorem eq_boolConst_of_eqModuloMeta {r : Expression.Expr} {b : Bool}
    (h : InterpLang.eqModuloMeta r (LExpr.boolConst () b) = true) :
    ∃ m, r = LExpr.boolConst m b := by
  change LExpr.eqModuloMeta r _ = true at h
  unfold LExpr.eqModuloMeta BEq.beq instBEqLExprOfIdentifier at h
  cases r <;> simp_all [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.boolConst, LExpr.beq]

/-- The Boolean literal of `b`, with any metadata, is read as `b` (`InterpLang.boolLit?`). -/
@[simp] theorem boolLit?_boolConst (m : ExpressionMetadata) (b : Bool) :
    InterpLang.boolLit? (P := Expression) (LExpr.boolConst m b) = some b := by
  cases b <;> rfl

/-- Core's Boolean literals, with any metadata, denote the Boolean values of every factory. -/
instance : InterpLangBool Expression where
  denote_tt _ := denotes_literal Lambda.LExpr.denoteEval_boolConst
  denote_ff _ := denotes_literal Lambda.LExpr.denoteEval_boolConst
  denote_of_eqModuloMeta_tt _ _ _ h hd := by
    obtain ⟨_, rfl⟩ := eq_boolConst_of_eqModuloMeta h
    exact Option.some.inj (hd.symm.trans (denotes_literal Lambda.LExpr.denoteEval_boolConst))
  denote_of_eqModuloMeta_ff _ _ _ h hd := by
    obtain ⟨_, rfl⟩ := eq_boolConst_of_eqModuloMeta h
    exact Option.some.inj (hd.symm.trans (denotes_literal Lambda.LExpr.denoteEval_boolConst))

/-- A value passing Core's `hasType` check at `ty` type checks against the factory
    (`typeCheckWith`) to the monomorphic, ground form of `ty`. -/
private theorem hasType_eq_true {F : Lambda.Factory CoreLParams} {r : Expression.Expr}
    {ty : Expression.Ty} (h : (InterpLang.ops (P := Expression)).hasType F r ty = true) :
    ∃ τ, ty.toMonoType? = some τ ∧ r.typeCheckWith F [] = some τ ∧ τ.IsGround := by
  simp only [InterpLang.ops, replayValueOps, valueHasType, valueHasMonoType] at h
  split at h
  · rename_i τ hτ
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨τ, hτ, h.1, isGroundTy_iff.1 h.2⟩
  · cases h

/-- A type obtained by type checking against a factory is the plain `typeCheck` type. -/
private theorem typeCheck_of_typeCheckWith {F : Lambda.Factory CoreLParams}
    {r : Expression.Expr} {τ : Lambda.LMonoTy} (h : r.typeCheckWith F [] = some τ) :
    r.typeCheck [] = some τ := by
  unfold LExpr.typeCheckWith at h
  split at h <;> simp_all

/-- Core's executable type checks are sound against `HasVal.valueOfTy`: a value passing
    `hasType` at `ty` denotes a value of `ty`, and a value passing `sameType` against an `old`
    value denoting a value of `ty` denotes a value of `ty`. -/
theorem replayValueOps_typedSound :
    (InterpLang.ops (P := Expression)).TypedSound InterpLang.rfactory InterpLang.denote := by
  refine ⟨fun F r ty hv ht => ?_, fun F old r vo ty hold hvo hv hs => ?_⟩
  · obtain ⟨τ, hτ, hw, hg⟩ := hasType_eq_true ht
    obtain ⟨v, hd, htc, hsv⟩ := denote_of_isValue_typeCheckWith hv hw hg
    exact ⟨v, hd, htc, hτ.trans (congrArg some hsv.symm)⟩
  · simp only [InterpLang.ops, replayValueOps, beq_iff_eq] at hs
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.1 (hs ▸ (denotes_iff.1 hold).2.1)
    have hold' : old.typeCheck [] = some τ := typeCheck_of_typeCheckWith (hs.trans hτ)
    have hτo : τ = vo.sort.toMonoTy :=
      Option.some.inj (hold'.symm.trans (denotes_typeCheck hold))
    obtain ⟨v, hd, htc, hsv⟩ :=
      denote_of_isValue_typeCheckWith hv hτ (hτo ▸ LSort.toMonoTy_isGround _)
    exact ⟨v, hd, htc, hvo.2.trans (congrArg some (hτo.symm.trans hsv.symm))⟩

/-- Core's executable type check is sound for its typed values: a runtime value that denotes
    `v` and passes `hasType` at `ty` denotes a value of `ty`. -/
theorem valueOfTy_of_ops {f : Expression.Factory} {r : Expression.Expr} {v : Expression.Val}
    (hd : InterpLang.Denotes f r v) {ty : Expression.Ty}
    (h : (InterpLang.ops (P := Expression)).hasType f.factory r ty = true) :
    HasVal.valueOfTy f v ty := by
  obtain ⟨τ, hτ, hw, -⟩ := hasType_eq_true h
  have hτv := (typeCheck_of_typeCheckWith hw).symm.trans (denotes_typeCheck hd)
  exact ⟨LExpr.denoteEval_tc (denotes_iff.1 hd).2.2, hτ.trans hτv⟩

/-- On a factory with no Boolean-valued constructor (`ConstrsNotBool`), a runtime value that
    passes Core's executable value check and its Boolean type check is the literal `true` or
    `false` up to metadata (`InterpLang.boolLit?`). -/
theorem replayValueOps_bool {F : Lambda.Factory CoreLParams} (hF : F.ConstrsNotBool)
    {v : Expression.Expr}
    (hv : ((InterpLang.ops (P := Expression)).isValue F v &&
      (InterpLang.ops (P := Expression)).hasType F v (HasBool.boolTy (P := Expression))) = true) :
    InterpLang.boolLit? (P := Expression) v = some true ∨
      InterpLang.boolLit? (P := Expression) v = some false := by
  simp only [Bool.and_eq_true] at hv
  obtain ⟨_, b, rfl⟩ := Lambda.LExpr.isValue_bool_eq_boolConst hF hv.1 (by
    have h2 := hv.2
    simp only [InterpLang.ops, replayValueOps, HasBool.boolTy, valueHasType,
      Lambda.LTy.toMonoType?, valueHasMonoType, Bool.and_eq_true, beq_iff_eq] at h2
    exact h2.1)
  cases b
  · exact .inr (boolLit?_boolConst _ false)
  · exact .inl (boolLit?_boolConst _ true)

end
end Core

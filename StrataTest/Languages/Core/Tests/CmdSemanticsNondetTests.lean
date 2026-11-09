/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.InstExprTyping
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Languages.Core.Expressions
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.LState
meta import all Strata.Languages.Core.Factory
meta import Strata.Languages.Core.Procedure

/-! # Typed nondeterministic Core command semantics

Core stores hold semantic values, each recording its sort. These tests
characterize nondeterministic Boolean writes by `HasVal.valueOfTy` and explicitly
rule out the integer `7`. They also show that both Boolean values are admissible, and
that a closed quantifier is not a value (`isValue`).
-/

namespace Core.CmdSemanticsNondetTests

open Imperative

private def x : Expression.Ident := ⟨"x", ()⟩
/-- The integer `7` in the model of the factory `f`. -/
private def intValue (f : Expression.Factory) : Expression.Val :=
  ⟨f.model.tcInterp, .int, (7 : Int)⟩

/-- The integer `7` is not a value of the Boolean type. -/
private theorem intValue_not_bool
    (f : Expression.Factory) :
    ¬ HasVal.valueOfTy f (intValue f) HasBool.boolTy := by
  simp [HasVal.valueOfTy, HasBool.boolTy, intValue, Lambda.LTy.toMonoType?,
    Lambda.LSort.toMonoTy]

/-- Event semantics imposes the same Boolean type restriction on init. -/
theorem evalCmdE_init_nondet_bool_typed
    (h : EvalCmdE Expression f σ (.init x HasBool.boolTy .nondet md) σ' []) :
    ∃ v, σ' x = some v ∧ HasVal.valueOfTy f v HasBool.boolTy := by
  cases h with
  | eval_init_unconstrained hinit htyped _ =>
    cases hinit with
    | init _ hx _ => exact ⟨_, hx, htyped⟩

/-- Event semantics likewise rejects an integer choice for Boolean init. -/
theorem evalCmdE_init_nondet_bool_not_int
    (h : EvalCmdE Expression f σ (.init x HasBool.boolTy .nondet md) σ' []) :
    σ' x ≠ some (intValue f) := by
  obtain ⟨v, hx, hv⟩ := evalCmdE_init_nondet_bool_typed h
  intro hint
  have : v = intValue f := Option.some.inj (hx.symm.trans hint)
  subst this
  exact intValue_not_bool f hv

/-- Event semantics preserves the same stored Boolean type on nondeterministic
assignment. -/
theorem evalCmdE_set_nondet_bool_typed
    (htrue : σ x = some (HasBool.ttVal f))
    (h : EvalCmdE Expression f σ (.set x .nondet md) σ' []) :
    ∃ v, σ' x = some v ∧ HasVal.valueOfTy f v HasBool.boolTy := by
  cases h with
  | eval_set_nondet hupdate hstored _ =>
    obtain ⟨previous, ty, hprevious, hpTy, hvTy⟩ := hstored
    have hprev : previous = HasBool.ttVal f := Option.some.inj (hprevious.symm.trans htrue)
    subst hprev
    have hvBool := LawfulHasVal.valueOfTy_congr f (HasBool.ttVal f) _ HasBool.boolTy ty
      (HasBool.boolIsValOfTy f).1 hpTy hvTy
    cases hupdate with
    | update _ hx _ => exact ⟨_, hx, hvBool⟩

/-- Event semantics also rejects an integer choice for a Boolean slot. -/
theorem evalCmdE_set_nondet_bool_not_int
    (htrue : σ x = some (HasBool.ttVal f))
    (h : EvalCmdE Expression f σ (.set x .nondet md) σ' []) :
    σ' x ≠ some (intValue f) := by
  obtain ⟨v, hx, hv⟩ := evalCmdE_set_nondet_bool_typed htrue h
  intro hint
  have : v = intValue f := Option.some.inj (hx.symm.trans hint)
  subst this
  exact intValue_not_bool f hv

/-- Both Boolean values satisfy the type premise used by nondeterministic
Boolean initialization and assignment. -/
theorem true_and_false_are_bool_values (f : Expression.Factory) :
    HasVal.valueOfTy f (HasBool.ttVal f) HasBool.boolTy ∧
    HasVal.valueOfTy f (HasBool.ffVal f) HasBool.boolTy :=
  HasBool.boolIsValOfTy f

/-- A nondeterministic Boolean initializer writes `true` or `false`, on every Core factory. -/
theorem evalCmd_init_nondet_bool_literal {f : Expression.Factory}
    (h : EvalCmdE Expression f σ (.init x HasBool.boolTy .nondet md) σ' []) :
    σ' x = some (HasBool.ttVal f) ∨ σ' x = some (HasBool.ffVal f) := by
  obtain ⟨v, hx, hv⟩ := evalCmdE_init_nondet_bool_typed h
  rcases Core.valueOfTy_bool f v hv with rfl | rfl
  · exact .inl hx
  · exact .inr hx

/-- `Bool.Not` annotated as `bool`: a partial application (hence a value) whose
annotation is not an instance of the signature `bool → bool`. -/
private def notAsBool : Expression.Expr := .op () ⟨"Bool.Not", ()⟩ (some .bool)

/-- `Bool.Not` with its signature as annotation. -/
private def notAsArrow : Expression.Expr :=
  .op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool))

#guard Lambda.LExpr.isValue Core.Factory notAsBool
#guard Lambda.LExpr.typeCheck [] notAsBool == some .bool
#guard Lambda.LExpr.typeCheckWith Core.Factory [] notAsBool == none
#guard Lambda.LExpr.typeCheckWith Core.Factory [] notAsArrow == some (.arrow .bool .bool)

/-- `Sequence.empty` (signature `Sequence a`) annotated with its own type variable `t`. -/
private def emptyAsSeqT : Expression.Expr :=
  .op () ⟨"Sequence.empty", ()⟩ (some (Core.seqTy (.ftvar "t")))

/-- `Sequence.empty` annotated with an instance of its signature. -/
private def emptyAsSeqInt : Expression.Expr :=
  .op () ⟨"Sequence.empty", ()⟩ (some (Core.seqTy .int))

/-- `Bool.Not` (signature `bool → bool`) annotated with the more general `t → t`. -/
private def notAsPoly : Expression.Expr :=
  .op () ⟨"Bool.Not", ()⟩ (some (.arrow (.ftvar "t") (.ftvar "t")))

#guard Lambda.LExpr.typeCheckWith Core.Factory [] emptyAsSeqT ==
  Lambda.LExpr.typeCheck [] emptyAsSeqT
#guard Lambda.LExpr.typeCheckWith Core.Factory [] emptyAsSeqT == some (Core.seqTy (.ftvar "t"))
#guard Lambda.LExpr.typeCheckWith Core.Factory [] emptyAsSeqInt == some (Core.seqTy .int)
#guard Lambda.LExpr.typeCheckWith Core.Factory [] notAsPoly == none
#guard (Lambda.LMonoTy.matchSubst (Core.seqTy (.ftvar "a")) (Core.seqTy (.ftvar "t"))).map
    (fun S => (Core.seqTy (.ftvar "a")).subst S) == some (Core.seqTy (.ftvar "t"))
#guard (Lambda.LMonoTy.matchSubst (Core.seqTy .int) (Core.seqTy (.ftvar "t"))).isNone
#guard (Lambda.LMonoTy.matchSubst (.arrow (.ftvar "a") (.ftvar "a")) (.arrow .int .bool)).isNone

/-- The closed quantifier `∀ y : int. y = y`. -/
private def quantExpr : Expression.Expr :=
  .quant () .all "y" (some .int) (.bvar () 0) (.eq () (.bvar () 0) (.bvar () 0))

#guard !Lambda.LExpr.isValue Core.Factory quantExpr

end Core.CmdSemanticsNondetTests

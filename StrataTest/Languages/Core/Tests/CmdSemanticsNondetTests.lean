/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.Languages.Core.Expressions
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Languages.Core.Expressions

/-! # Typed nondeterministic Core command semantics

Core stores hold semantic values, each recording its sort. These tests
characterize nondeterministic Boolean writes by `HasVal.valueOfTy` and explicitly
rule out the integer `7`. They also show that both Boolean values are admissible.
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

end Core.CmdSemanticsNondetTests

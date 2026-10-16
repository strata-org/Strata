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

Core Boolean values include symbolic canonical Boolean expressions, not only the
literal expressions `true` and `false`. These tests therefore characterize
nondeterministic Boolean writes by `HasVal.valueOfTy` and explicitly rule out an
integer literal. They also show that both Boolean literals are admissible.
-/

namespace Core.CmdSemanticsNondetTests

open Imperative

private def x : Expression.Ident := ⟨"x", ()⟩
private def intValue : Expression.Expr := .intConst () 7

/-- The integer literal `7` is not a value of the Boolean type. -/
private theorem intValue_not_bool
    (f : Expression.Factory) :
    ¬ HasVal.valueOfTy f intValue HasBool.boolTy := by
  simp [HasVal.valueOfTy, HasBool.boolTy, intValue, Lambda.LExpr.typeCheck,
    Lambda.LTy.toMonoType?, Lambda.LConst.ty, Lambda.LMonoTy.int]

/-- A nondeterministic Boolean initializer writes a Boolean-typed value. -/
theorem evalCmd_init_nondet_bool_typed
    (h : EvalCmd Expression f σ (.init x HasBool.boolTy .nondet md) σ' false) :
    ∃ v, σ' x = some v ∧ HasVal.valueOfTy f v HasBool.boolTy := by
  cases h with
  | eval_init_unconstrained hinit htyped _ =>
    cases hinit with
    | init _ hx _ => exact ⟨_, hx, htyped⟩

/-- Event semantics imposes the same Boolean type restriction on init. -/
theorem evalCmdE_init_nondet_bool_typed
    (h : EvalCmdE Expression f σ (.init x HasBool.boolTy .nondet md) σ' []) :
    ∃ v, σ' x = some v ∧ HasVal.valueOfTy f v HasBool.boolTy := by
  cases h with
  | eval_init_unconstrained hinit htyped _ =>
    cases hinit with
    | init _ hx _ => exact ⟨_, hx, htyped⟩

/-- A nondeterministic Boolean initializer cannot choose an integer literal. -/
theorem evalCmd_init_nondet_bool_not_int
    (h : EvalCmd Expression f σ (.init x HasBool.boolTy .nondet md) σ' false) :
    σ' x ≠ some intValue := by
  obtain ⟨v, hx, hv⟩ := evalCmd_init_nondet_bool_typed h
  intro hint
  have : v = intValue := Option.some.inj (hx.symm.trans hint)
  subst this
  exact intValue_not_bool f hv

/-- Event semantics likewise rejects an integer choice for Boolean init. -/
theorem evalCmdE_init_nondet_bool_not_int
    (h : EvalCmdE Expression f σ (.init x HasBool.boolTy .nondet md) σ' []) :
    σ' x ≠ some intValue := by
  obtain ⟨v, hx, hv⟩ := evalCmdE_init_nondet_bool_typed h
  intro hint
  have : v = intValue := Option.some.inj (hx.symm.trans hint)
  subst this
  exact intValue_not_bool f hv

/-- Reassigning a slot containing `true` nondeterministically preserves its
Boolean type. -/
theorem evalCmd_set_nondet_bool_typed
    (htrue : σ x = some Core.true)
    (h : EvalCmd Expression f σ (.set x .nondet md) σ' false) :
    ∃ v, σ' x = some v ∧ HasVal.valueOfTy f v HasBool.boolTy := by
  cases h with
  | eval_set_nondet hupdate hstored _ =>
    obtain ⟨previous, ty, hprevious, hpTy, hvTy⟩ := hstored
    have hprev : previous = Core.true := Option.some.inj (hprevious.symm.trans htrue)
    subst hprev
    have hvBool := LawfulHasVal.valueOfTy_congr f Core.true _ HasBool.boolTy ty
      (HasBool.boolIsValOfTy f).1 hpTy hvTy
    cases hupdate with
    | update _ hx _ => exact ⟨_, hx, hvBool⟩

/-- Event semantics preserves the same stored Boolean type on nondeterministic
assignment. -/
theorem evalCmdE_set_nondet_bool_typed
    (htrue : σ x = some Core.true)
    (h : EvalCmdE Expression f σ (.set x .nondet md) σ' []) :
    ∃ v, σ' x = some v ∧ HasVal.valueOfTy f v HasBool.boolTy := by
  cases h with
  | eval_set_nondet hupdate hstored _ =>
    obtain ⟨previous, ty, hprevious, hpTy, hvTy⟩ := hstored
    have hprev : previous = Core.true := Option.some.inj (hprevious.symm.trans htrue)
    subst hprev
    have hvBool := LawfulHasVal.valueOfTy_congr f Core.true _ HasBool.boolTy ty
      (HasBool.boolIsValOfTy f).1 hpTy hvTy
    cases hupdate with
    | update _ hx _ => exact ⟨_, hx, hvBool⟩

/-- Nondeterministic assignment of a Boolean slot cannot choose an integer. -/
theorem evalCmd_set_nondet_bool_not_int
    (htrue : σ x = some Core.true)
    (h : EvalCmd Expression f σ (.set x .nondet md) σ' false) :
    σ' x ≠ some intValue := by
  obtain ⟨v, hx, hv⟩ := evalCmd_set_nondet_bool_typed htrue h
  intro hint
  have : v = intValue := Option.some.inj (hx.symm.trans hint)
  subst this
  exact intValue_not_bool f hv

/-- Event semantics also rejects an integer choice for a Boolean slot. -/
theorem evalCmdE_set_nondet_bool_not_int
    (htrue : σ x = some Core.true)
    (h : EvalCmdE Expression f σ (.set x .nondet md) σ' []) :
    σ' x ≠ some intValue := by
  obtain ⟨v, hx, hv⟩ := evalCmdE_set_nondet_bool_typed htrue h
  intro hint
  have : v = intValue := Option.some.inj (hx.symm.trans hint)
  subst this
  exact intValue_not_bool f hv

/-- Both Boolean literals satisfy the type premise used by nondeterministic
Boolean initialization and assignment. -/
theorem true_and_false_are_bool_values (f : Expression.Factory) :
    HasVal.valueOfTy f Core.true HasBool.boolTy ∧
    HasVal.valueOfTy f Core.false HasBool.boolTy :=
  HasBool.boolIsValOfTy f

end Core.CmdSemanticsNondetTests

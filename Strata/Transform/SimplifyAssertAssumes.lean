/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SimplifyExpr
public import Strata.Languages.Core.PipelinePhase

/-! # Simplify Assert/Assume Conditions

This transformation simplifies the condition expression of every `assert`
and `assume` command using `SimplifyExpr.simplifyExpr`. -/

public section

namespace Core
namespace SimplifyAssertAssumes

open Core.Transform Core.SimplifyExpr Lambda

inductive Stats where
  | assertsSimplifiedToTrue
  | assertsSimplified
  | assumesSimplifiedToTrue
  | assumesSimplified

#derive_prefixed_toString Stats "SimplifyAssertAssumes"

/-- The main simplification on a single command. -/
def simplifyCmd (cmd : Command) : CoreTransformM (Option (List Statement)) := do
  let F ← getFactory
  let σ := LState.init.setFactory F
  match cmd with
  | .cmd (.assert label expr md) =>
    if LExpr.isTrue _ expr then return .none
    let expr' := simplifyExpr 100 σ expr
    if LExpr.eqModuloMeta expr expr' then return .none
    else if LExpr.isTrue _ expr' then
      incrementStat s!"{Stats.assertsSimplifiedToTrue}"
      return .some [Statement.assert label expr' md]
    else
      incrementStat s!"{Stats.assertsSimplified}"
      return .some [Statement.assert label expr' md]
  | .cmd (.assume label expr md) =>
    if LExpr.isTrue _ expr then return .none
    let expr' := simplifyExpr 100 σ expr
    if LExpr.eqModuloMeta expr expr' then return .none
    else if LExpr.isTrue _ expr' then
      incrementStat s!"{Stats.assumesSimplifiedToTrue}"
      return .some [Statement.assume label expr' md]
    else
      incrementStat s!"{Stats.assumesSimplified}"
      return .some [Statement.assume label expr' md]
  | _ => return .none

/-- Run simplification over an entire program. -/
def simplifyAssertAssumes (p : Program) : CoreTransformM (Bool × Program) :=
  runProgram simplifyCmd p

end SimplifyAssertAssumes

/-- Pipeline phase for assert/assume simplification. Model-preserving because
    partial evaluation only replaces expressions with semantically equivalent
    simplified forms. -/
def simplifyAssertAssumesPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "SimplifyAssertAssumes"
    SimplifyAssertAssumes.simplifyAssertAssumes

end Core

end -- public section

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

/-- The main simplification on a single command. -/
def simplifyCmd (cmd : Command) : CoreTransformM (Option (List Statement)) := do
  let F ← getFactory
  let σ := LState.init.setFactory F
  match cmd with
  | .cmd (.assert label expr md) =>
    let expr' := simplifyExpr 100 σ expr
    if LExpr.eqModuloMeta expr expr' then return .none
    else return .some [Statement.assert label expr' md]
  | .cmd (.assume label expr md) =>
    let expr' := simplifyExpr 100 σ expr
    if LExpr.eqModuloMeta expr expr' then return .none
    else return .some [Statement.assume label expr' md]
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

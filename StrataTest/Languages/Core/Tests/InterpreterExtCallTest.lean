/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.InterpreterEval
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.InterpreterTestUtils

/-! # An extension command that resolves to a call

`Calls.stepCmdWith` runs an extension command (`Calls.CmdView.ext`) that resolves to a call
(`Calls.ExtStep.call`) as it runs a call, from the environment the extension command reached.
The view `extView y` takes every call command for an extension command that sets `y := y₀`
and then resolves to `call pick(y, out x)`. The callee `pick(a : int, out r : int)` sets
`r := 1` when `0 < a` and `r := 0` otherwise, so `x` after the step shows which `y` the call
read: `1` for `y₀ = 5`, `0` for `y₀ = -3`, from the caller store `x ↦ 7, y ↦ 5`. -/

meta section

namespace InterpreterExtCallTest

open Core Lambda Imperative

/-- The callee `pick` and the structured caller `caller`, whose body is `call pick(5, out x)`. -/
private def program :=
#strata
program Core;
procedure pick(a : int, out r : int)
{
  if (int.lt(0, a)) {
    r := 1;
  } else {
    r := 0;
  }
};
procedure caller(out x : int)
{
  call pick(5, out x);
};
#end

#guard Strata.InterpreterTestUtils.translationOk program

/-- The procedure table of `program`. -/
private def π : String → Option Procedure := Strata.InterpreterTestUtils.procTable program

/-- The call command of `caller`. -/
private def callerCmd : Command :=
  match (π "caller").map Procedure.body with
  | some (.structured [.cmd c] _) => c
  | _ => .call "" none [] #[]

/-- The Core identifier `name`. -/
private def id (name : String) : CoreIdent := ⟨name, ()⟩
/-- The integer literal `n`. -/
private def int (n : Int) : Expression.Expr := .intConst default n

/-- The view that takes every call command for an extension command that sets `y := y₀` and
    resolves to `call pick(y, out x)` from the store it reached; other commands as
    `Calls.CmdExt.view`. -/
private def extView (y₀ : Int) : Command → Calls.CmdView Expression Command Procedure.Header EvalM
  | .call n tyArgs _ md =>
    .ext fun _ env => pure (.call { env with store := env.store.update (id "y") (int y₀) } n
      [.inArg (.fvar default (id "y") none), .outArg (id "x")] md
      fun p => ProcedureTypeInstantiation.instantiate p (tyArgs.getD []))
  | c => Calls.CmdExt.view c

/-- The caller store `x ↦ 7, y ↦ 5`. -/
private def σ0 : RStore Expression := fun n =>
  if n == id "x" then some (int 7) else if n == id "y" then some (int 5) else none

/-- The caller environment: store `σ0` at `Core.Factory`. -/
private def env0 : IEnv Expression := { store := .ofStore σ0, factory := Core.Factory }

/-- The `EvalM` options of every run. -/
private def opts : EvalOpts := EvalOpts.legacy 100

/-- `x` after one step of `stepCmdWith (extView y₀)` on `callerCmd`, `none` for every other
    outcome. -/
private def xAfter (y₀ : Int) : Option Expression.Expr :=
  match ((((Calls.stepCmdWith (extView y₀) (fun _ x => x) π .contract defaultMaxCallDepth 100
      env0 callerCmd).run opts).run).run {}) with
  | (.ok (.terminal ρ), _) => ρ.store.get (id "x")
  | _ => none

#guard xAfter 5 =ₘ some (int 1)
#guard xAfter (-3) =ₘ some (int 0)

end InterpreterExtCallTest

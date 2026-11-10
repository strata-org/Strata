/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.DL.Imperative.InterpreterObs
public import Strata.DL.Imperative.InterpreterCallInterrupt
public import Strata.DL.Imperative.InterpreterCall
public import Strata.Languages.Core.StatementSemanticsProps
public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.DL.Imperative.InterpreterCallProps
public import Strata.Languages.Core.InterpreterProps
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplayProps
import all Strata.DL.Imperative.InterpreterCallInterrupt
import Strata.Languages.Core.InterpreterReplayTactics

/-! # The interruption bridges for `runCoreInterp π`: the Core instance of
`Imperative.InterpreterCallInterrupt`

The production replay run stops early through its stop hook (`interruptOn`); the specification
run records every event and never stops early (`interruptOff`).  The generic bridges of
`Imperative.InterpreterCallInterrupt` relate the two; this module instantiates them at Core's
call-aware stepper `replayStepCmd π` and driver `runCoreInterp π`:
* `Calls.DBridge`: the interrupt-on trace is a suffix of the interrupt-off trace;
* `Calls.FeasBridge`: under the enforcing stop hook `enforceInterrupt`, a run that succeeds or
  stops at the target keeps every recorded assume true (`PathFeasible`);
* `Calls.StopBridge`: under `enforceInterrupt`, a run that records a failing target occurrence
  stops with `.interrupted`;
* `Calls.CoBridge`: the interrupt-on run equals the interrupt-off run until its stop hook fires.

Key theorems:
* `genuineFeasible_iff_genuineEnforced`: the two production verdicts coincide;
* `genuineEnforced_of_spec_suffix`: a failing target occurrence preceded by true assumes in the
  specification trace makes the enforcing production verdict `.genuine`. -/

namespace Core

public section

open Imperative

/-! ## `Calls.DBridge`: the interrupt-on trace is a suffix of the interrupt-off trace -/

/-- Every step of Core's call-aware command stepper `replayStepCmd π` satisfies `Calls.DBridge` (the
    stop hook only truncates the run). -/
theorem dBridge_replayStepCmd (π : String → Option Procedure) :
    ∀ (k d : Nat) (env : IEnv Expression) (cmd : Command)
      (cfg : ReplayCfg Expression) (st : ReplayState Expression),
      Calls.DBridge (replayStepCmd π d k env cmd) cfg st := by core_gen dBridge_stepCmd

/-- Every run of Core's call-aware driver `runCoreInterp π` satisfies `Calls.DBridge` (the stop hook
    only truncates the run). -/
theorem dBridge_runCoreInterp (π : String → Option Procedure) (fuel : Nat)
    (start : IConfig Expression Command) (d : Nat) (cfg : ReplayCfg Expression)
    (st : ReplayState Expression) :
    Calls.DBridge (runCoreInterp (m := ReplayM Expression) π fuel start d) cfg st := by
  core_gen dBridge_runCallInterp

/-- **Interrupt-on genuine ⟹ interrupt-off genuine**: if the replay of `runCoreInterp π` with
    the stop hook of `cfg` returns `.genuine`, so does the replay with the stop hook disabled
    (`interruptOff cfg`), with the same halting predicate `haltOn` and oracle. -/
theorem runReplay_genuine_of_interruptOn (π : String → Option Procedure) (fuel : Nat)
    (start : IConfig Expression Command) (d : Nat) (cfg : ReplayCfg Expression)
    (haltOn : IEvent Expression → Bool)
    (oracle : List Expression.Expr)
    (h : (runReplay (runCoreInterp (m := ReplayM Expression) π fuel start d) cfg haltOn oracle).1
        = .genuine) :
    (runReplay (runCoreInterp (m := ReplayM Expression) π fuel start d)
        (interruptOff cfg) haltOn oracle).1 = .genuine := by core_gen

/-! ## `Calls.FeasBridge`: a target-reaching production run has a path-feasible trace -/

/-- Every step of Core's call-aware command stepper `replayStepCmd π` satisfies `Calls.FeasBridge`
    (an `.ok` or interrupted run keeps the trace path-feasible). -/
theorem feasBridge_replayStepCmd (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) :
    ∀ (k d : Nat) (env : IEnv Expression) (cmd : Command)
      (cfg : ReplayCfg Expression) (st : ReplayState Expression),
      Calls.FeasBridge target fuel (replayStepCmd π d k env cmd) cfg st := by
  core_gen feasBridge_stepCmd

/-- Every run of Core's call-aware driver `runCoreInterp π` satisfies `Calls.FeasBridge` (an `.ok`
    or interrupted run keeps the trace path-feasible). -/
theorem feasBridge_runCoreInterp (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) (dfuel : Nat)
    (start : IConfig Expression Command) (d : Nat) (cfg : ReplayCfg Expression)
    (st : ReplayState Expression) :
    Calls.FeasBridge target fuel (runCoreInterp (m := ReplayM Expression) π dfuel start d)
      cfg st := by
  core_gen feasBridge_runCallInterp

/-- A strict replay run of `runCoreInterp π` under the enforcing stop hook
    `enforceInterrupt target fuel` that succeeds or stops at the target records only assumes that
    evaluate to true (`PathFeasible`). -/
theorem pathFeasible_of_runReplayRun_enforce (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) (start : IConfig Expression Command) (d : Nat)
    (oracle : List Expression.Expr)
    (hok : Calls.OkOrInterrupt
      (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel start d)
        { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel } oracle).1) :
    PathFeasible fuel (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
      oracle).2.traceRev := by
  core_gen

/-! ## `Calls.StopBridge`: a target-reaching production run stops by `.interrupted` -/

/-- Every step of Core's call-aware command stepper `replayStepCmd π` satisfies `Calls.StopBridge`
    (a newly recorded failing target event interrupts the run). -/
theorem stopBridge_replayStepCmd (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) :
    ∀ (k d : Nat) (env : IEnv Expression) (cmd : Command)
      (cfg : ReplayCfg Expression) (st : ReplayState Expression),
      Calls.StopBridge target fuel (replayStepCmd π d k env cmd) cfg st := by
  core_gen stopBridge_stepCmd

/-- Every run of Core's call-aware driver `runCoreInterp π` satisfies `Calls.StopBridge` (a newly
    recorded failing target event interrupts the run). -/
theorem stopBridge_runCoreInterp (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) (dfuel : Nat)
    (start : IConfig Expression Command) (d : Nat) (cfg : ReplayCfg Expression)
    (st : ReplayState Expression) :
    Calls.StopBridge target fuel (runCoreInterp (m := ReplayM Expression) π dfuel start d)
      cfg st := by
  core_gen stopBridge_runCallInterp

/-! ## `Calls.CoBridge`: the production run coincides with the spec run until its stop hook fires -/

/-- Every step of Core's call-aware command stepper `replayStepCmd π` satisfies `Calls.CoBridge`
    (the stop hook can only stop the run at its last event). -/
theorem coBridge_replayStepCmd
    (π : String → Option Procedure) :
    ∀ (k d : Nat) (env : IEnv Expression) (cmd : Command)
      (cfg : ReplayCfg Expression) (st : ReplayState Expression),
      Calls.CoBridge (replayStepCmd π d k env cmd) cfg st := by core_gen coBridge_stepCmd

/-- Every run of Core's call-aware driver `runCoreInterp π` satisfies `Calls.CoBridge` (the stop
    hook can only stop the run at its last event). -/
theorem coBridge_runCoreInterp
    (π : String → Option Procedure) (dfuel : Nat)
    (start : IConfig Expression Command) (d : Nat) (cfg : ReplayCfg Expression)
    (st : ReplayState Expression) :
    Calls.CoBridge (runCoreInterp (m := ReplayM Expression) π dfuel start d) cfg st := by
  core_gen coBridge_runCallInterp

/-! ## Corollaries relating the verdicts -/

/-- If the strict replay of `runCoreInterp π` under the enforcing stop hook returns `.genuine`,
    every assume its run records evaluates to true (`PathFeasible`). -/
theorem pathFeasible_of_runReplay_genuine_core (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) (start : IConfig Expression Command) (d : Nat)
    (oracle : List Expression.Expr)
    (h : (runReplay (runCoreInterp (m := ReplayM Expression) π fuel start d)
        { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        (assertFailureHalt target fuel) oracle).1 = .genuine) :
    PathFeasible fuel (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
      oracle).2.traceRev := by
  core_gen

/-- If the record-only specification trace of `runCoreInterp π` has the suffix `tgt :: pre`,
    where every assume in `pre` evaluates to true and `tgt` is a failing target occurrence, then
    every assume recorded by the enforcing production run also evaluates to true. -/
theorem pathFeasible_enforce_of_spec_suffix (target : AssertId Expression) (fuel : Nat)
    (π : String → Option Procedure) (start : IConfig Expression Command) (d : Nat)
    (oracle : List Expression.Expr) (tgt : IEvent Expression) (pre : List (IEvent Expression))
    (htgt : assertFailureHalt target fuel tgt = true) (hpre : PathFeasible fuel pre)
    (hsuf : (tgt :: pre) <:+ (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel start d)
        { oracleConfig := .strict } oracle).2.traceRev) :
    PathFeasible fuel (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
      oracle).2.traceRev := by
  core_gen

/-- **The two production verdicts coincide** on every Core counterexample, for every callee
    table `π`, target and fuel: the replay is genuine with every recorded assume true
    (`genuineFeasible`) exactly when the enforcing production run returns `.genuine`
    (`genuineEnforced`). -/
theorem genuineFeasible_iff_genuineEnforced (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (cex : CexA Expression Command) (d : Nat) :
    genuineFeasible π target fuel cex d ↔ genuineEnforced π target fuel cex d := by core_gen

/-- **Completeness of the production verdict.** If the record-only spec trace of the strict replay
    run of `runCoreInterp π` from `cex.cfg` has the suffix `tgt :: pre`, where every
    assume in `pre` evaluates to true and `tgt` is a failing target occurrence, then `cex` is
    `genuineEnforced`: the enforcing production run returns `.genuine`. -/
theorem genuineEnforced_of_spec_suffix (π : String → Option Procedure)
    (target : AssertId Expression) (cex : CexA Expression Command) (fuel d : Nat)
    (tgt : IEvent Expression) (pre : List (IEvent Expression))
    (htgt : assertFailureHalt target fuel tgt = true) (hpre : PathFeasible fuel pre)
    (hsuf : (tgt :: pre) <:+ (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel
        cex.cfg d) { oracleConfig := .strict } cex.oracle).2.traceRev) :
    genuineEnforced π target fuel cex d := by core_gen

end -- public section

end Core

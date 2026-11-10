/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterReplay
public import Strata.DL.Lambda.FactoryProps
public import Strata.Languages.Core.Interpreter
public import Strata.Languages.Core.ConfigWF
import all Strata.DL.Imperative.Interpreter
import all Strata.Languages.Core.Interpreter
import Strata.Languages.Core.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterReplayProps

/-! # Core counterexample replay

Key definitions:
* `replayWithM`: replays a counterexample with `runCoreInterp` in `ReplayM` from the embedding
  of its configuration, halting on the target predicate `assertFailureHalt`.
* The stop hooks `targetInterrupt` and `enforceInterrupt`, and the trace predicate
  `PathFeasible`.
* The verdicts `genuine`, `genuineFeasible` and `genuineEnforced`.

Under `ReplayM`, the nondeterministic choices of a callee body are drawn from the same oracle as
the caller's.

Lemmas about these definitions are in `Core/InterpreterReplayProps.lean`. -/

namespace Core

open Imperative

public section

/-- The target predicate (`Calls.assertFailureHalt` at `Expression`): `ev` matches the target id
    (`label` and `md`) and its condition evaluates under `evalBounded fuel` to `ff` for an
    `.assert`, or `tt` for a `.cover`, up to metadata (`Lambda.LExpr.eqModuloMeta`). -/
abbrev assertFailureHalt (target : AssertId Expression) (fuel : Nat) : IEvent Expression → Bool :=
  Calls.assertFailureHalt target fuel

/-- Production stop hook, interrupt only (`Calls.targetInterrupt` at `Expression`): throws
    `.interrupted` exactly at an event satisfying `assertFailureHalt target fuel`. -/
abbrev targetInterrupt (target : AssertId Expression) (fuel : Nat) :
    IEvent Expression → Option StopReason :=
  Calls.targetInterrupt target fuel

/-- Production stop hook with assume enforcement (`Calls.enforceInterrupt` at `Expression`): on
    an `.assume`, `tt` continues, `ff` throws `.assumptionFalseUnderReplay`, a non-Boolean
    `.expressionWasNotBoolean`, a non-reducing condition `.expressionDidNotEvaluate`; every other
    event is `targetInterrupt target fuel`. -/
abbrev enforceInterrupt (target : AssertId Expression) (fuel : Nat) :
    IEvent Expression → Option StopReason :=
  Calls.enforceInterrupt target fuel

/-- Every `.assume` event in `evs` evaluates to `tt` under `evalBounded fuel`
    (`Calls.PathFeasible` at `Expression`). -/
abbrev PathFeasible (fuel : Nat) (evs : List (IEvent Expression)) : Prop :=
  Calls.PathFeasible fuel evs

/-- Replay `cex` with `runCoreInterp π` at the single fuel `fuel` and call-depth limit
    `maxCallDepth`, halting on `assertFailureHalt target fuel` (`Calls.replayWith` at
    `Expression`). -/
abbrev replayWithM (cex : CexA Expression Command) (target : AssertId Expression)
    (fuel : Nat) (π : String → Option Procedure := fun _ => none)
    (maxCallDepth : Nat := defaultMaxCallDepth) :
    CEValidationVerdict StopReason :=
  Calls.replayWith cex target fuel π maxCallDepth

/-! ## The replay verdicts, keyed on the target assertion id -/

/-- Replaying `cex` with `replayWithM` at fuel `fuel` and call-depth limit `maxCallDepth`, with
    callees resolved by `π`, reaches a failing occurrence of the target assertion (or a satisfied
    target cover) (`Calls.genuine` at `Expression`). -/
abbrev genuine (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (cex : CexA Expression Command) (maxCallDepth : Nat := defaultMaxCallDepth) :
    Prop :=
  Calls.genuine π target fuel cex maxCallDepth

/-- `cex` is `genuine`, and the enforcing production run
    (`interruptOn := enforceInterrupt target fuel`) has a `PathFeasible` trace: every assume up to
    the first failing target occurrence holds (`Calls.genuineFeasible` at `Expression`). -/
abbrev genuineFeasible (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (cex : CexA Expression Command) (maxCallDepth : Nat := defaultMaxCallDepth) :
    Prop :=
  Calls.genuineFeasible π target fuel cex maxCallDepth

/-- The strict enforcing production run (`interruptOn := enforceInterrupt target fuel`) returns
    `.genuine`: some target occurrence fails and every assume before it holds
    (`Calls.genuineEnforced` at `Expression`).  It is equivalent to `genuineFeasible`. -/
abbrev genuineEnforced (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (cex : CexA Expression Command) (maxCallDepth : Nat := defaultMaxCallDepth) :
    Prop :=
  Calls.genuineEnforced π target fuel cex maxCallDepth

end -- public section

end Core

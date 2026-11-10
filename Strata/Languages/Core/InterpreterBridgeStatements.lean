/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.StatementSemantics

/-! # The replay soundness and completeness statements for Core `Command`

`ReplaySound`, `ReplaySoundFeasible` and `ReplayComplete` relate `Core.genuine` /
`Core.genuineEnforced` to the reference relation `StepStmtStarE (EvalCommandE π)
(EvalPureFunc)`.  The two soundness statements are proved in `InterpreterCallSound`
(`core_replaySound`, `core_replaySound_feasible`).  `InterpreterCallComplete` proves
completeness for a failing run whose choices the counterexample's oracle supplies
(`core_replayComplete`). -/

namespace Core

open Imperative

public section

/-- **Soundness**: if replaying `cex` at fuel `fuel` and call-depth limit `maxCallDepth` reaches a
    failure of the target assertion (`genuine`), then a reference run from `cex.cfg` emits an event
    on which the target fails (`assertFailureHalt target fuel`: the event matches the target id and
    its condition evaluates to false for an assert, or to true for a cover). -/
def ReplaySound
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (F : Expression.Factory)
    (cex : CexA Expression Command)
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuine π target fuel cex maxCallDepth →
    ∃ (evs : List (IEvent Expression)) (final : Config Expression Command),
      StepStmtStarE (P := Expression) (EvalCommandE π)
        (cex.cfg.abs F) (evs.map (REvent.abs F)) final ∧
      ∃ ev ∈ evs, assertFailureHalt target fuel ev = true

/-- **Feasibility-aware soundness**: if the replay of `cex` that also enforces assumptions
    reaches a failure of the target assertion (`genuineEnforced`), then a reference run from
    `cex.cfg` emits events `evs` among which the target fails (`assertFailureHalt target fuel`),
    and every assume event of `evs` evaluates to true at fuel `fuel` (`PathFeasible`). -/
def ReplaySoundFeasible
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (F : Expression.Factory)
    (cex : CexA Expression Command)
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuineEnforced π target fuel cex maxCallDepth →
    ∃ (evs : List (IEvent Expression)) (final : Config Expression Command),
      StepStmtStarE (P := Expression) (EvalCommandE π)
        (cex.cfg.abs F) (evs.map (REvent.abs F)) final ∧
      (∃ ev ∈ evs, assertFailureHalt target fuel ev = true) ∧
      PathFeasible fuel evs

/-- **Completeness**: if a reference run from `cex.cfg` emits an event on which the target
    assertion fails at fuel `fuel` (`assertFailureHalt target fuel`), then replaying `cex` at
    fuel `fuel` reaches that failure (`genuine`). -/
def ReplayComplete
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (F : Expression.Factory)
    (cex : CexA Expression Command) : Prop :=
  (∃ (evs : List (IEvent Expression)) (final : Config Expression Command),
      StepStmtStarE (P := Expression) (EvalCommandE π)
        (cex.cfg.abs F) (evs.map (REvent.abs F)) final ∧
      ∃ ev ∈ evs, assertFailureHalt target fuel ev = true) →
    genuine π target fuel cex

end -- public section

end Core

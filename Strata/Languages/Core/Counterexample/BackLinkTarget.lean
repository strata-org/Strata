/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkExact
public import Strata.Languages.Core.Counterexample.BackLinkPhases
public import Strata.Languages.Core.Counterexample.RunTarget
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCall
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.Counterexample.BackLinkExact
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.RunProps
import all Strata.DL.Imperative.Counterexample.BackLinkProps
import all Strata.Languages.Core.Counterexample.BackLinkPhases
import all Strata.Languages.Core.Counterexample.Run
import all Strata.Languages.Core.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.ValuationToRun
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Counterexample targets: assertions and loop verification conditions

A back-link lifts a counterexample *for a target*, the obligation it violates.  An assertion is
named by its id (`AssertId`) and fires on a replay event.  A loop verification condition (VC:
the invariant at entry or after an iteration, the measure's lower bound or decrease) is not a
statement of the source program; it is named by the loop's metadata and the VC kind
(`LoopVCId`), and its failure is a run reaching the loop at the relevant moment in a store
where the VC's expression evaluates to false.

`RunTarget` defines `Target`; `Counterexample.Run` defines `loopVCRun` (the
replay deciding a loop-VC target) and claim validity over targets, `genuineFeasibleT`
(`genuineFeasible` for an assertion, `loopVCRun` for a loop VC).

Key definitions: `directTargetBackLink` (the direct back-link of a target),
`TargetedBackLinkPreserves` (per-level preservation of a target-rewriting link),
`ForwardChainT` (a forward chain of such links), `callElimBackLinkT`.  Their properties
are in `BackLinkTargetProps`. -/

namespace Core

open Imperative
open BackLinkOutcome

public section

/-! ## Direct back-links over `Target`

The analogue of `directAssertionBackLink` for every kind of target: rebuild the top of the
source unit from the environment and oracle of the incoming chain's head, and decide the
target there.  A loop VC or a point check is decided by its walk (`loopVCRun`,
`pointRun`) at the shared replay fuel; an assertion, or a declaration check (an assertion
of its derived unit), by `directAssertionBackLink`. -/

/-- Direct back-link for a target decided by `check`: the rebuilt top claims the target
    when `check` accepts it at the shared replay fuel, and is otherwise kept as an
    unconfirmed slice. -/
@[expose] def directCheckedBackLink (name : String)
    (check : Nat → CexA Expression Command → Bool) : BackLink Expression Command Command where
  name := name
  lift := fun st incoming =>
    match incoming.chain.head? with
    | none => .empty
    | some inTop =>
      if st.isEmpty then .empty else
        let top : CexA Expression Command :=
          { cfg := .stmts st inTop.cfg.getEnv,
            oracle := inTop.oracle }
        if check replayFuelGuess top then ⟨[], some (top, replayFuelGuess)⟩
        else ⟨[top], none⟩

/-- Direct back-link for a loop-VC target. -/
@[expose] def directLoopVCBackLink (π : String → Option Procedure) (id : LoopVCId)
    (name : String) : BackLink Expression Command Command :=
  directCheckedBackLink name (loopVCRun π id)

/-- Direct back-link for a point-check target. -/
@[expose] def directPointBackLink (π : String → Option Procedure) (id : PointCheckId)
    (name : String) : BackLink Expression Command Command :=
  directCheckedBackLink name (pointRun π id)

/-- **The direct back-link of a target**: `directAssertionBackLink` for an assertion and
    for a declaration check (at its assertion), the checked direct back-link deciding by
    `loopVCRun` for a loop VC and by `pointRun` for a point check. -/
@[expose] def directTargetBackLink (π : String → Option Procedure) (name : String) :
    Target → BackLink Expression Command Command
  | .assert a => directAssertionBackLink π a name
  | .loopVC id => directLoopVCBackLink π id name
  | .atPoint id => directPointBackLink π id name
  | .declCheck id => directAssertionBackLink π id.check name

/-! ## Target-threading composition over `Target`

`composeTargeted` instantiates each link at the target as rewritten by the links
downstream of it (`TargetedBackLink.upstream`).  Validity is then per level: the
outcome at a phase's output is valid for the target there, and the lifted outcome at
its input is valid for the rewritten target. -/

/-- Per-level preservation for a target-rewriting link: for every target `t` at the
    phase's output, an outcome valid for `t` at the output unit lifts to one valid for
    `link.upstream t` at the input unit, the link being built at `link.upstream t`. -/
@[expose] def TargetedBackLinkPreserves (π : String → Option Procedure)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command)))
    (link : TargetedBackLink Expression Command Target) : Prop :=
  ∀ t st st', T st = some st' →
    ∀ o, ValidOutcomeOf (genuineFeasibleT π) t st' o →
      ValidOutcomeOf (genuineFeasibleT π) (link.upstream t) st
        ((link.build (link.upstream t)).lift st o)

/-- Forward chain of target-rewriting passes, in forward order, mapping the
    global-source unit to the final unit, each with its per-level preservation fact. -/
inductive ForwardChainT (π : String → Option Procedure) :
    List (TargetedBackLink Expression Command Target) →
    List (List (Stmt Expression Command) → Option (List (Stmt Expression Command))) →
    List (Stmt Expression Command) → List (Stmt Expression Command) → Type where
  | nil (st : List (Stmt Expression Command)) : ForwardChainT π [] [] st st
  | cons (link) (T) (links) (Ts) (st mid last : List (Stmt Expression Command))
      (hpres : TargetedBackLinkPreserves π T link) (hstep : T st = some mid)
      (rest : ForwardChainT π links Ts mid last) :
      ForwardChainT π (link :: links) (T :: Ts) st last

/-- The per-link input units a `ForwardChainT` traverses, in forward order. -/
@[expose] def ForwardChainT.inputUnits {π} {links Ts} {st st' : List (Stmt Expression Command)} :
    ForwardChainT π links Ts st st' → List (List (Stmt Expression Command))
  | .nil _ => []
  | .cons _ _ _ _ st _ _ _ _ rest => st :: rest.inputUnits

/-- The call-elimination back-link over `Target`: `callElimBackLink` for an assertion
    target, the direct back-link of the target otherwise. -/
@[expose] def callElimBackLinkT (π : String → Option Procedure)
    (origins : List CallElim.CallOrigin) : Target → BackLink Expression Command Command
  | .assert a => callElimBackLink π a origins
  | t => directTargetBackLink π "callElim" t

end -- public section

end Core

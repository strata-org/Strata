/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.InterpreterReplay
public import Strata.DL.Imperative.InterpreterProps
public import Strata.DL.Imperative.InterpreterObs
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterObs
import Strata.Languages.Core.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterObsProps
import all Strata.Languages.Core.Interpreter
import all Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.InterpreterReplayProps

/-! # Properties of Core counterexample replay

Lemmas about the definitions of `Core/InterpreterReplay.lean`.

Key theorems:
* `replayM_choose_cons`: `choose` with a validating oracle head consumes it.
* `assertFailureHalt_fires`, `assertFailureHalt_fires_cover`: when the target predicate fires.
* `pathFeasible_nil`, `pathFeasible_cons`: `PathFeasible` on an empty and a non-empty trace.
* `genuine_iff`: `genuine` holds iff the replay trace contains an event firing the target
  predicate. -/

namespace Core

open Imperative

public section

/-! ## `ReplayM` run lemmas at the projection `(((· .run cfg).run).run st)` -/

/-- `choose` with a validating oracle head `v` pops it, logs it in `usedRev`, and returns
    `.ok v`. -/
theorem replayM_choose_cons (factory : Lambda.Factory CoreLParams) (store : RStore Expression)
    (ty : Expression.Ty) (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (v : Expression.Expr) (rest : List Expression.Expr)
    (hrem : st.remaining = v :: rest)
    (hval : ((InterpLang.ops (P := Expression)).isValue factory v
              && (InterpLang.ops (P := Expression)).hasType factory v ty) = true) :
    (((InterpEffects.choose (m := ReplayM Expression) factory store ty).run cfg).run).run st
      = (.ok v, { st with remaining := rest, usedRev := v :: st.usedRev }) :=
  replayRun_choose_cons _ _ _ _ _ _ _ hrem (by simp_all) (by simp_all)

/-! ## When the target predicate fires -/

/-- `assertFailureHalt` fires on a target assert whose condition is the false literal. -/
theorem assertFailureHalt_fires (target : AssertId Expression) (f : Nat) (arg : REventArg Expression (Lambda.Factory CoreLParams))
    (hl : target.label = arg.label) (he : target.md = arg.metadata)
    (hff : evalBounded f arg.factory arg.store arg.expr = some (HasBool.ff (P := Expression))) :
    assertFailureHalt target f (.assert arg) = true := by
  simp +decide [Calls.assertFailureHalt, InterpLang.boundedEval, hl, he, hff]

/-- `assertFailureHalt` fires on a target cover whose condition is the true literal. -/
theorem assertFailureHalt_fires_cover (target : AssertId Expression) (f : Nat)
    (arg : REventArg Expression (Lambda.Factory CoreLParams))
    (hl : target.label = arg.label) (he : target.md = arg.metadata)
    (htt : evalBounded f arg.factory arg.store arg.expr = some (HasBool.tt (P := Expression))) :
    assertFailureHalt target f (.cover arg) = true := by
  simp +decide [Calls.assertFailureHalt, InterpLang.boundedEval, hl, he, htt]

/-! ## Path feasibility and the `genuine` verdict -/

/-- The empty trace is path-feasible: it records no assume that could fail. -/
theorem pathFeasible_nil (fuel : Nat) : PathFeasible fuel [] := nofun

/-- `e :: evs` is path-feasible (every `.assume` in it evaluates to `tt` up to metadata) iff `e`,
    if an `.assume`, evaluates to `tt` up to metadata and `evs` is path-feasible. -/
theorem pathFeasible_cons {fuel : Nat} {e : IEvent Expression}
    {evs : List (IEvent Expression)} :
    PathFeasible fuel (e :: evs) ↔
      (∀ arg, e = REvent.assume arg →
        (evalBounded fuel arg.factory arg.store arg.expr).bind
          (InterpLang.boolLit? (P := Expression)) = some true)
      ∧ PathFeasible fuel evs :=
  ⟨fun h => ⟨fun a he => h a (he ▸ .head _), fun a ha => h a (.tail _ ha)⟩,
    fun ⟨h1, h2⟩ a ha => (List.mem_cons.1 ha).elim (fun he => h1 a he.symm) (h2 a)⟩

/-- **`genuine` holds iff the strict replay trace contains a target event that fires**: a
    target assert whose condition evaluates to `ff`, or a target cover whose condition evaluates
    to `tt` (`assertFailureHalt target fuel`). -/
theorem genuine_iff (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (cex : CexA Expression Command) :
    genuine π target fuel cex ↔
        ∃ ev ∈ (runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel cex.cfg)
                  { oracleConfig := .strict }
                  cex.oracle).2.traceRev,
          assertFailureHalt target fuel ev = true := runReplay_genuine_iff ..

end
end Core

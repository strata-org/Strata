/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.Counterexample.Run
public import Strata.Languages.Core.Counterexample.BackLink
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Languages.Core.Counterexample.RunProps
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink
public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.Languages.Core.InterpreterInterruptBridge
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterCFG
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplayProps
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Imperative.Counterexample.Tactics
public import Strata.Util.ListUtilsProps

/-! # Replay-vs-replay domination: definitions

The relational context `RelCtx` relating a downstream replay run to an upstream one, the state
relation `StRel`, domination of one computation by another (`RelDom`), its equality instance
(`RelCtx.EqCompat`), the per-command obligation `StepDom`, and `IsReplaySimulation`.  The
combinators and the claim transport are in `BackLinkSimProps`. -/

namespace Core

open Imperative

public section

/-! ## Runs and growth -/

/-- The full `ReplayM` run projection. -/
abbrev rrun {α : Type} (X : ReplayM Expression α) (cfg : ReplayCfg Expression)
    (s : ReplayState Expression) : Except StopReason α × ReplayState Expression :=
  ((X.run cfg).run).run s

/-- `X` only ever prepends to the recorded trace. -/
@[expose] def Grows {α : Type} (cfg : ReplayCfg Expression) (X : ReplayM Expression α) : Prop :=
  ∀ s, s.traceRev <:+ (rrun X cfg s).2.traceRev

/-! ## `Grows` combinators -/

/-! ## Contexts and state relation -/

/-- The two run configurations of a relational simulation, the target predicate of each
    side, and the event relation. -/
structure RelCtx where
  cfgD : ReplayCfg Expression
  cfgU : ReplayCfg Expression
  haltD : IEvent Expression → Bool
  haltU : IEvent Expression → Bool
  ER : IEvent Expression → IEvent Expression → Prop
  /-- Events only the downstream run emits (the phase inserted them); they never fire
      the downstream target predicate. -/
  Extra : IEvent Expression → Prop := fun _ => False
  /-- The upstream run never draws from the oracle, so the two oracle cursors need not
      agree. -/
  freeOracle : Bool := false

/-- Both runs answer nondeterminism strictly from the oracle; a related event that fires
    downstream fires upstream; a related event that does not stop the downstream run
    either does not stop the upstream run or fires the upstream target predicate. -/
structure RelCtx.Compat (K : RelCtx) : Prop where
  strictD : K.cfgD.oracleConfig = .strict
  strictU : K.cfgU.oracleConfig = .strict
  halt : ∀ ev' ev, K.ER ev' ev → K.haltD ev' = true → K.haltU ev = true
  hook : ∀ ev' ev, K.ER ev' ev → K.cfgD.interruptOn ev' = none →
    K.cfgU.interruptOn ev = none ∨ K.haltU ev = true
  extra : ∀ ev', K.Extra ev' → K.haltD ev' = false

/-- Related traces: pointwise related by `K.ER`, the downstream trace also holding
    events only it emits (`K.Extra`). -/
inductive TraceRel (K : RelCtx) : List (IEvent Expression) → List (IEvent Expression) → Prop where
  | nil : TraceRel K [] []
  | cons {a b l l'} : K.ER a b → TraceRel K l l' → TraceRel K (a :: l) (b :: l')
  | extra {a l l'} : K.Extra a → TraceRel K l l' → TraceRel K (a :: l) l'

/-- Related replay states: the same oracle cursor (unless `K.freeOracle`) and related
    traces. -/
@[expose] def StRel (K : RelCtx) (s' s : ReplayState Expression) : Prop :=
  (K.freeOracle = true ∨ s'.remaining = s.remaining) ∧
    (K.freeOracle = true ∨ s'.usedRev = s.usedRev) ∧ TraceRel K s'.traceRev s.traceRev

/-- The downstream state has recorded an event firing the downstream target predicate. -/
@[expose] def FiredD (K : RelCtx) (s : ReplayState Expression) : Prop :=
  ∃ ev ∈ s.traceRev, K.haltD ev = true

/-- The upstream state has recorded an event firing the upstream target predicate. -/
@[expose] def FiredU (K : RelCtx) (s : ReplayState Expression) : Prop :=
  ∃ ev ∈ s.traceRev, K.haltU ev = true

/-! ## Relational domination of one computation -/

/-- Downstream-by-upstream relational domination: from related states, a downstream
    success is matched by an upstream success with related results and states (or the
    upstream run has fired); a downstream failure whose state has fired is matched by an
    upstream run that has fired.  The upstream computation only grows its trace. -/
@[expose] def RelDom {α' α : Type} (K : RelCtx) (X' : ReplayM Expression α')
    (X : ReplayM Expression α) (Ra : α' → α → Prop) : Prop :=
  Grows K.cfgU X ∧ ∀ s' s, StRel K s' s →
    (∀ a' s'1, rrun X' K.cfgD s' = (.ok a', s'1) →
      (∃ a s1, rrun X K.cfgU s = (.ok a, s1) ∧ Ra a' a ∧ StRel K s'1 s1) ∨
        FiredU K (rrun X K.cfgU s).2) ∧
    (∀ e s'1, rrun X' K.cfgD s' = (.error e, s'1) → FiredD K s'1 →
      FiredU K (rrun X K.cfgU s).2)

/-! ## The equality instance -/

/-- A relational context of runs that agree on events: compatible, the oracle cursors kept
    equal (`freeOracle` unset), and every event related to itself. -/
structure RelCtx.EqCompat (K : RelCtx) : Prop where
  compat : K.Compat
  oracle : K.freeOracle = false
  refl : ∀ ev, K.ER ev ev

/-! ## Base commands and single steps -/

/-! ## The whole run, from a per-command obligation -/

/-- Per-command obligation of a replay simulation: the downstream command stepper at
    fuel `k` is dominated by the upstream one at any fuel `k' ≥ k`, results related by
    equality. -/
@[expose] def StepDom (K : RelCtx) (sc' sc : StepCmdM Expression Command (ReplayM Expression)) :
    Prop :=
  ∀ k k' env cmd, k ≤ k' → RelDom K (sc' k env cmd) (sc k' env cmd) Eq

/-- Every command step grows the trace. -/
@[expose] def StepGrows (cfg : ReplayCfg Expression)
    (sc : StepCmdM Expression Command (ReplayM Expression)) : Prop :=
  ∀ k env cmd, Grows cfg (sc k env cmd)

/-! ## CFG callee bodies -/

/-! ## The Core command stepper -/

/-! ## Claim transport, proved once -/

/-- The production (enforcing) replay configuration of `genuineEnforced`. -/
@[expose] def prodCfg (target : AssertId Expression) (fuel : Nat) : ReplayCfg Expression :=
  { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }

/-- The relational context of two production runs: downstream target `t'` at fuel `f`,
    upstream target `t` at fuel `f'`, events related by `ER`. -/
@[expose] def relProdCtx (t' t : AssertId Expression) (f f' : Nat)
    (ER : IEvent Expression → IEvent Expression → Prop)
    (Extra : IEvent Expression → Prop := fun _ => False) (free : Bool := false) : RelCtx :=
  { cfgD := prodCfg t' f, cfgU := prodCfg t f', haltD := assertFailureHalt t' f,
    haltU := assertFailureHalt t f', ER := ER, Extra := Extra, freeOracle := free }

/-- What an event relation must transfer between the two production runs: a related
    event firing the downstream target fires the upstream one, and a related event the
    downstream production hook lets through is let through upstream or fires the
    upstream target. -/
structure EventTransfer (t' t : AssertId Expression) (f f' : Nat)
    (ER : IEvent Expression → IEvent Expression → Prop) : Prop where
  halt : ∀ ev' ev, ER ev' ev → assertFailureHalt t' f ev' = true → assertFailureHalt t f' ev = true
  hook : ∀ ev' ev, ER ev' ev → enforceInterrupt t' f ev' = none →
    enforceInterrupt t f' ev = none ∨ assertFailureHalt t f' ev = true

/-- **Replay simulation between two procedure tables**: under every equality-instance
    relational context (`RelCtx.EqCompat`), Core's command stepper over the downstream table
    `π'` is dominated by the one over the upstream table `π` (downstream fuel `≤` upstream
    fuel, results related by equality), at every call-depth budget. -/
@[expose] def IsReplaySimulation (π' π : String → Option Procedure) : Prop :=
  ∀ K : RelCtx, K.EqCompat → ∀ d,
    StepDom K (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d)

end -- public section

end Core

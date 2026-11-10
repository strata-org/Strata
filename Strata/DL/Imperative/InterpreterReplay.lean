/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Interpreter

/-! # `ReplayM`: the counterexample-replay instance of `InterpEffects`, and `runReplay`

`ReplayM` reads a `ReplayCfg`, throws `StopReason`, and threads a `ReplayState` (oracle tail,
consumed-choice log, event trace) that survives a throw.  `runReplayRun` runs a `ReplayM`
program from an oracle; `runReplay` runs it and classifies the run (`CEValidationVerdict`).

Lemmas about these definitions (`runReplay_genuine_iff`, the run lemmas `replayM_run_*`) are in
`InterpreterReplayProps.lean`. -/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type}

/-- How a `choose` is answered once the oracle is empty: `strict` fails, `withDefaults`
    synthesizes a value. -/
inductive OracleMode (P : PureExpr) [InterpLang P] where
  | strict
  | withDefaults (getDefault : InterpLang.RFactory P → RStore P → P.Ty → Option P.Expr)

/-- The per-run configuration of a replay run. -/
structure ReplayCfg (P : PureExpr) [InterpLang P] where
  /-- Oracle-exhaustion policy: `strict` (fail) vs `withDefaults` (synthesize). -/
  oracleConfig : OracleMode P := .strict
  /-- Emit stop hook: `emit` records `ev`, then throws `r` iff `interruptOn ev = some r`.  The
      default `fun _ => none` makes `emit` record-only. -/
  interruptOn : IEvent P → Option StopReason := fun _ => none

/-- Mutable state of a replay run. -/
structure ReplayState (P : PureExpr) [InterpLang P] where
  remaining : List P.Expr
  usedRev : List P.Expr := []
  /-- Every emitted event, most recent first. -/
  traceRev : List (IEvent P) := []

/-- `ReaderT` the config over `ExceptT StopReason` over the state; the state survives a throw. -/
abbrev ReplayM (P : PureExpr) [InterpLang P] :=
  ReaderT (ReplayCfg P) (ExceptT StopReason (StateT (ReplayState P) Id))

instance [HasBool P] [DecidableEq P.Expr] [InterpLang P] : InterpEffects P (ReplayM P) where
  choose factory store ty := do
    let cfg ← read
    let ops := InterpLang.ops (P := P)
    let validate (v : P.Expr) : ReplayM P P.Expr :=
      if ops.isValue factory v && ops.hasType factory v ty then
        modify (fun st => { st with usedRev := v :: st.usedRev }) *> pure v
      else throw .illTypedValue
    match (← get).remaining with
    | v :: rest => modify (fun st => { st with remaining := rest }) *> validate v
    | [] =>
      match cfg.oracleConfig with
      | .strict => throw .oracleExhausted
      | .withDefaults getDefault =>
        match getDefault factory store ty with
        | some d => validate d
        | none => throw .oracleExhausted
  emit ev := do
    modify fun st => { st with traceRev := ev :: st.traceRev }
    let cfg ← read
    -- Record first, then throw iff the stop hook fires on this event.
    match cfg.interruptOn ev with
    | none => pure ()
    | some r => throw r

/-- Run a `ReplayM` computation from the oracle to its `(outcome, final-state)` pair. -/
def runReplayRun [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (driver : ReplayM P (IConfig P CmdT)) (cfg : ReplayCfg P) (oracle : List P.Expr) :
    Except StopReason (IConfig P CmdT) × ReplayState P :=
  ((driver.run cfg).run).run { remaining := oracle }

/-- Run a `ReplayM` computation and classify it: *genuine* iff some emitted event fires
    `haltOn` (checked first), else *cantValidate* on an error, else *spurious*; also returns
    the consumed oracle. -/
def runReplay [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (driver : ReplayM P (IConfig P CmdT)) (cfg : ReplayCfg P) (haltOn : IEvent P → Bool)
    (oracle : List P.Expr) :
    CEValidationVerdict StopReason × List P.Expr :=
  let (res, st) := runReplayRun driver cfg oracle
  let verdict :=
    if st.traceRev.any (fun ev => haltOn ev) then .genuine
    else match res with
      | .error r => .cantValidate r
      | .ok _ => .spurious
  (verdict, st.usedRev.reverse)

end -- public section

end Imperative

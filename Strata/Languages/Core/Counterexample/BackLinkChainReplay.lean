/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.InterpreterInterruptBridge
public import Strata.Languages.Core.ReplayWF
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.Languages.Core.Counterexample.Model
public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Languages.Core.ObligationExtraction
public import Strata.DL.Imperative.Counterexample.Valuation
public import Strata.Languages.Core.Counterexample.Run
public import Strata.Languages.Core.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.Counterexample.Run
import all Strata.Languages.Core.Counterexample.BackLink
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Chain replay with slice merging (the shared standard replay step)

A `BackLinkOutcome`'s chain is a list of slices of one putative counterexample, in
execution order, with the gaps between consecutive slices *unconfirmed*: nothing says
the run from an earlier slice ever reaches the next one.  This module supplies the one
replay step every replay-based back-link runs to close such gaps:

replay from a slice `sᵢ` (consuming its oracle) step by step, and stop at the first of

* the **target firing** (a false assert / true cover at the target id) — `sᵢ`, extended
  by the oracle consumed so far, is then a counterexample in its own right;
* **reaching the start of a later slice `sⱼ`** — the two slices merge into
  `(sᵢ.cfg, consumed-prefix ++ sⱼ.oracle)`, the slices strictly between them are
  dropped, and the walk continues from the merged slice;
* **any other stop** (fuel or oracle exhausted, an engine refusal) — `sᵢ` is kept as
  an unconfirmed slice and the walk restarts from `sᵢ₊₁`.

"Reaching the start of `sⱼ`" is `configMatches`: the same program point exactly, and
stores that agree on an over-approximation of the variables the rest of the run may
read (`IConfig.readVars`).  Agreement is decided on that finite list.

Soundness does not rest on the walk: a claim the walk proposes is only returned after
one `replayCandidate` re-validation at its fuel (`chainReplayClaim`), so a merge the
replay does not actually support is discarded rather than trusted.

Both replays step the monadic interpreter over its own configurations (`IConfig`) from the
slice's configuration; stop points are compared with the interpreter's bookkeeping forgotten
(`IConfig.norm`).

Key definitions: `sliceRun`, `chainWalk`, `chainReplayClaim`, `chainReplayOutcome`. -/

namespace Core

open Imperative

public section

/-! ## The variables the rest of a run may read

The agreement check reads the variables `IConfig.readVars` lists.
A call is covered by its actuals and targets because Core has no global variables: the
callee starts from a fresh frame built only from the passed values (`callEntryStore`), its
internal variables are gone once it returns, and its outputs land in the caller's targets,
whose later reads are covered by the caller's own continuation.  `IConfig` has no
active-call-frame constructor: `replayStepCmd` runs a callee body to completion inside the
single interpreter step of its `.call`, so every configuration the step-by-step walk
(`attemptSlice`) inspects is at the caller's level, and the walk never matches a slice
start that lies inside a callee body. -/


/-- Same program point: `IConfig.samePointN` on the two configurations with the interpreter's
    bookkeeping forgotten (`IConfig.norm`). -/
def samePoint (c c' : IConfig Expression Command) : Bool :=
  IConfig.samePointN c.norm c'.norm

/-- Do the two stores agree on every variable of `vars`, both undefined or both defined with
    values equal up to metadata (`InterpLang.eqModuloMeta`)?  Decidable because `vars` is
    finite, unlike equality of the stores themselves (a store is a function). -/
def storesAgreeOn (σ σ' : RStore Expression) (vars : List Expression.Ident) : Bool :=
  vars.all fun x =>
    match σ x, σ' x with
    | some v, some v' => InterpLang.eqModuloMeta v v'
    | none, none => true
    | _, _ => false

/-- The walk's slice-start match of an interpreter configuration against a slice start: the same
    program point, and stores agreeing on an over-approximation of the variables the rest of the
    run may read. -/
def configMatches (current target : IConfig Expression Command) : Bool :=
  samePoint current target &&
    storesAgreeOn current.getEnv.store.get target.getEnv.store.get (IConfig.readVars target)

/-! ## One replay attempt from a slice -/

/-- The outcome of walking one slice forward. -/
inductive AttemptResult where
  /-- The target fired; `used` is the oracle consumed up to and including the firing
      step. -/
  | fired (used : List Expression.Expr)
  /-- The run reached the start of the stop configuration at index `index`, having
      consumed `used`. -/
  | hit (index : Nat) (used : List Expression.Expr)
  /-- No target and no slice start was reached. -/
  | stuck
  deriving Repr

/-- Step-by-step replay from `cex`, at fuel `fuel`, stopping at the first target firing
    or the first configuration matching an element of `stops`.  `stops` is matched only
    after at least one step, so the starting configuration never matches itself.

    The replay runs in `withDefaults defaults` oracle mode: once `cex`'s oracle is
    exhausted (e.g. inside a callee body the slice's oracle never covered), a choice is
    resolved by `defaults`.  Every value drawn — from the oracle or synthesized — is
    recorded in the replay state's `usedRev` at its draw position, so `used` is exactly
    the oracle a strict replay needs to reproduce this run.  The replay starts from `cex`'s
    configuration. -/
def attemptSlice (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty →
      Option Expression.Expr) (fuel : Nat)
    (stops : List (IConfig Expression Command)) (cex : CexA Expression Command) :
    AttemptResult :=
  go fuel cex.cfg { remaining := cex.oracle } false
where
  /-- `budget` steps left; `started` records whether a step has been taken. -/
  go (budget : Nat) (c : IConfig Expression Command) (st : ReplayState Expression)
      (started : Bool) : AttemptResult :=
    if st.traceRev.any (assertFailureHalt target fuel) then
      .fired st.usedRev.reverse
    else
      match (if started then stops.findIdx? (configMatches c) else none) with
      | some i => .hit i st.usedRev.reverse
      | none =>
        match budget with
        | 0 => .stuck
        | budget + 1 =>
          match replayRun (stepInterp (replayStepCmd π defaultMaxCallDepth) fuel c)
              { oracleConfig := .withDefaults defaults } st with
          | (.error _, st') =>
            if st'.traceRev.any (assertFailureHalt target fuel) then
              .fired st'.usedRev.reverse
            else .stuck
          | (.ok c', st') => go budget c' st' true

/-! ## The slicing replay (shared run loop)

A back-link whose pass abstracts part of the execution (call elimination replaces a
call by its contract; loop elimination replaces iterations by an arbitrary one)
cannot follow the downstream counterexample through that part: the downstream run
picks the abstracted values freely.  It replays the *source* instead, and at every
abstracted point it *cuts*: it closes the current slice, takes the values the
downstream picked from the oracle, and opens a new slice at the continuation.  The
gap between the two slices is an open reachability question, which the chain walk
(`chainWalk`) later tries to close with a real replay.

`sliceRun` is the one run loop; the pass-specific part is a `CutHandler`, consulted
before every interpreter step. -/

/-- What a pass-specific cut handler decides before a interpreter step. -/
inductive CutStep (H : Type) where
  /-- Take one ordinary interpreter step. -/
  | step
  /-- The handler's own check emitted a failing target occurrence; `st` is the replay
      state after the check. -/
  | fire (st : ReplayState Expression)
  /-- Stop the run: close the current slice with no claim. -/
  | stop
  /-- The handler took the step itself, without cutting: continue from `next` in state
      `st`, with handler state `h`. -/
  | moved (next : IConfig Expression Command) (st : ReplayState Expression) (h : H)
  /-- Cut: close the current slice with the oracle `closed` it consumed, and open a new
      one at `next`, whose oracle is `remaining`; continue from `next` with handler state
      `h`. -/
  | cut (next : IConfig Expression Command) (closed remaining : List Expression.Expr) (h : H)

/-- A pass-specific cut handler with state `H`: given its state, the eval fuel, the
    configuration about to be stepped and the replay state, decide what to do. -/
abbrev CutHandler (H : Type) :=
  H → Nat → IConfig Expression Command → ReplayState Expression → CutStep H

/-- The result of a slicing replay: the closed slices in execution order, and the
    claim (the last slice, with the oracle it consumed up to the target firing, and
    the fuel it must be re-checked at) if the target fired. -/
structure SliceResult where
  slices : List (CexA Expression Command)
  claim : Option (CexA Expression Command × Nat)

/-- Does the replay state record a failing occurrence of `target`? -/
def targetFired (target : AssertId Expression) (fuel : Nat) (st : ReplayState Expression) :
    Bool :=
  st.traceRev.any (assertFailureHalt target fuel)

/-- **The slicing replay.**  Replay step by step from `start` (strict oracle, callees
    resolved by `π`, eval fuel `fuel`, at most `fuel` interpreter steps, handler moves and
    cuts overall), consulting `handler` (initial state `h₀`) before each step.  The
    current slice is `(sliceStart, sliceOracle)`; the oracle it consumed so far is the
    replay state's `usedRev`.

    * the target fires (in a interpreter step or in the handler's check) — the current slice,
      with the oracle consumed up to the firing, becomes the claim at `fuel`;
    * the handler cuts — the current slice is closed with the oracle the handler says it
      consumed and a new slice opens at the handler's configuration with the handler's
      oracle;
    * the handler moves — the run continues from the handler's configuration and state;
    * anything else stops the run (fuel or oracle exhausted, an engine refusal, the end
      of the program, or the handler) — the current slice is closed with no claim and keeps the
      whole oracle it was opened with. -/
def sliceRun {H : Type} (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (handler : CutHandler H) (h₀ : H) (start : CexA Expression Command) :
    SliceResult :=
  go fuel h₀ start.cfg { remaining := start.oracle } start.cfg start.oracle []
where
  /-- `budget` interpreter steps left; `acc` the closed slices, most recent first. -/
  go (budget : Nat) (h : H) (c : IConfig Expression Command) (st : ReplayState Expression)
      (sliceStart : IConfig Expression Command) (sliceOracle : List Expression.Expr)
      (acc : List (CexA Expression Command)) : SliceResult :=
    let open_ : CexA Expression Command := { cfg := sliceStart, oracle := sliceOracle }
    let stopped : SliceResult := { slices := (open_ :: acc).reverse, claim := none }
    let claimAt (st' : ReplayState Expression) : SliceResult :=
      { slices := acc.reverse,
        claim := some ({ cfg := sliceStart, oracle := st'.usedRev.reverse }, fuel) }
    if targetFired target fuel st then claimAt st
    else if c.Done then stopped
    else
      match budget with
      | 0 => stopped
      | budget + 1 =>
        match handler h fuel c st with
        | .fire st' => claimAt st'
        | .stop => stopped
        | .moved next st' h' => go budget h' next st' sliceStart sliceOracle acc
        | .cut next closed remaining h' =>
          go budget h' next { remaining := remaining } next remaining
            ({ cfg := sliceStart, oracle := closed } :: acc)
        | .step =>
          match replayRun (stepInterp (replayStepCmd π defaultMaxCallDepth) fuel c)
              { oracleConfig := .strict } st with
          | (.error _, st') => if targetFired target fuel st' then claimAt st' else stopped
          | (.ok c', st') => go budget h c' st' sliceStart sliceOracle acc

/-! ## The chain walk -/

/-- The start configurations a walk may stop at: those of the slices `rest`, then the
    claim's (if any) last. -/
private def stopConfigs (rest : List (CexA Expression Command))
    (claim : Option (CexA Expression Command × Nat)) : List (IConfig Expression Command) :=
  rest.map (·.cfg) ++ claim.toList.map (·.1.cfg)

/-- Walk the chain `slices` (with trailing `claim`) merging slices, at per-attempt fuel
    `fuel`.  Returns the reduced chain: the slices kept unconfirmed, and the claim —
    the incoming one, one inherited through a merge, or one newly found by a target
    firing.  The claim this returns is a *proposal*: `chainReplayClaim` re-validates it
    before any back-link emits it. -/
def chainWalk (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty →
      Option Expression.Expr) (fuel : Nat)
    (slices : List (CexA Expression Command))
    (claim : Option (CexA Expression Command × Nat)) :
    List (CexA Expression Command) × Option (CexA Expression Command × Nat) :=
  match slices with
  | [] => ([], claim)
  | s :: rest =>
    match attemptSlice π target defaults fuel (stopConfigs rest claim) s with
    | .fired used =>
      -- The target is reached from `s` itself: it becomes the claim and every later
      -- slice is dropped.
      ([], some ({ cfg := s.cfg, oracle := used }, fuel))
    | .hit i used =>
      if hi : i < rest.length then
        -- Merge with the later slice `rest[i]`, dropping the slices in between, and
        -- continue from the merged slice.
        let sj := rest[i]
        let merged : CexA Expression Command := { cfg := s.cfg, oracle := used ++ sj.oracle }
        chainWalk π target defaults fuel (merged :: rest.drop (i + 1)) claim
      else
        -- The stop was the claim's own slice: the merged slice inherits the claim, with
        -- the fuel of this attempt added to the claim's fuel.
        match claim with
        | some (c, f) => ([], some ({ cfg := s.cfg, oracle := used ++ c.oracle }, fuel + f))
        | none => (s :: rest, claim)
    | .stuck =>
      let (kept, claim') := chainWalk π target defaults fuel rest claim
      (s :: kept, claim')
  termination_by slices.length
  decreasing_by all_goals grind

/-! ## The re-validated claim a back-link may emit -/

/-- Executable form of `isTopLevelAt`'s configuration test. -/
def isTopLevelAtB (stmts : List (Stmt Expression Command))
    (cfg : IConfig Expression Command) : Bool :=
  match cfg with
  | .stmts ss _ => decide (ss = stmts)
  | _ => false

/-- The guessed replay fuel used whenever a counterexample must be replayed without a
    fuel derived from the obligation.  A guess, not derived from the program: a replay
    that needs more is reported unconfirmed, never wrongly confirmed. -/
def replayFuelGuess : Nat := 10000

/-- Re-validate a candidate counterexample: run it under a default-filling,
    interrupt-on-target search, and if that reaches the failing target, strictly
    re-validate under the consumed oracle.  Returns the re-validated `CexA` with its
    fuel, or `none`. -/
@[expose] def replayCandidate (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidate : CexCandidateA Expression Command) (fuel : Nat) :
    Option (CexA Expression Command × Nat) :=
  if !candidate.sourceRelation candidate.cfg then none
  else
      let cfg : ReplayCfg Expression :=
        { interruptOn := enforceInterrupt target fuel,
          oracleConfig := .withDefaults defaults }
      match (runReplay (runCoreInterp (m := ReplayM Expression) π fuel candidate.cfg)
               cfg (assertFailureHalt target fuel) candidate.oracle) with
      | (.genuine, used) =>
        let cex : CexA Expression Command :=
          { cfg := candidate.cfg, oracle := used }
        match (runReplay (runCoreInterp (m := ReplayM Expression) π fuel cex.cfg)
                 { interruptOn := enforceInterrupt target fuel,
                   oracleConfig := .strict }
                 (assertFailureHalt target fuel) cex.oracle).1 with
        | .genuine => some (cex, fuel)
        | _ => none
      | _ => none

/-- Search an ordered candidate list (outermost first); first that validates. -/
@[expose] def replayCandidateLadder (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidates : List (CexCandidateA Expression Command)) (fuel : Nat) :
    Option (CexA Expression Command × Nat) :=
  candidates.findSome? fun c => replayCandidate π target defaults c fuel

/-- **The standard replay step of a back-link**, as a claim usable at the source unit
    `stmts`: walk the incoming outcome's chain merging slices, then *re-validate* the
    proposed claim with one `replayCandidate` at its fuel.  `none` unless the walk
    proposes a claim that both re-validates and is strictly inside `stmts` (a claim at
    the top of `stmts` is the top-level claim the back-link searches for directly, and
    is not routed through here).  The returned counterexample is `replayCandidate`'s
    own output. -/
@[expose] def chainReplayClaim (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty →
      Option Expression.Expr)
    (stmts : List (Stmt Expression Command)) (o : BackLinkOutcome Expression Command) :
    Option (CexA Expression Command × Nat) :=
  match (chainWalk π target defaults replayFuelGuess o.slices o.claim).2 with
  | none => none
  | some (cand, f) =>
    if isTopLevelAtB stmts cand.cfg then none
    else replayCandidate π target defaults { cfg := cand.cfg, oracle := cand.oracle } f

/-- **Chain replay as an outcome** at the source unit `stmts`, headed by the top-level
    slice `top`: walk the chain of `o` merging slices, then re-validate the proposed
    claim with one `replayCandidate` at its fuel.  A re-validated claim at the top of
    `stmts` is the lone claim `⟨[], some claim⟩`; one strictly inside `stmts` follows the
    unconfirmed `top`; no (re-validated) claim leaves `top` alone. -/
@[expose] def chainReplayOutcome (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty →
      Option Expression.Expr)
    (stmts : List (Stmt Expression Command)) (top : CexA Expression Command)
    (o : BackLinkOutcome Expression Command) : BackLinkOutcome Expression Command :=
  match (chainWalk π target defaults replayFuelGuess o.slices o.claim).2 with
  | none => ⟨[top], none⟩
  | some (cand, f) =>
    match replayCandidate π target defaults { cfg := cand.cfg, oracle := cand.oracle } f with
    | none => ⟨[top], none⟩
    | some claim =>
      if isTopLevelAtB stmts claim.1.cfg then ⟨[], some claim⟩ else ⟨[top], some claim⟩

end -- public section

end Core

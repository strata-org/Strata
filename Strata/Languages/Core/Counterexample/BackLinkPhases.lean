/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.InterpreterInterruptBridge
public import Strata.Languages.Core.Counterexample.BackLinkChainReplay
public import Strata.Languages.Core.Counterexample.BackLinkCallElim
public import Strata.Languages.Core.Counterexample.BackLinkLoopElim
public import Strata.Languages.Core.Counterexample.Model
public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Transform.LoopInitHoist
public import Strata.Languages.Core.Counterexample.BackLinkSliceWF
public import Strata.Languages.Core.Counterexample.BackLinkExact
public import Strata.DL.Imperative.Counterexample.RunProps
public import Strata.DL.Imperative.Counterexample.BackLinkProps
public import Strata.DL.Imperative.InterpreterCallEmbed
import Strata.DL.Imperative.InterpreterCallEmbedProps
import Strata.Languages.Core.Counterexample.BackLinkChainReplayProps
import Strata.Languages.Core.Counterexample.RunProps
public import Strata.DL.Lambda.OperationalSemanticsProps
public import Strata.DL.Lambda.LExprEvalProps
public import Strata.DL.Lambda.LExprEvalSound
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.Languages.Core.InterpreterEval
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.RunProps
import all Strata.DL.Imperative.Counterexample.BackLinkProps
import all Strata.Languages.Core.Counterexample.Run
import all Strata.Languages.Core.Counterexample.BackLink
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Counterexample back-links

The `(a)→(a)` back-links of the Core pipeline phases, and the `(b)→(a)` direct
back-link.  Level `(a)` is a run of the program: a `CexA`, a start configuration
replayed with an oracle of nondeterministic choices; level `(b)` is a valuation of a
proof obligation's variables.  Each back-link is a `BackLink Expression Command
Command` (`BackLink … (Cmd Expression) (Cmd Expression)` for the loop-init hoist)
whose `lift` re-validates candidates through the monadic interpreter's replay
(`replayCandidate`/`replayWithM`), keyed on the **target assertion id** `target`.

**Assertion ids are preserved across transforms.**  All five Core
transforms (`callElim`/`loopElim`/`nondetElim`/loop-init-hoist/`stmtsToCFG`) pass a
source `assert` command through *verbatim* — same label, same condition expr; none
substitutes/renames/havocs the expr inside a source assert or changes its label
(the only new asserts are transform-*synthesized* contract/measure asserts, which
are never the carried-through source assert a counterexample targets).  So each
back-link bakes the *same* `target` into its lift, and the structural
`composeBackLinks` composes them with no id remapping.

The preservation theorems are in `BackLinkPhasesProps`.

Key definitions: `directAssertionBackLink`, `ladderBackLink`, `nondetElimBackLink`,
`stmtsToCFGBackLink`, `slicedChainOutcome`, `unchangedUnitBackLink`, `plainOrSlicedLink`,
`callElimBackLink`, `loopElimBackLink`, `hoistBackLink`,
`BackLinkPreservesBase`. -/

namespace Core

open Imperative
open BackLinkOutcome

public section

/-- Default values for replay requests, by type: Booleans default to `false`, other
    types with a monomorphic form to their canonical default value, if any. -/
def nondetElimDefaults (_ : @Lambda.Factory CoreLParams) (_ : RStore Expression)
    (ty : Expression.Ty) : Option Expression.Expr :=
  if ty = HasBool.boolTy (P := Expression) then some (HasBool.ff (P := Expression))
  else match Lambda.LTy.toMonoType? ty with
    | some monoTy => defaultCanonicalValue monoTy
    | none => none

/-- The typed free variables of the leading `assume` statements of a unit (the
    preconditions of a procedure unit). -/
@[expose] def preconditionVars (st : List (Stmt Expression Command)) :
    List (Expression.Ident × Lambda.LMonoTy) :=
  (st.takeWhile fun s => match s with | .cmd (.cmd (.assume _ _ _)) => true | _ => false).flatMap
    fun s => match s with
      | .cmd (.cmd (.assume _ e _)) =>
        (Lambda.LExpr.freeVars e).filterMap fun (x, ty?) => ty?.map (x, ·)
      | _ => []

/-- A store completed for the unit `st`: a variable the store leaves unbound that the
    unit's preconditions read gets the canonical default value of its type.  A model
    need not bind an input the obligation does not constrain, but the unit assumes the
    preconditions before anything else, so its replay reads every input they mention; a
    default that violates a precondition only makes the replay infeasible. -/
@[expose] def completeStore (st : List (Stmt Expression Command)) (σ : RStore Expression) :
    RStore Expression := fun x =>
  match σ x with
  | some v => some v
  | none => ((preconditionVars st).lookup x).bind defaultCanonicalValue

/-- The environment the direct link replays the unit `st` from: the head's, with its
    store completed for `st` (`completeStore`). -/
@[expose] def directSourceEnv (st : List (Stmt Expression Command))
    (ρ : IEnv Expression) : IEnv Expression :=
  { ρ with store := .ofStore (completeStore st ρ.store.get) }

/-- Generic replay-based back-link, used for a phase with no back-link of its own.
    It rebuilds a top-level configuration of the phase's input unit `st` (the unit the
    forward pass processed), seeded with the starting store and oracle of the head of
    the incoming chain, and re-validates it by replay against the target
    id.  Claims the rebuilt top-level slice on success; otherwise tries chain replay on
    the incoming chain; otherwise returns the rebuilt slice as the lone unconfirmed
    slice.  An empty `st` (a unit the phase synthesized) or an empty incoming chain
    gives the empty outcome. -/
def directAssertionBackLink (π : String → Option Procedure) (target : AssertId Expression)
    (name : String) : BackLink Expression Command Command where
  name := name
  lift := fun st incoming =>
    match incoming.chain.head? with
    | none => .empty
    | some inTop =>
      if st.isEmpty then .empty else
        let statements := st
        let sourceEnv : IEnv Expression := directSourceEnv st inTop.cfg.getEnv
        let topCfg : IConfig Expression Command := .stmts statements sourceEnv
        let candidate : CexCandidateA Expression Command :=
          { cfg := topCfg, oracle := inTop.oracle }
        match replayCandidate π target (fun _ _ _ => none) candidate replayFuelGuess with
        | some top => ⟨[], some top⟩
        | none =>
          let topCex : CexA Expression Command := { cfg := topCfg, oracle := inTop.oracle }
          match chainReplayClaim π target (fun _ _ _ => none) statements incoming with
          | some merged => ⟨[topCex], some merged⟩
          | none => ⟨[topCex], none⟩

/-- The `(a)→(a)` top→inner ladder back-link named `name`: rebuild a top-level source slice
    at the source unit `st`, seeded from the oracle of the head of the incoming chain,
    and climb (claimed top → unconfirmed top with the claim of the chain-replay step
    `chainReplayClaim`, which merges the slices of the incoming chain → unconfirmed top
    with a claimed strictly-inner slice → unconfirmed top alone), re-validating through
    replay against `target`.  An empty `st` (a unit the phase synthesized, or a procedure
    with a CFG body) or an empty incoming chain gives an empty outcome. -/
@[expose] def ladderBackLink (name : String) (π : String → Option Procedure)
    (target : AssertId Expression) : BackLink Expression Command Command where
  name := name
  lift := fun st incoming =>
    match incoming.chain.head? with
    | none => .empty
    | some inTop =>
      if st.isEmpty then .empty else
        let sourceEnv : IEnv Expression := inTop.cfg.getEnv
        let topCfg : IConfig Expression Command := .stmts st sourceEnv
        let topCandidate : CexCandidateA Expression Command :=
          { cfg := topCfg, oracle := inTop.oracle }
        match replayCandidate π target nondetElimDefaults topCandidate replayFuelGuess with
        | some top => ⟨[], some top⟩
        | none =>
          let innerCandidates : List (CexCandidateA Expression Command) :=
            st.map fun s =>
              { cfg := (.stmt s sourceEnv : IConfig Expression Command)
                oracle := inTop.oracle }
          let topCex : CexA Expression Command :=
            { cfg := topCfg, oracle := inTop.oracle }
          match chainReplayClaim π target nondetElimDefaults st incoming with
          | some merged => ⟨[topCex], some merged⟩
          | none =>
            match replayCandidateLadder π target nondetElimDefaults innerCandidates
                replayFuelGuess with
            | some inner => ⟨[topCex], some inner⟩
            | none => ⟨[topCex], none⟩

/-- `(a)→(a)` back-link for `nondetElim`: the top→inner ladder `ladderBackLink`. -/
@[expose] def nondetElimBackLink (π : String → Option Procedure) (target : AssertId Expression) :
    BackLink Expression Command Command :=
  ladderBackLink "nondetElim" π target

/-- `(a)→(a)` back-link for `stmtsToCFG`: the top→inner ladder `ladderBackLink`. -/
@[expose] def stmtsToCFGBackLink (π : String → Option Procedure) (target : AssertId Expression) :
    BackLink Expression Command Command :=
  ladderBackLink "stmtsToCFG" π target

/-! ### Slicing back-links (`callElim`, `loopElim`)

A pass that abstracts part of the execution is inverted by slicing: each slice of the
incoming chain (at the pass's output) is replayed upstream by the pass's slicing replay,
from its start mapped upstream, with its own oracle; the pieces are concatenated in
order; and the chain replay tries to close the gaps through the real execution. -/

/-- Concatenate the upstream pieces (`piece d`, `none` for a slice with no upstream
    counterpart, dropped) of the downstream slices `ds` in order, after the slices
    `acc` already collected: the first piece that fires the target ends the chain with
    its claim (later pieces are not needed to explain the failure). -/
def concatSlicePieces (piece : CexA Expression Command → Option SliceResult)
    (acc : List (CexA Expression Command)) :
    List (CexA Expression Command) → BackLinkOutcome Expression Command
  | [] => ⟨acc, none⟩
  | d :: ds =>
    match piece d with
    | none => concatSlicePieces piece acc ds
    | some r =>
      match r.claim with
      | some c => ⟨acc ++ r.slices, some c⟩
      | none => concatSlicePieces piece (acc ++ r.slices) ds

/-- **The sliced lift** at the source unit `st`:

    * the head slice starts at the top of the source unit, `.stmts st σ₀` (`σ₀` the
      head's environment, adjusted by `topEnv`), with the head's oracle;
    * every later slice (and the claim slice) starts at its start mapped upstream by
      `mapCfg` (dropped if unmapped, never invented), with its own oracle;

    each is replayed upstream by `slice`; the pieces are concatenated
    (`concatSlicePieces`) and the chain replay (`chainReplayOutcome`) tries to close the
    gaps; its claim is re-validated before it is returned.  An empty `st` or an empty
    incoming chain gives the empty outcome. -/
@[expose] def slicedChainOutcome (π : String → Option Procedure) (target : AssertId Expression)
    (st : List (Stmt Expression Command))
    (topEnv : IEnv Expression → IEnv Expression)
    (slice : CexA Expression Command → SliceResult)
    (mapCfg : IConfig Expression Command → Option (IConfig Expression Command))
    (incoming : BackLinkOutcome Expression Command) : BackLinkOutcome Expression Command :=
  match incoming.chain with
  | [] => .empty
  | inTop :: rest =>
    if st.isEmpty then .empty else
      let top : CexA Expression Command :=
        { cfg := .stmts st (topEnv inTop.cfg.getEnv),
          oracle := inTop.oracle }
      let headPiece := slice top
      let upstream : BackLinkOutcome Expression Command :=
        match headPiece.claim with
        | some c => ⟨headPiece.slices, some c⟩
        | none =>
          concatSlicePieces
            (fun d => (mapCfg d.cfg).map fun c => slice { cfg := c, oracle := d.oracle })
            headPiece.slices rest
      chainReplayOutcome π target nondetElimDefaults st top upstream

/-- The upstream pieces of one downstream slice for `callElim`: `callElimSlice` from the
    slice's start mapped by `uncallElimConfig`, with the slice's own oracle. -/
def callElimSlicePiece (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallElim.CallOrigin) (d : CexA Expression Command) : Option SliceResult :=
  (uncallElimConfig origins
      d.cfg).map fun c => callElimSlice π target origins { cfg := c, oracle := d.oracle }

/-- `concatSlicePieces` over the `callElim` pieces `callElimSlicePiece`. -/
def callElimConcatPieces (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallElim.CallOrigin) (acc : List (CexA Expression Command))
    (ds : List (CexA Expression Command)) : BackLinkOutcome Expression Command :=
  concatSlicePieces (callElimSlicePiece π target origins) acc ds

/-- The replay-free back-link of a unit the phase left unchanged, at one procedure table:
    `exactBackLink` of the unchanged-unit certificate (`ExactCert.ofUnchangedUnit`).  It
    translates the chain of a unit equal to the phase's output unit, and nothing of the
    chain of a unit the phase changed (the head is then not at the unit's top). -/
@[expose] def unchangedUnitBackLink (π : String → Option Procedure) (name : String) :
    BackLink Expression Command Command :=
  exactBackLink name (ExactCert.ofUnchangedUnit (π' := π) (π := π)
    (isReplaySimulation_of_sub fun _ _ h => h) (fun st => some st))

/-- A sliced lift `sliced` that is skipped on the units `plain` accepts: there the link is the
    replay-free `unchangedUnitBackLink`, with `sliced` as the fallback where it translates
    nothing of a non-empty chain; on every other unit it is `sliced`. -/
@[expose] def plainOrSlicedLink (π : String → Option Procedure) (name : String)
    (plain : List (Stmt Expression Command) → Bool)
    (sliced : List (Stmt Expression Command) → BackLinkOutcome Expression Command →
      BackLinkOutcome Expression Command) : BackLink Expression Command Command where
  name := name
  lift := fun st o =>
    if plain st then
      let r := (unchangedUnitBackLink π name).lift st o
      if r.chain.isEmpty && !o.chain.isEmpty then sliced st o else r
    else sliced st o

/-- Is `target` the upstream id of no precondition check the pass generated: does no origin
    record an upstream id (`CallOrigin.preconditionTargets`) with the label of `target`?  Then
    `callElimUpstreamTarget` maps only `target` itself to `target`. -/
@[expose] def callElimNotGeneratedTarget (origins : List CallElim.CallOrigin)
    (target : AssertId Expression) : Bool :=
  origins.all fun o => o.preconditionTargets.all fun p => p.2.label != target.label

/-- `(a)→(a)` back-link for `callElim`, built at the *upstream* target (for a
    precondition assert the pass generated, the callee precondition's id,
    `callElimUpstreamTarget`): on a unit with no call (`Statements.noCalls`), for a target
    that is the upstream id of no generated check (`callElimNotGeneratedTarget`), the
    replay-free unchanged-unit link, falling back to the sliced lift where it translates nothing
    (`plainOrSlicedLink`); on any other unit the sliced lift (`slicedChainOutcome`) with the
    call-elimination slicer (`callElimSlice`, cutting at eliminated calls), downstream
    starts mapped by `uncallElimConfig`, and the pass's fresh variables dropped from the
    head's store. -/
@[expose] def callElimBackLink (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallElim.CallOrigin) : BackLink Expression Command Command :=
  plainOrSlicedLink π "callElim"
      (fun st => Statements.noCalls st && callElimNotGeneratedTarget origins target)
      fun st incoming =>
    slicedChainOutcome π target st (dropFreshEnv (callElimFreshVars origins))
      (callElimSlice π target origins) (uncallElimConfig origins) incoming

/-- `(a)→(a)` back-link for `loopElim`: on a unit with no loop (`Block.noLoops`) the
    replay-free unchanged-unit link, falling back to the sliced lift where it translates
    nothing (`plainOrSlicedLink`); on any other unit the sliced lift (`slicedChainOutcome`)
    with the loop-elimination slicer (`loopElimSlice`, cutting at loop entries and exits) and
    downstream starts mapped by `unloopElimConfig` over the phase's loop origins
    (`loopOriginsProgram`). -/
@[expose] def loopElimBackLink (π : String → Option Procedure) (target : AssertId Expression)
    (origins : LoopOrigins) : BackLink Expression Command Command :=
  plainOrSlicedLink π "loopElim" Block.noLoops fun st incoming =>
    slicedChainOutcome π target st id (loopElimSlice π target) (unloopElimConfig origins)
      incoming

/-! ### Base-command (`Cmd Expression`) replay — for the `loopInitHoist` back-link

`hoist` operates on the Imperative base-command language (`Cmd Expression`, no
`.call`).  A base program is a call-free `Command` program (`Calls.embedConfig`), and
on such a program the call-aware stepper performs exactly the base stepper's steps
(`Calls.runReplay_embedConfig`), so base-command replay is the one call-aware
replay path at the empty callee table: `replayCandidateBase` runs `replayCandidate`
on the embedded candidate and returns the validated counterexample at the base
representation. -/

/-- Base-command candidate search: `replayCandidate` at the empty callee table on the
    embedded candidate, with the validated counterexample returned at the base
    representation (same start config and oracle) together with its fuel. -/
@[expose] def replayCandidateBase (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidate : CexCandidateA Expression (Imperative.Cmd Expression))
    (fuel : Nat) : Option (CexA Expression (Imperative.Cmd Expression) × Nat) :=
  (replayCandidate (fun _ => none) target defaults (Calls.embedCandidate candidate) fuel).map
    fun r => ({ cfg := candidate.cfg, oracle := r.1.oracle }, r.2)

/-- Base-command candidate ladder: the first candidate `replayCandidateBase` validates,
    with its fuel. -/
@[expose] def replayCandidateLadderBase (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidates : List (CexCandidateA Expression (Imperative.Cmd Expression)))
    (fuel : Nat) : Option (CexA Expression (Imperative.Cmd Expression) × Nat) :=
  candidates.findSome? fun c => replayCandidateBase target defaults c fuel

/-- `(a)→(a)` back-link for the `loopInitHoist` pass (`Block.hoistLoopPrefixInits`), over the
    base-command language `Cmd Expression`: the top→inner ladder of `nondetElimBackLink`,
    replaying with `replayCandidate` under the empty callee table (`replayCandidateBase`).
    The pass lifts each loop body's prefix `init`s out as `havoc`s before the loop, and its
    forward map is `T st = some (Block.hoistLoopPrefixInits st)`, so the back-link replays the
    source unit `st` itself, seeded from the incoming top's oracle: the reordering needs no
    reconstruction.

    It does **not** run the shared chain-replay step: `chainReplayClaim` walks a chain
    at the call-aware `Command` representation, and a claim it produced would have to be
    carried back to the base representation, which the embedding `Calls.embedCexA` does
    not invert (a claim on an embedded configuration need not be the embedding of a base
    configuration).  This back-link therefore keeps the top→inner ladder only.  An empty
    `st` (a unit the phase synthesized) or an empty incoming chain gives the empty
    outcome. -/
@[expose] def hoistBackLink (target : AssertId Expression) :
    BackLink Expression (Imperative.Cmd Expression) (Imperative.Cmd Expression) where
  name := "loopInitHoist"
  lift := fun st incoming =>
    match incoming.chain.head? with
    | none => .empty
    | some inTop =>
      if st.isEmpty then .empty else
        let sourceEnv : IEnv Expression := inTop.cfg.getEnv
        let topCfg : IConfig Expression (Imperative.Cmd Expression) := .stmts st sourceEnv
        let topCandidate : CexCandidateA Expression (Imperative.Cmd Expression) :=
          { cfg := topCfg, oracle := inTop.oracle }
        match replayCandidateBase target nondetElimDefaults topCandidate replayFuelGuess with
        | some top => ⟨[], some top⟩
        | none =>
          let innerCandidates : List (CexCandidateA Expression (Imperative.Cmd Expression)) :=
            st.map fun s =>
              { cfg := (.stmt s sourceEnv : IConfig Expression (Imperative.Cmd Expression))
                oracle := inTop.oracle }
          let topCex : CexA Expression (Imperative.Cmd Expression) :=
            { cfg := topCfg, oracle := inTop.oracle }
          match replayCandidateLadderBase target nondetElimDefaults innerCandidates
              replayFuelGuess with
          | some inner => ⟨[topCex], some inner⟩
          | none => ⟨[topCex], none⟩

/-! ### Validity preservation at the base representation

`BackLinkPreservesBase` is the base-command form of `BackLinkPreserves`, for the loop-init
`hoistBackLink` at the `Cmd Expression` representation. -/

/-- Base-command outcome-validity preservation, stated on embeddings: whenever `T` maps
    the unit `st` to `st'`, a back-link over `Cmd Expression` lifts every outcome whose
    embedding is valid at the embedding of `st'` (`ValidOutcome` at the empty callee
    table) to one whose embedding is valid at the embedding of `st`. -/
def BackLinkPreservesBase (target : AssertId Expression)
    (T : List (Stmt Expression (Imperative.Cmd Expression)) → Option (List (Stmt Expression
        (Imperative.Cmd Expression))))
    (link : BackLink Expression (Imperative.Cmd Expression) (Imperative.Cmd Expression)) : Prop :=
  ∀ st st', T st = some st' →
    ∀ o, ValidOutcome (fun _ => none) target (Calls.embedBlock st') (Calls.embedOutcome o) →
      ValidOutcome (fun _ => none) target (Calls.embedBlock st)
        (Calls.embedOutcome (link.lift st o))

end -- public section

end Core

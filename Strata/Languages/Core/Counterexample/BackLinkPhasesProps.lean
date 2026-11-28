/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkPhases
import all Strata.Languages.Core.Counterexample.BackLinkPhases
import Strata.DL.Imperative.InterpreterCallEmbedProps
import Strata.Languages.Core.Counterexample.ValuationToRunSupportA
import Strata.Languages.Core.Counterexample.BackLinkChainReplayProps
import Strata.Languages.Core.Counterexample.RunProps
import Strata.Languages.Core.Counterexample.BackLinkExactProps
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

/-! # Validity preservation of the counterexample back-links

The back-links of `BackLinkPhases` map valid outcomes to valid outcomes.  An
outcome (`BackLinkOutcome`: a chain of unconfirmed slices, optionally ended by a claim)
is *valid* at a source unit `st` (`ValidOutcome`) when its chain head, if any, starts at
the top of `st`, its claim `(c, f)`, if any, replays genuinely and feasibly to the
target assertion at fuel `f` (`genuineFeasible`) and is not top-level when unconfirmed
slices precede it, and every chain element is well-formed (`CexWF`: every factory and
store of its start configuration is well-formed).  A back-link *preserves validity*
across a forward map `T` (`BackLinkPreserves`) when it lifts every outcome valid at the
image `T st` to one valid at `st`.

Validity is executable: it bottoms out in the result of the replay `replayWithM`, so
these results do not depend on a small-step semantics of `.call`.

Key theorems: `directAssertionBackLink_preserves`, `ladderBackLink_preserves`,
`nondetElimBackLink_preserves`, `stmtsToCFGBackLink_preserves`, `plainOrSlicedLink_preserves`,
`callElimBackLink_preserves`,
`loopElimBackLink_preserves`, `hoistBackLink_preserves`, `slicedChainOutcome_valid`.

Key definitions (`BackLinkPhases`): the back-links, `slicedChainOutcome`,
`BackLinkPreservesBase`. -/

namespace Core

open Imperative
open BackLinkOutcome

public section

/-- Completing a store for a unit (`completeStore`) keeps it closed (`StoreClosed`: every
    value has no free variables). -/
private theorem completeStore_closed (st : List (Stmt Expression Command))
    {σ : RStore Expression}
    (h : StoreClosed σ) : StoreClosed (completeStore st σ) := fun x v hx => by
  simp only [completeStore] at hx
  split at hx
  · cases hx; exact h _ _ ‹_›
  obtain ⟨ty, -, hdef⟩ := Option.bind_eq_some_iff.1 hx
  exact Lambda.isValue_getVars_nil .default _
    (defaultCanonicalValue_isCanonical _ _ _ hdef)

/-! ## Executable properties of the candidate search

A successful `replayCandidate` returns the candidate's start configuration at the
requested fuel, re-validated by a strict replay. -/

/-- A `replayCandidate` success keeps the candidate's start and fuel, with an oracle on
    which the strict replay, interrupted at the target, reports `.genuine`. -/
private theorem cel_rcInv {π : String → Option Procedure} {target : AssertId Expression}
    {defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr}
    {candidate : CexCandidateA Expression Command} {fuel : Nat} {cex : CexA Expression Command}
      {fuel' : Nat}
    (h : replayCandidate π target defaults candidate fuel = some (cex, fuel')) :
    ∃ used, cex = { cfg := candidate.cfg, oracle := used } ∧ fuel' = fuel ∧
      (runReplay (runCoreInterp (m := ReplayM Expression) π fuel candidate.cfg)
        { interruptOn := enforceInterrupt target fuel, oracleConfig := .strict }
        (assertFailureHalt target fuel) used).1 = .genuine := by
  simp only [replayCandidate] at h
  split at h <;> (try split at h) <;> (try split at h) <;> cases h
  exact ⟨_, rfl, rfl, ‹_›⟩

/-- `replayCandidate` returning `some (cex, fuel')` keeps the candidate's start config. -/
theorem replayCandidate_cfg (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidate : CexCandidateA Expression Command) (fuel : Nat)
    (cex : CexA Expression Command) (fuel' : Nat)
    (h : replayCandidate π target defaults candidate fuel = some (cex, fuel')) :
    cex.cfg = candidate.cfg := by
  obtain ⟨_, rfl, -⟩ := cel_rcInv h
  rfl

/-- `replayCandidate` returning `some (cex, fuel')` yields a `genuineFeasible` cex at
    `fuel'`: `genuine` (its replay reaches a failing occurrence of the target assertion),
    and the strict replay with interruption at the target at fuel `fuel'` has a
    `PathFeasible` trace (every assume on it holds). -/
theorem replayCandidate_genuineFeasible (π : String → Option Procedure)
    (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidate : CexCandidateA Expression Command) (fuel : Nat)
    (cex : CexA Expression Command) (fuel' : Nat)
    (h : replayCandidate π target defaults candidate fuel = some (cex, fuel')) :
    genuineFeasible π target fuel' cex := by
  obtain ⟨_, rfl, rfl, hg⟩ := cel_rcInv h
  exact ⟨runReplay_genuine_of_interruptOn _ _ _ _ _ _ _ hg,
    pathFeasible_of_runReplay_genuine_core (h := hg)⟩

/-- Every result `replayCandidate` returns is `genuineFeasible` at its fuel and starts at the
    candidate's configuration; the statement is `True` when it returns `none`. -/
private theorem replayCandidate_elim (π : String → Option Procedure)
    (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (cand : CexCandidateA Expression Command) (fuel : Nat) :
    (replayCandidate π target defaults cand fuel).elim True
      fun r => genuineFeasible π target r.2 r.1 ∧ r.1.cfg = cand.cfg := by
  cases h : replayCandidate π target defaults cand fuel
  · trivial
  · exact ⟨replayCandidate_genuineFeasible _ _ _ _ _ _ _ h, replayCandidate_cfg _ _ _ _ _ _ _ h⟩

/-- The head of an outcome's chain (the slices followed by the claimed slice, if any) is
    in the chain. -/
theorem BackLinkOutcome.mem_chain_of_head {P : PureExpr} [InterpLang P] {CmdT : Type}
    {o : BackLinkOutcome P CmdT} {x : CexA P CmdT} (h : o.chain.head? = some x) :
    x ∈ o.chain := List.mem_of_mem_head? h

/-- If every element of an outcome's chain is well-formed (`CexWF`: every factory and
    store of its start configuration is well-formed), the environment of the chain head
    is well-formed (`EnvWF`: a well-formed factory and a
    closed store). -/
theorem headEnv_wf {o : BackLinkOutcome Expression Command} {inTop : CexA Expression Command}
    (hwf : ∀ x ∈ o.chain, CexWF x) (ho : o.chain.head? = some inTop) :
    EnvWF inTop.cfg.getEnv := by
  apply_rules [CfgWF.getEnv, BackLinkOutcome.mem_chain_of_head]

/-- For an outcome whose chain elements are all well-formed (`CexWF`), a claim the chain
    walk `chainWalk` proposes, once `replayCandidate` re-validates it, is
    `genuineFeasible` (its replay reaches a failing target occurrence along a trace whose
    assumes hold), well-formed, and starts at the proposal's configuration. -/
private theorem cel_chainCand {π : String → Option Procedure} {target : AssertId Expression}
    {defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr}
    {o : BackLinkOutcome Expression Command} (hwf : ∀ x ∈ o.chain, CexWF x)
    {cand c : CexA Expression Command} {f f' : Nat}
    (hw : (chainWalk π target defaults replayFuelGuess o.slices o.claim).2 = some (cand, f))
    (hc : replayCandidate π target defaults { cfg := cand.cfg, oracle := cand.oracle } f = some
        (c, f')) :
    genuineFeasible π target f' c ∧ CexWF c ∧ c.cfg = cand.cfg :=
  have hcfg := replayCandidate_cfg _ _ _ _ _ _ _ hc
  ⟨replayCandidate_genuineFeasible _ _ _ _ _ _ _ hc,
    by simpa [CexWF, hcfg] using chainWalk_claim_wf _ _ _ _ _ _
        (fun _ h => hwf _ (by simp [chain, h])) (fun _ _ h => hwf _ (by simp [chain, h])) _ _ hw,
    hcfg⟩

/-- **Specification of the chain-replay step.**  For an outcome whose chain elements are
    all well-formed (`CexWF`), a claim `chainReplayClaim` returns is `genuineFeasible` at
    its fuel (its replay reaches a failing target occurrence along a trace whose assumes
    hold), does not start at the top of `stmts` (`isTopLevelAt`), and is well-formed. -/
private theorem chainReplayClaim_spec (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (stmts : List (Stmt Expression Command)) (o : BackLinkOutcome Expression Command)
    (hwf : ∀ x ∈ o.chain, CexWF x)
    (c : CexA Expression Command) (f : Nat)
    (h : chainReplayClaim π target defaults stmts o = some (c, f)) :
    genuineFeasible π target f c ∧ ¬ isTopLevelAt stmts c ∧ CexWF c := by
  simp only [chainReplayClaim] at h
  have hcand := @cel_chainCand π target defaults o hwf
  grind [not_isTopLevelAt_of_isTopLevelAtB_false]

/-! ## Validity preservation of each back-link

Each lift rebuilds and validates a source counterexample at its `st` argument and never
refers to the forward transform, so preservation holds for **any** forward map `T`. -/

/-- `ladderBackLink` preserves validity across any forward map `T`
    (`BackLinkPreserves`: whenever `T` maps a unit `st` to `st'`, the link lifts every
    outcome valid at `st'` to one valid at `st`), whatever its name. -/
theorem ladderBackLink_preserves (name : String) (π : String → Option Procedure)
    (target : AssertId Expression)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (ladderBackLink name π target) :=
    fun st _ _ o ⟨_, _, hwf⟩ => by
  simp only [ladderBackLink]
  split
  · exact validOutcome_empty ..
  split
  · exact validOutcome_empty ..
  have hhead := headEnv_wf hwf ‹_›
  have hrc := replayCandidate_elim π target nondetElimDefaults
  have hspec := chainReplayClaim_spec π target nondetElimDefaults st o hwf
  (repeat' split) <;> grind [ValidOutcomeOf, chain, CexWF, isTopLevelAt,
    List.exists_of_findSome?_eq_some, replayCandidateLadder, CfgWF]

/-- `nondetElimBackLink` preserves validity across any forward map `T`
    (`BackLinkPreserves`: whenever `T` maps a unit `st` to `st'`, the link lifts every
    outcome valid at `st'` to one valid at `st`). -/
theorem nondetElimBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (nondetElimBackLink π target) :=
  ladderBackLink_preserves "nondetElim" π target T

/-- `stmtsToCFGBackLink` preserves validity across any forward map `T`
    (`BackLinkPreserves`: whenever `T` maps a unit `st` to `st'`, the link lifts every
    outcome valid at `st'` to one valid at `st`). -/
theorem stmtsToCFGBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (stmtsToCFGBackLink π target) :=
  ladderBackLink_preserves "stmtsToCFG" π target T

/-- `directAssertionBackLink` lifts every outcome whose chain elements are all
    well-formed (`CexWF`) to an outcome valid at `st` (`ValidOutcome`: head at the top of
    `st`, claim genuine and feasible at its fuel, every element well-formed). -/
theorem cel_directValid (π : String → Option Procedure) (target : AssertId Expression)
    (name : String)
    (st : List (Stmt Expression Command)) (o : BackLinkOutcome Expression Command)
      (hwf : ∀ x ∈ o.chain, CexWF x) :
    ValidOutcome π target st ((directAssertionBackLink π target name).lift st o) := by
  simp only [directAssertionBackLink, List.isEmpty_iff]
  have hhead := @headEnv_wf
  have hrc := replayCandidate_elim π target fun _ _ _ => none
  have hspec := chainReplayClaim_spec π target (fun _ _ _ => none) st o hwf
  (repeat' split) <;> grind [ValidOutcomeOf, BackLinkOutcome.chain, BackLinkOutcome.empty, CexWF,
    isTopLevelAt, directSourceEnv, completeStore_closed, CfgWF, EnvWF, IStore.get_ofStore]

/-- `directAssertionBackLink` preserves validity across **any** forward map `T`
    (`BackLinkPreserves`: whenever `T` maps a unit `st` to `st'`, the link lifts every
    outcome valid at `st'` to one valid at `st`).  The link never trusts the incoming
    claim: its claim, if any, is re-validated by `replayCandidate` or `chainReplayClaim`;
    otherwise it returns the rebuilt `.stmts st env` as the lone unconfirmed slice, whose
    environment is the incoming head's with a completed store. -/
theorem directAssertionBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) (name : String)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (directAssertionBackLink π target
        name) := fun _ _ _ _ ⟨_, _, hwf⟩ => cel_directValid _ _ _ _ _ hwf

/-- **Validity of the chain-replay outcome**: for a well-formed (`CexWF`) slice `top` at
    the top of `stmts` and an outcome whose chain elements are all well-formed, the
    outcome `chainReplayOutcome` returns is valid at `stmts` (`ValidOutcome`: head at the
    top, claim genuine and feasible at its fuel, every element well-formed).  Its claim is
    `replayCandidate`'s re-validated output, placed alone exactly when it is top-level. -/
private theorem chainReplayOutcome_valid (π : String → Option Procedure)
    (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (stmts : List (Stmt Expression Command)) (top : CexA Expression Command)
    (o : BackLinkOutcome Expression Command) (ht : isTopLevelAt stmts top)
    (hwt : CexWF top) (hwf : ∀ x ∈ o.chain, CexWF x) :
    ValidOutcome π target stmts (chainReplayOutcome π target defaults stmts top o) := by
  unfold chainReplayOutcome
  have hcand := @cel_chainCand π target defaults o hwf
  (repeat' split) <;> grind [ValidOutcomeOf, chain, isTopLevelAt_of_isTopLevelAtB,
    not_isTopLevelAt_of_isTopLevelAtB_false]

/-- Every chain element of `concatSlicePieces piece acc ds` is well-formed (`CexWF`)
    when the elements of `acc` and `ds` are and every piece `piece` returns for a
    well-formed slice has well-formed slices and claim. -/
private theorem concatSlicePieces_wf (piece : CexA Expression Command → Option SliceResult)
    (hpiece : ∀ d r, piece d = some r → CexWF d →
      (∀ x ∈ r.slices, CexWF x) ∧ ∀ c f, r.claim = some (c, f) → CexWF c) :
    ∀ (acc ds : List (CexA Expression Command)), (∀ x ∈ acc, CexWF x) → (∀ x ∈ ds, CexWF x) →
      ∀ x ∈ (concatSlicePieces piece acc ds).chain, CexWF x
  | acc, [], hacc, _ => by simpa [concatSlicePieces, chain] using hacc
  | acc, d :: ds, hacc, hds => by
    simp only [concatSlicePieces]
    split
    · exact concatSlicePieces_wf _ hpiece acc _ hacc fun x hx => hds x (by simp [hx])
    split
    · grind [chain]
    exact concatSlicePieces_wf _ hpiece _ _ (by grind) fun x hx => hds x (by simp [hx])

/-- **Validity of the sliced lift**: for an incoming outcome whose chain elements are all
    well-formed (`CexWF`), `slicedChainOutcome` returns an outcome valid at `st`
    (`ValidOutcome`: head at the top of `st`, claim genuine and feasible at its fuel, every
    element well-formed), provided `topEnv` keeps environments well-formed (`EnvWF`), the
    slicer `slice` maps a well-formed start to well-formed slices and claim, and the start
    map `mapCfg` keeps configurations well-formed (`CfgWF`).  The head is the top of `st`
    by construction and the claim is re-validated by the chain replay. -/
theorem slicedChainOutcome_valid (π : String → Option Procedure) (target : AssertId Expression)
    (st : List (Stmt Expression Command))
    (topEnv : IEnv Expression → IEnv Expression)
    (slice : CexA Expression Command → SliceResult)
    (mapCfg : IConfig Expression Command → Option (IConfig Expression Command))
    (htopEnv : ∀ env, EnvWF env → EnvWF (topEnv env))
    (hslice : ∀ start, CexWF start →
      (∀ x ∈ (slice start).slices, CexWF x) ∧ ∀ c f, (slice start).claim = some (c, f) → CexWF c)
    (hmap : ∀ c c', mapCfg c = some c' → CfgWF c → CfgWF c')
    (incoming : BackLinkOutcome Expression Command) (hwf : ∀ x ∈ incoming.chain, CexWF x) :
    ValidOutcome π target st (slicedChainOutcome π target st topEnv slice mapCfg incoming) := by
  unfold slicedChainOutcome
  split
  · exact validOutcome_empty ..
  rename_i inTop rest hchain
  split
  · exact validOutcome_empty ..
  have hwf' : ∀ x ∈ inTop :: rest, CexWF x := hchain ▸ hwf
  have henv : EnvWF (topEnv inTop.cfg.getEnv) :=
    htopEnv _ (CfgWF.getEnv (hwf' inTop (by simp)))
  have hhead := hslice ⟨.stmts st _, inTop.oracle⟩ henv
  refine chainReplayOutcome_valid _ _ _ _ _ _ (by simp [isTopLevelAt]) henv ?_
  split
  · grind [chain]
  exact concatSlicePieces_wf _ (fun d r hd hwd => by
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hd
    exact hslice _ (hmap _ _ hc hwd)) _ rest hhead.1 fun x hx => hwf' x (by simp [hx])

/-- `plainOrSlicedLink`, built for the target `u`, lifts every outcome valid for the target
    `t` at the image `T st` to one valid for `u` at `st`, when its sliced lift returns an
    outcome valid for `u` at the unit from every incoming outcome whose chain elements are
    well-formed, and the two targets agree on every unit `plain` accepts: there the
    unchanged-unit link carries the claim with its target. -/
theorem plainOrSlicedLink_preserves_of (π : String → Option Procedure)
    (t u : AssertId Expression) (name : String)
    (plain : List (Stmt Expression Command) → Bool)
    (sliced : List (Stmt Expression Command) → BackLinkOutcome Expression Command →
      BackLinkOutcome Expression Command)
    (hs : ∀ st o, (∀ x ∈ o.chain, CexWF x) → ValidOutcome π u st (sliced st o))
    (hplain : ∀ st, plain st = true → t = u)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    ∀ st st', T st = some st' → ∀ o, ValidOutcome π t st' o →
      ValidOutcome π u st ((plainOrSlicedLink π name plain sliced).lift st o) :=
  fun st st' hT o ho => by
    simp only [plainOrSlicedLink]
    split
    · rename_i hp
      obtain rfl := hplain st hp
      split
      · exact hs st o ho.2.2
      · exact unchangedExactBackLink_preserves π t T name st st' hT o ho
    · exact hs st o ho.2.2

/-- `plainOrSlicedLink` preserves validity across any forward map `T` (`BackLinkPreserves`)
    when its sliced lift returns an outcome valid at the unit from every incoming outcome
    whose chain elements are well-formed: the unchanged-unit link preserves validity, and the
    sliced lift is valid wherever it is used. -/
theorem plainOrSlicedLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) (name : String)
    (plain : List (Stmt Expression Command) → Bool)
    (sliced : List (Stmt Expression Command) → BackLinkOutcome Expression Command →
      BackLinkOutcome Expression Command)
    (hs : ∀ st o, (∀ x ∈ o.chain, CexWF x) → ValidOutcome π target st (sliced st o))
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (plainOrSlicedLink π name plain sliced) :=
  plainOrSlicedLink_preserves_of π target target name plain sliced hs (fun _ _ => rfl) T

/-- `callElimBackLink` preserves validity across any forward map `T`
    (`BackLinkPreserves`: whenever `T` maps a unit `st` to `st'`, the link lifts every
    outcome valid at `st'` to one valid at `st`). -/
theorem callElimBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) (origins : List CallElim.CallOrigin)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (callElimBackLink π target
        origins) :=
  plainOrSlicedLink_preserves π target _ _ _ (fun st o hwf =>
    slicedChainOutcome_valid π _ st _ _ _ (fun _ => dropFreshEnv_wf _) (callElimSlice_wf π _ _)
      (fun c _ => uncallElimConfig_wf _ c) o hwf) T

/-- `loopElimBackLink` preserves validity across any forward map `T`
    (`BackLinkPreserves`: whenever `T` maps a unit `st` to `st'`, the link lifts every
    outcome valid at `st'` to one valid at `st`). -/
theorem loopElimBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) (origins : LoopOrigins)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreserves π target T (loopElimBackLink π target
        origins) :=
  plainOrSlicedLink_preserves π target _ _ _ (fun st o hwf =>
    slicedChainOutcome_valid π target st id _ _ (fun _ => id) (loopElimSlice_wf π target)
      (fun c _ => unloopElimConfig_wf origins c) o hwf) T

/-- `replayCandidateBase = some (cex, fuel')`: the embedded candidate validates through
    `replayCandidate` at the empty callee table, and the call-aware counterexample it
    returns is the embedding of `cex`, at the same fuel. -/
private theorem replayCandidateBase_embed (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidate : CexCandidateA Expression (Imperative.Cmd Expression)) (fuel : Nat)
    (cex : CexA Expression (Imperative.Cmd Expression)) (fuel' : Nat)
    (h : replayCandidateBase target defaults candidate fuel = some (cex, fuel')) :
    cex.cfg = candidate.cfg ∧
      replayCandidate (fun _ => none) target defaults (Calls.embedCandidate candidate) fuel
        = some (Calls.embedCexA cex, fuel') := by
  simp only [replayCandidateBase, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨cfg, oracle⟩, f⟩, hrc, heq⟩ := h
  have hcfg := replayCandidate_cfg _ _ _ _ _ _ _ hrc
  grind [Calls.embedCandidate, Calls.embedCexA]

/-- `replayCandidateBase = some (cex, fuel')` yields a counterexample whose embedding is
    `genuineFeasible` at `fuel'` at the empty callee table (its replay reaches a failing
    target occurrence along a trace whose assumes hold). -/
private theorem replayCandidateBase_genuineFeasible (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty → Option
        Expression.Expr)
    (candidate : CexCandidateA Expression (Imperative.Cmd Expression)) (fuel : Nat)
    (cex : CexA Expression (Imperative.Cmd Expression)) (fuel' : Nat)
    (h : replayCandidateBase target defaults candidate fuel = some (cex, fuel')) :
    genuineFeasible (fun _ => none) target fuel' (Calls.embedCexA
        cex) :=
  replayCandidate_genuineFeasible _ _ _ _ _ _ _ (replayCandidateBase_embed _ _ _ _ _ _ h).2

/-- `hoistBackLink` preserves validity on embeddings across any forward map `T`
    (`BackLinkPreservesBase`: whenever `T` maps `st` to `st'`, it lifts every outcome whose
    embedding is valid at the embedding of `st'` to one whose embedding is valid at the
    embedding of `st`). -/
theorem hoistBackLink_preserves (target : AssertId Expression)
    (T : List (Stmt Expression (Imperative.Cmd Expression)) → Option (List (Stmt Expression
        (Imperative.Cmd Expression)))) :
    BackLinkPreservesBase target T (hoistBackLink target) := fun st _ _ o ⟨_, _, hwf⟩ => by
  simp only [hoistBackLink]
  split
  · exact validOutcome_empty ..
  split
  · exact validOutcome_empty ..
  have henv := ((cfgWF_embedConfig _).1 (hwf (Calls.embedCexA _) (by
    simp only [embedOutcome_chain, List.mem_map]
    exact ⟨_, BackLinkOutcome.mem_chain_of_head ‹_›, rfl⟩))).getEnv
  have hrb : ∀ defaults cand fuel, (replayCandidateBase target defaults cand fuel).elim True
      fun r => r.1.cfg = cand.cfg ∧ genuineFeasible (fun _ => none) target r.2
        (Calls.embedCexA r.1) := fun defaults cand fuel => by
    cases h : replayCandidateBase target defaults cand fuel
    · trivial
    · exact ⟨(replayCandidateBase_embed _ _ _ _ _ _ h).1,
        replayCandidateBase_genuineFeasible _ _ _ _ _ _ h⟩
  (repeat' split) <;> grind [ValidOutcomeOf, Calls.embedOutcome, BackLinkOutcome.chain, CexWF,
    isTopLevelAt, Calls.embedCexA, Calls.embedIConfig, List.exists_of_findSome?_eq_some,
    replayCandidateLadderBase, CfgWF, EnvWF]

end -- public section

end Core

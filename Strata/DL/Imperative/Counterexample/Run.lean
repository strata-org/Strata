/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.InterpreterTypes
public import Strata.DL.Imperative.InterpreterConfig
public import Strata.Transform.Specification
public import Strata.DL.Imperative.InterpreterCallEmbed

/-! # Level-(a) counterexamples: runs, verdicts and outcome validity

Counterexamples live at three *levels*: level (a) is a run of the program (a `CexA`
replayed from a configuration with an oracle), level (b) is a valuation of a proof
obligation's variables, and level (c) is the SMT solver's model.  This module holds the
level-(a) vocabulary, generic in the pure-expression bundle and command language: a
counterexample at an imperative node is an entry configuration together with only the
nondeterministic choices needed to replay it (`CexA`); the result of lifting a
counterexample to level (a) is a `BackLinkOutcome`, a chain of slices with at most one
genuineness claim.

It also holds the candidate descriptor `CexCandidateA` a back-link may use to search for a
validated counterexample at a chosen start configuration, and the embeddings of a base
candidate and a base outcome into the call-aware command type (`Calls.embedCandidate`,
`Calls.embedOutcome`).

Key definitions: `BackLinkOutcome`, `isTopLevelAt`, `BackLinkOutcome.Fail`,
`BackLinkOutcome.isFail`, `CexValidity`, `ValidOutcomeWF`, `CexCandidateA`.
-/

namespace Imperative

public section

universe u
variable {P : PureExpr.{u}} {CmdT : Type}

/-! ## Counterexample structures

The data of a counterexample and the vocabulary its verdicts use.  Nothing here
executes or validates anything; these are the types the verdicts below and the back-links
(`Counterexample.BackLink`) consume. -/

/-- The result of lifting a counterexample to level (a): the slices of the
    putative counterexample, in execution order, plus at most one genuineness
    claim on the last slice.

    Each element of `chain` is a slice of the obligation-level putative
    counterexample, starting at an intermediate point of the execution (the head,
    if any, starts at the top).  Nothing guarantees reachability between
    consecutive elements: each gap is an open reachability problem (confirmed
    reachability would have merged the two slices).  The only genuineness claim is
    `claim = some (c, f)`: replaying `c` at fuel `f` genuinely and feasibly fails
    the target.  A claim without a counterexample is unrepresentable. -/
structure BackLinkOutcome (P : PureExpr) [InterpLang P] (CmdT : Type) where
  /-- Unconfirmed slices, in execution order; the head (if any) starts at the top. -/
  slices : List (CexA P CmdT)
  /-- The last slice, claimed genuine at the given fuel; `none` = no claim. -/
  claim : Option (CexA P CmdT × Nat)

namespace BackLinkOutcome

/-- The outcome carrying no counterexample data at all. -/
@[expose] def empty {P : PureExpr} [InterpLang P] {CmdT : Type} : BackLinkOutcome P CmdT :=
  ⟨[], none⟩

/-- The whole chain, claim last. -/
@[expose] def chain {P : PureExpr} [InterpLang P] {CmdT : Type} (o : BackLinkOutcome P CmdT) :
    List (CexA P CmdT) :=
  o.slices ++ o.claim.toList.map (·.1)

end BackLinkOutcome

/-! ## Counterexample validation and verdicts

Deciding whether a counterexample is genuine by replaying it against the imperative
semantics.  Replay runs on the engine runner `Imperative.runReplay`
(`InterpreterReplay.lean`), whose genuineness is *target-keyed and trace-based*: a verdict is
`.genuine` exactly when some emitted event fires the target `haltOn` predicate
(`runReplay_genuine_iff`).  The call-aware wrappers `Calls.replayWith` / `Calls.genuine` /
`Calls.genuineFeasible` (`InterpreterCall.lean`) run it on the call-aware monadic interpreter;
Core's `replayWithM` / `genuine` / `genuineFeasible` coincide with them
(`InterpreterCallBridge.lean`), and Core's `genuineFeasible` is the claim validity of Core's
back-link validity specification (`ValidOutcome`, `Strata.Languages.Core.Counterexample.Run`).
This is the (a)-level analogue of evaluating a model against a proof obligation at (b); it is
independent of any program transformation.  This section defines the verdicts reported on a
back-link outcome. -/

/-- `cex` starts at the top of `stmts`: its configuration is `.stmts stmts _`. -/
@[expose] def isTopLevelAt {P : PureExpr} [InterpLang P] {CmdT : Type}
    (stmts : List (Stmt P CmdT)) (cex : CexA P CmdT) : Prop :=
  match cex.cfg with
  | .stmts s _ => s = stmts
  | _ => False

/-- The user-facing `Fail` verdict of a back-link outcome at `stmts`: the outcome
    claims a slice that starts at the top of `stmts`.  Every other outcome is
    reported as `Unknown`. -/
@[expose] def BackLinkOutcome.Fail {P : PureExpr} [InterpLang P] {CmdT : Type}
    (stmts : List (Stmt P CmdT)) (o : BackLinkOutcome P CmdT) : Prop :=
  ∃ c f, o.claim = some (c, f) ∧ isTopLevelAt stmts c

/-- The executable form of the `Fail` verdict used at runtime: no unconfirmed
    slices and a claim present.  On a valid outcome it coincides with
    `BackLinkOutcome.Fail`. -/
@[expose] def BackLinkOutcome.isFail {P : PureExpr} [InterpLang P] {CmdT : Type}
    (o : BackLinkOutcome P CmdT) : Bool :=
  o.slices.isEmpty && o.claim.isSome

/-! ## Outcome validity

The validity of a back-link outcome, generic over the claim-validity predicate of the
target and the well-formedness of a slice start. -/

/-- A claim-validity predicate: the target, the claim's fuel, and the claimed slice. -/
abbrev CexValidity (P : PureExpr) [InterpLang P] (CmdT : Type) (Tgt : Type) :=
  Tgt → Nat → CexA P CmdT → Prop

/-- Validity of a back-link outcome for the target `t` at the unit `stmts`: the head starts
    at the top of `stmts`, a claim is valid for `t` (`V`) and, behind unconfirmed slices,
    does not start at the top, and every slice start is well-formed (`WF`). -/
@[expose] def ValidOutcomeWF [InterpLang P] (WF : IConfig P CmdT → Prop) {Tgt : Type}
    (V : CexValidity P CmdT Tgt) (t : Tgt) (stmts : List (Stmt P CmdT))
    (o : BackLinkOutcome P CmdT) : Prop :=
  (∀ h, o.chain.head? = some h → isTopLevelAt stmts h) ∧
  (∀ c f, o.claim = some (c, f) → V t f c ∧ (o.slices ≠ [] → ¬ isTopLevelAt stmts c)) ∧
  (∀ c ∈ o.chain, WF c.cfg)

end -- public section

public section


/-- Candidate descriptor for a source search: a proposed start configuration with a
    partial oracle seed (the `CexA` fields `cfg` and `oracle`, the oracle empty by default),
    and two source relations.  `sourceRelation` checks the proposed start configuration;
    `failureSourceRelation` checks the configuration whose next replay step produced the
    failure. -/
structure CexCandidateA (P : PureExpr) [InterpLang P] (CmdT : Type) extends CexA P CmdT where
  oracle := []
  sourceRelation : IConfig P CmdT → Bool := fun _ => true
  failureSourceRelation : IConfig P CmdT → Bool := fun _ => true

/-! Embedding a base counterexample candidate / back-link outcome into the
    call-aware command type.  They mention CEL types (`CexCandidateA`,
    `BackLinkOutcome`), so they live here rather than in the engine module. -/
namespace Calls

variable {P : PureExpr} [InterpLang P]

/-- A base counterexample candidate as a call-aware one (same oracle seed);
    the source relations are evaluated at the base configuration. -/
@[expose] def embedCandidate (c : CexCandidateA P (Cmd P)) : CexCandidateA P (CmdExt P) :=
  { cfg := embedIConfig c.cfg, oracle := c.oracle,
    sourceRelation := fun _ => c.sourceRelation c.cfg,
    failureSourceRelation := fun _ => c.failureSourceRelation c.cfg }

/-- A base back-link outcome as a call-aware one. -/
@[expose] def embedOutcome (o : BackLinkOutcome P (Cmd P)) : BackLinkOutcome P (CmdExt P) :=
  { slices := o.slices.map embedCexA, claim := o.claim.map fun (c, f) => (embedCexA c, f) }

end Calls

end -- public section

end Imperative

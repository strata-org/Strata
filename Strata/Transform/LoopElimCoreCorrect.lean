/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SpecificationProps
public import Strata.Transform.SpecHoareConnection
public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.LangDef
public import Strata.DL.Imperative.Logic.HoareTemplate
import Strata.Transform.LoopElimProps
public import Strata.Transform.LoopElimCoreProps

/-! # Core loop-elimination correctness

Over Core's event language for statement lists (`EventLang.coreBlock`), eliminating the loops of
a call-free list (`Block.loopElim`, which replaces each loop by its passive encoding) is a trace
over-approximation (`Core.LoopElim.overapproximatesTraces`), with one relation for finite
prefixes and one for completed runs.  From every entry environment satisfying the gate
`BlockInitEnvWF` at parameters reserving the label prefix of the blocks the encoding mints
(`Core.loopElimPrefix`), so that no `exit` of the source targets one of them:
* every finite trace of the source has a target trace ending with its last event
  (`Trace.PreservesLastEvent`), the events before it related to those before it in the source
  by dropping events (`Trace.MayDropEvents`) and then inserting assumptions that evaluate to
  `true` (`Trace.InsertsTrueAssumes`), followed by extra events that are such assumptions
  (`Trace.HasExtraEvents`);
* every terminating and every exiting run of the source has a target run ending the same way in
  the same environment, whose trace is related to the source's by dropping events and then
  inserting assumptions that evaluate to `true`;
* the output satisfies the gate `BlockInitEnvWF` at the parameters without that reservation.

The target replays one iteration of each loop, so its traces drop the events of the others,
including their assertions.  A prefix ending at an event can replay the iteration that event is
in, so the prefix relation keeps it; a run must end the way the source's does, which can force
the replay of another iteration, so the run relation keeps no particular event.  Assertion
validity (`Core.LoopElim.assertValid`) follows from the prefix clause; it needs an
interpretation under which every condition that evaluates to `true` holds
(`ConditionInterp.TrueStutterHolds`), as evaluation to `true` does
(`Core.LoopElim.evalInterp_trueStutterHolds`).

A Hoare triple also asks for assertion validity on completed runs, which the run relation does
not carry.  When no loop iteration leaves its loop by an `exit` (`Block.loopExitsLocal`), every
event of a source run is kept by some target run ending the same way (`LoopElim.run_sim_at`), so
every source run from an entry over a Lambda factory `F` has a target run ending the same way
whose assertions are valid under `DenoteBasedInterp F` only if the source's are
(`Core.LoopElim.overapproximatesTraces_whenLoopExitsLocal`), and a Core triple on the output
gives the triple on the input (`Core.LoopElim.triple`, by
`overapproximatesTraces2UptoWhen_triple_general`).

In a verification pipeline, the prefix relation keeps the last assertion of a prefix
(`Trace.ReflectsLastAssertion`), not every assertion of a trace, so the pipeline lemmas whose
hypothesis is a relation reflecting whole-trace validity
(`Analysis.ValidOnTracesVerifier.runTransforms_of_overapproximatesTracesUpto`) do not apply as
stated.  A verifier run after the phase is still sound on its input: each source assertion is
reflected through the prefix ending at it (`Core.LoopElim.validOnTracesVerifier_coreProgram`).

The Core pass `Core.loopElim` that the verifier runs builds the same encoding up to loop numbers,
which the two passes draw in different orders.  When it succeeds, the results hold for each
procedure body and the body the pass returns in its place, from every entry environment
satisfying the gate with no prefix reserved, since the pass itself rejects a loop body exiting
to a label starting with `Core.loopElimPrefix` (`Core.LoopElim.overapproximatesTraces_coreProgram`,
`Core.LoopElim.assertValid_coreProgram`, `Core.LoopElim.triple_coreProgram`,
`Core.LoopElim.validOnTracesVerifier_coreProgram`).  Both kinds of results
are instances of the lemmas of `LoopElimCoreProps`, stated for every transformation whose outputs
are images of its inputs under `BlockRel`.

A havoc can only choose a value of the type of the value the variable holds; the gate's
value-valued store (`WellFormedStore`) holds typed values (`LawfulHasVal.value_typed`), so the
havocs of the target can reach every store of the source.

Key theorems: `Core.LoopElim.overapproximatesTraces`, `Core.LoopElim.assertValid`,
`Core.LoopElim.overapproximatesTraces_whenLoopExitsLocal`, `Core.LoopElim.triple`,
`Core.LoopElim.evalInterp_trueStutterHolds`, and for the Core pass
`Core.LoopElim.overapproximatesTraces_coreProgram`, `Core.LoopElim.assertValid_coreProgram`,
`Core.LoopElim.triple_coreProgram` and `Core.LoopElim.validOnTracesVerifier_coreProgram`. -/

namespace Core.LoopElim

open Core Core.Logic Imperative Imperative.BigStep Imperative.LoopElim
  Imperative.Specification Imperative.Specification.Transform Strata.Logic

public section

variable (π : String → Option Procedure)

/-! ## The `Imperative.Block.loopElim` pass -/

/-- **Loop elimination over-approximates the traces of a Core statement list.**  For a call-free
    Core statement list `ss` (`Statements.noCalls`) whose loops `Block.loopElim` eliminates, and
    every entry environment `ρ₀` satisfying `BlockInitEnvWF` of `ss` at `params` with
    `Core.loopElimPrefix` reserved for block labels (no `exit` of `ss` targets a label starting
    with it):
    * every finite trace of `ss` from `ρ₀` has a trace of the output from `ρ₀` ending with its
      last event (`Trace.PreservesLastEvent`) after events related to those before it by
      dropping events (`Trace.MayDropEvents`) and inserting true assumptions
      (`Trace.InsertsTrueAssumes`, the assumptions captured under a factory satisfying
      `WellFormedSemanticEval`), followed by true assumptions (`Trace.HasExtraEvents`);
    * every terminating or exiting run of `ss` from `ρ₀` has a run of the output from `ρ₀`
      ending in the same environment, in the same way, with a trace related to the source's by
      dropping events and inserting true assumptions;
    * the output satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem overapproximatesTraces (params : InitEnvWFParams) :
    OverapproximatesTraces2UptoWhen
      (Trace.HasExtraEvents
        (Trace.PreservesLastEvent (RComp Trace.MayDropEvents
          (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression)))))
        (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression)) []))
      (RComp Trace.MayDropEvents
        (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression))))
      -- Both executions start from the same environment.
      (· = ·)
      -- Completed runs end in the same environment.
      (· = ·)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => Imperative.Block.loopElim ss)
      -- The bridge to the big-step semantics requires a call-free source.
      (fun ss => Statements.noCalls ss = Bool.true)
      (params.extendBlockLabels [loopElimPrefix]) params :=
  overapproximatesTraces_of_blockRel π params [loopElimPrefix]
    fun _ _ _ ht hwf => blockRel_of_loopElim ht hwf

/-- **Assertion validity transported back through loop elimination.**  For an interpretation `I`
    under which every condition that evaluates to `true` under a factory satisfying
    `WellFormedSemanticEval` holds (such as evaluation to `true`, by
    `evalInterp_trueStutterHolds`), and a call-free Core statement list `ss` whose loops
    `Block.loopElim` eliminates into `ss'`: if every occurrence of the assertion `aid` holds
    under its preceding assumptions on every trace of `ss'` from every environment satisfying
    `BlockInitEnvWF params ss'`, the same holds for `ss` from every environment satisfying
    `BlockInitEnvWF` of `ss` at `params` with `Core.loopElimPrefix` reserved for block
    labels. -/
theorem assertValid (params : InitEnvWFParams) {ss ss' : Statements}
    (ht : Imperative.Block.loopElim ss = some ss') (hnc : Statements.noCalls ss = Bool.true)
    {I : ConditionInterp Expression}
    (htrue : I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)))
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF params ss') ss' aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF (params.extendBlockLabels [loopElimPrefix]) ss) ss aid :=
  assertValid_of_blockRel π params [loopElimPrefix] (fun _ => blockRel_of_loopElim ht) hnc
    htrue hvalid

/-- Evaluation to `true` holds for every condition that evaluates to `true`. -/
theorem evalInterp_trueStutterHolds (allowed : Expression.Factory → Prop) :
    (evalInterp : ConditionInterp Expression).TrueStutterHolds allowed :=
  fun _ _ h _ => h

/-- **Loop elimination over-approximates the traces of a Core statement list whose loop
    iterations never leave their loop by an `exit`**, its completed runs reflecting assertion
    validity under `DenoteBasedInterp F`.  For a call-free Core statement list `ss` whose loop
    iterations never leave their loop by an `exit` (`Block.loopExitsLocal`) and whose loops
    `Block.loopElim` eliminates, and every entry environment `ρ₀` over `F`
    (`ρ₀.factory.factory = F`) satisfying `BlockInitEnvWF` of `ss` at `params` with
    `Core.loopElimPrefix` reserved for block labels: as `overapproximatesTraces`, with every
    terminating or exiting run of `ss` from `ρ₀` matched by a run of the output whose trace,
    besides being related to the source's by dropping events and inserting true assumptions,
    has valid assertions only if the source's has (`Trace.ImpliesAssertValidity`) and is
    reachable if the source's is (`Trace.ImpliesReachability`), under `DenoteBasedInterp F`. -/
theorem overapproximatesTraces_whenLoopExitsLocal (params : InitEnvWFParams)
    (F : Lambda.Factory CoreLParams) :
    OverapproximatesTraces2UptoWhen
      (Trace.HasExtraEvents
        (Trace.PreservesLastEvent (RComp Trace.MayDropEvents
          (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression)))))
        (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression)) []))
      (fun trace trace' =>
        RComp Trace.MayDropEvents
          (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression))) trace trace' ∧
        Trace.ImpliesAssertValidity (DenoteBasedInterp F) trace trace' ∧
        Trace.ImpliesReachability (DenoteBasedInterp F) trace trace')
      -- Both executions start from the same environment, over `F`.
      (fun (ρ₀ ρ₀' : Env Expression) => ρ₀ = ρ₀' ∧ ρ₀.factory.factory = F)
      -- Completed runs end in the same environment.
      (· = ·)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => Imperative.Block.loopElim ss)
      -- The bridge to the big-step semantics requires a call-free source; no loop iteration
      -- leaves its loop by an `exit`.
      (fun ss => Statements.noCalls ss = Bool.true ∧ Block.loopExitsLocal ss)
      (params.extendBlockLabels [loopElimPrefix]) params :=
  overapproximatesTraces_whenLoopExitsLocal_of_blockRel π params [loopElimPrefix]
    (fun _ _ _ ht hwf => blockRel_of_loopElim ht hwf) F

/-- **A Hoare triple transported back through loop elimination.**  For a call-free Core
    statement list `ss` whose loop iterations never leave their loop by an `exit`
    (`Block.loopExitsLocal`) and whose loops `Block.loopElim` eliminates into `ss'`, and a
    precondition admitting only entry environments over `F`: a Core triple `{Pre} ss' {Post}`
    over `F` (`Core.Logic.Hoare.Triple`, read by `DenoteBasedInterp F`) at `params` gives the
    triple `{Pre} ss {Post}` at `params` with `Core.loopElimPrefix` reserved for block labels.

    Why `Block.loopExitsLocal` is needed: in
    ```
    block L { i := 0; while (true) { if (i == 0) { assert A: false; i := 1 } else { exit L } };
      i := 2 }
    ```
    the source ends with `i = 1` after failing `A`: the first iteration asserts `A`, and the
    second runs `exit L`, which skips `i := 2`.  The output replaces the loop by one iteration
    from a havocked `i`; its runs not running `exit L` run `i := 2` and end with `i = 2`, and
    those running it replay only that iteration, with trace `[assume true]`.  No run of the
    output ending the way the source's does fails `A`, so its triple does not determine the
    source's. -/
theorem triple (params : InitEnvWFParams) {ss ss' : Statements}
    (ht : Imperative.Block.loopElim ss = some ss') (hnc : Statements.noCalls ss = Bool.true)
    (hloc : Block.loopExitsLocal ss)
    {F : Lambda.Factory CoreLParams} {Pre Post : Env Expression → Prop}
    (hpin : ∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F)
    (h : Core.Logic.Hoare.Triple π params Pre ss' Post F) :
    Core.Logic.Hoare.Triple π (params.extendBlockLabels [loopElimPrefix]) Pre ss Post F :=
  triple_of_blockRel π params [loopElimPrefix] (fun _ => blockRel_of_loopElim ht) hnc hloc
    hpin h

/-! ## The Core pass, `Core.loopElim`

When `Core.loopElim p` succeeds with `p'`, each procedure of `p` with a structured body `ss` has,
at its position in `p'`, a body `ss'`, and the results above hold for `ss` and `ss'` from every
entry satisfying the gate at `params`, with no label prefix reserved: the pass rejects a loop
body exiting to a label starting with `Core.loopElimPrefix`. -/

/-- **The Core pass over-approximates the traces of each procedure body.**  When
    `Core.loopElim p` succeeds with `p'`, a procedure of `p` with a structured body `ss` has, at
    its position in `p'`, a body `ss'` such that sending `ss` to `ss'` over-approximates traces
    as in `overapproximatesTraces`, from every entry environment satisfying `BlockInitEnvWF` at
    `params`. -/
theorem overapproximatesTraces_coreProgram (params : InitEnvWFParams) {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (h : loopElim p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      OverapproximatesTraces2UptoWhen
        (Trace.HasExtraEvents
          (Trace.PreservesLastEvent (RComp Trace.MayDropEvents
            (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression)))))
          (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression)) []))
        (RComp Trace.MayDropEvents
          (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression))))
        -- Both executions start from the same environment.
        (· = ·)
        -- Completed runs end in the same environment.
        (· = ·)
        (EventLang.coreBlock π) (EventLang.coreBlock π)
        (fun (s : Statements) => if s = ss then some ss' else none)
        (fun s => Statements.noCalls s = Bool.true) params params :=
  have ⟨ss', hd, hrel⟩ := loopElim_body_blockRel h hproc hbody
  ⟨ss', hd, overapproximatesTraces_of_blockRel π params [] (single_blockRel fun _ _ => hrel)⟩

/-- **The Core pass transports assertion validity back to each procedure body.**  When
    `Core.loopElim p` succeeds with `p'`, a call-free structured body `ss` of a procedure of `p`
    has, at its position in `p'`, a body `ss'` such that, for an interpretation `I` as in
    `assertValid`, validity of the assertion `aid` on `ss'` from every environment satisfying
    `BlockInitEnvWF params ss'` gives its validity on `ss` from every environment satisfying
    `BlockInitEnvWF params ss`. -/
theorem assertValid_coreProgram (params : InitEnvWFParams) {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (h : loopElim p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss)
    (hnc : Statements.noCalls ss = Bool.true) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      ∀ {I : ConditionInterp Expression},
        I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)) →
      ∀ {aid : AssertId Expression},
        AssertValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF params ss') ss' aid →
        AssertValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF params ss) ss aid :=
  have ⟨ss', hd, hrel⟩ := loopElim_body_blockRel h hproc hbody
  ⟨ss', hd, fun {_} htrue {_} hvalid =>
    assertValid_of_blockRel π params [] (fun _ _ => hrel) hnc htrue hvalid⟩

/-- **The Core pass transports Hoare triples back to each procedure body.**  When
    `Core.loopElim p` succeeds with `p'`, a call-free structured body `ss` of a procedure of `p`
    whose loop iterations never leave their loop by an `exit` (`Block.loopExitsLocal`) has, at
    its position in `p'`, a body `ss'` such that, for a precondition admitting only entry
    environments over `F`, a Core triple `{Pre} ss' {Post}` over `F` at `params` gives the
    triple `{Pre} ss {Post}` at `params`.  `triple` shows why loops left by an `exit` are
    excluded. -/
theorem triple_coreProgram (params : InitEnvWFParams) {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (h : loopElim p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss)
    (hnc : Statements.noCalls ss = Bool.true) (hloc : Block.loopExitsLocal ss) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      ∀ {F : Lambda.Factory CoreLParams} {Pre Post : Env Expression → Prop},
        (∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F) →
        Core.Logic.Hoare.Triple π params Pre ss' Post F →
        Core.Logic.Hoare.Triple π params Pre ss Post F :=
  have ⟨ss', hd, hrel⟩ := loopElim_body_blockRel h hproc hbody
  ⟨ss', hd, fun hpin h => triple_of_blockRel π params [] (fun _ _ => hrel) hnc hloc hpin h⟩

/-- **A verifier run after the Core pass is sound on each procedure body.**  When
    `Core.loopElim p` succeeds with `p'`, a call-free structured body `ss` of a procedure of `p`
    has, at its position in `p'`, a body `ss'` such that, for an interpretation `I` as in
    `assertValid` and a verifier `analyze` that passes only lists whose traces from entries
    satisfying `BlockInitEnvWF params` have every assertion valid under `I`: if `analyze` passes
    `ss'`, every assertion of every trace of `ss` from an entry satisfying `BlockInitEnvWF params`
    is valid under `I`. -/
theorem validOnTracesVerifier_coreProgram (params : InitEnvWFParams) {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (h : loopElim p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss)
    (hnc : Statements.noCalls ss = Bool.true) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      ∀ {I : ConditionInterp Expression},
        I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)) →
      ∀ {analyze : Statements → Bool},
        Analysis.ValidOnTracesVerifier (EventLang.coreBlock π) I (BlockInitEnvWF params)
          analyze →
        analyze ss' = Bool.true →
        AllAssertsValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF params ss) ss :=
  have ⟨ss', hd, hrel⟩ := loopElim_body_blockRel h hproc hbody
  ⟨ss', hd, fun {_} htrue {_} hsound hpass ρ₀ cfg trace hwf htrace =>
    validOnTracesVerifier_of_blockRel π params [] (single_blockRel fun _ _ => hrel) htrue hsound
      ss (by simpa [Analysis.thenVerify] using hpass) ρ₀ cfg trace ⟨hnc, hwf⟩ htrace⟩

end -- public section

end Core.LoopElim

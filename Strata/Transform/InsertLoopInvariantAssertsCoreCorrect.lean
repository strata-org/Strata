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
public import Strata.Transform.InsertLoopInvariantAssertsCoreProps
import Strata.Transform.InsertLoopInvariantAssertsProps

/-! # Core correctness of inserting loop invariant checks

Over Core's event language for statement lists (`EventLang.coreBlock`), the pass
`Core.insertLoopInvariantAsserts` that the verifier runs inserts the checks of the invariants
and measures of the loops of each procedure body.  When it succeeds from a well-formed generator
state, each call-free structured procedure body `ss` has, at its position in the output, a body
`ss'` such that sending `ss` to `ss'` is a trace over-approximation
(`Core.InsertLoopInvAsserts.overapproximatesTraces_coreProgram`).  From every entry environment
satisfying the gate `BlockInitEnvWF` at parameters reserving the prefix of the measure snapshot
variables (`InsertLoopInvAsserts.prefixesReserved`), every finite trace and every terminating or
exiting run of `ss` has a trace or run of `ss'`, ending the same way in the same environment for
a run, whose trace is the source's with each condition captured in a store extended with measure
snapshots and with assertions inserted (`Trace.InsertsAsserts`), and then assumptions that
evaluate to `true` or copy the condition, with the same value, of an earlier inserted assertion
of an invariant (`Trace.InsertsCheckedAssumes`, with the inserted invariant assertions
`InsertLoopInvAsserts.InvCheck`).  `ss'` satisfies the gate at the parameters without that
reservation, when none of their prefixes is a prefix of the snapshot names' prefix
(`InsertLoopInvAsserts.measurePrefix`) or starts with it.

The gate's `measuresTyped` gives each measure the integer type under its annotations, which,
with `fvarTypesOk`, makes it evaluate to an integer where its loop is entered: the measure
snapshot `init` of the output never blocks.

An inserted assumption of an invariant holds only where the assertion before it does, so
assertion validity transported back to the source
(`Core.InsertLoopInvAsserts.assertValid_coreProgram`) asks for the validity of the inserted
invariant assertions as well, under an interpretation for which conditions with the same value
hold alike and true conditions hold, as evaluation to `true`
(`Core.InsertLoopInvAsserts.evalInterp_stableUnder`,
`Core.LoopElim.evalInterp_trueStutterHolds`).  A Core triple on `ss'` gives the triple on `ss`
(`Core.InsertLoopInvAsserts.triple_coreProgram`), and a verifier sound on event traces that
passes `ss'` makes every assertion of `ss` valid
(`Core.InsertLoopInvAsserts.validOnTracesVerifier_coreProgram`): both make every assertion of
`ss'` valid, those of the invariants included.  The results are instances of the lemmas of
`InsertLoopInvariantAssertsCoreProps`, stated for every transformation whose outputs are images
of its inputs under `BlockRel []`.

Key theorems: `Core.InsertLoopInvAsserts.overapproximatesTraces_coreProgram`,
`Core.InsertLoopInvAsserts.assertValid_coreProgram`,
`Core.InsertLoopInvAsserts.triple_coreProgram`,
`Core.InsertLoopInvAsserts.validOnTracesVerifier_coreProgram`,
`Core.InsertLoopInvAsserts.evalInterp_stableUnder`. -/

namespace Core.InsertLoopInvAsserts

open Core Core.Logic Imperative Imperative.BigStep Imperative.InsertLoopInvAsserts
  Imperative.Specification Imperative.Specification.Transform Strata.Logic

public section

variable (π : String → Option Procedure)

/-- Evaluation to `true` gives the same truth value to conditions with the same value. -/
theorem evalInterp_stableUnder (allowed : Expression.Factory → Prop) :
    (evalInterp : ConditionInterp Expression).StableUnder (EventArg.SameValue allowed) := by
  intro _ a b ⟨_, hf, _, hv⟩
  change Expression.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) ↔
    Expression.eval b.factory b.store b.expr = some (HasBool.ttVal b.factory)
  rw [hv, hf]

/-- **The Core pass over-approximates the traces of each procedure body.** When
    `Core.insertLoopInvariantAsserts p` succeeds with `p'` from a state whose generator state is
    well formed, a procedure of `p` with a structured body `ss` has, at its position in `p'`, a body
    `ss'` such that sending `ss` to `ss'` over-approximates traces as in
    `overapproximatesTraces_of_blockRel`, from every entry environment satisfying `BlockInitEnvWF`
    at `base` with `prefixesReserved` reserved. -/
theorem overapproximatesTraces_coreProgram (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (hgen : σ.genState.WF)
    (h : insertLoopInvariantAsserts p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      OverapproximatesTracesUptoWhen
        (RComp (Trace.InsertsAsserts (WellFormedSemanticEval (P := Expression)))
          (Trace.InsertsCheckedAssumes (WellFormedSemanticEval (P := Expression)) InvCheck []))
        -- Both executions start from the same environment.
        (· = ·)
        -- Completed runs end in the same environment.
        (· = ·)
        (EventLang.coreBlock π) (EventLang.coreBlock π)
        (fun (s : Statements) => if s = ss then some ss' else none)
        (fun s => Statements.noCalls s = Bool.true) (base.extend prefixesReserved) base :=
  have ⟨ss', hd, hrel⟩ := insertLoopInvariantAsserts_body_blockRel hgen h hproc hbody
  ⟨ss', hd, overapproximatesTraces_of_blockRel π base hprefixes (single_blockRel hrel)⟩

/-- **The Core pass transports assertion validity back to each procedure body.**  When
    `Core.insertLoopInvariantAsserts p` succeeds with `p'` from a state whose generator state is
    well formed, a call-free structured body `ss` of a procedure of `p` has, at its position in
    `p'`, a body `ss'` such that, for an interpretation `I` under which conditions with the same
    value hold alike and every condition that evaluates to `true` holds, under factories
    satisfying `WellFormedSemanticEval`, the validity on `ss'` of its inserted invariant
    assertions and of the assertion `aid`, from every environment satisfying
    `BlockInitEnvWF base ss'`, gives the validity of `aid` on `ss` from every environment
    satisfying `BlockInitEnvWF` of `ss` at `base` with `prefixesReserved` reserved. -/
theorem assertValid_coreProgram (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (hgen : σ.genState.WF)
    (h : insertLoopInvariantAsserts p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss)
    (hnc : Statements.noCalls ss = Bool.true) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      ∀ {I : ConditionInterp Expression},
        I.StableUnder (EventArg.SameValue (WellFormedSemanticEval (P := Expression))) →
        I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)) →
        (∀ ρ₀ cfg trace, BlockInitEnvWF base ss' ρ₀ →
          (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss' ρ₀) trace cfg →
          Trace.AssertionsValidFromP Expression I InvCheck [] trace) →
      ∀ {aid : AssertId Expression},
        AssertValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF base ss') ss' aid →
        AssertValidOnTracesWhen (EventLang.coreBlock π) I
          (BlockInitEnvWF (base.extend prefixesReserved) ss) ss aid :=
  have ⟨ss', hd, hrel⟩ := insertLoopInvariantAsserts_body_blockRel hgen h hproc hbody
  ⟨ss', hd, fun {_} hstable htrue hchecks {_} hvalid =>
    assertValid_of_blockRel π base hprefixes hrel hnc hstable htrue hchecks hvalid⟩

/-- **The Core pass transports Hoare triples back to each procedure body.**  When
    `Core.insertLoopInvariantAsserts p` succeeds with `p'` from a state whose generator state is
    well formed, a call-free structured body `ss` of a procedure of `p` has, at its position in
    `p'`, a body `ss'` such that, for a precondition admitting only entry environments over `F`,
    a Core triple `{Pre} ss' {Post}` over `F` at `base` gives the triple `{Pre} ss {Post}` at
    `base` with `prefixesReserved` reserved. -/
theorem triple_coreProgram (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (hgen : σ.genState.WF)
    (h : insertLoopInvariantAsserts p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss)
    (hnc : Statements.noCalls ss = Bool.true) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      ∀ {F : Lambda.Factory CoreLParams} {Pre Post : Env Expression → Prop},
        (∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F) →
        Core.Logic.Hoare.Triple π base Pre ss' Post F →
        Core.Logic.Hoare.Triple π (base.extend prefixesReserved) Pre ss Post F :=
  have ⟨ss', hd, hrel⟩ := insertLoopInvariantAsserts_body_blockRel hgen h hproc hbody
  ⟨ss', hd, fun hpin h => triple_of_blockRel π base hprefixes hrel hnc hpin h⟩

/-- **A verifier run after the Core pass is sound on each procedure body.**  When
    `Core.insertLoopInvariantAsserts p` succeeds with `p'` from a state whose generator state is
    well formed, a call-free structured body `ss` of a procedure of `p` has, at its position in
    `p'`, a body `ss'` such that, for an interpretation `I` under which conditions with the same
    value hold alike and every condition that evaluates to `true` holds, under factories
    satisfying `WellFormedSemanticEval`, and a verifier `analyze` that passes only lists whose
    traces from entries satisfying `BlockInitEnvWF base` have every assertion valid under `I`:
    if `analyze` passes `ss'`, every assertion of every
    trace of `ss` from an entry satisfying `BlockInitEnvWF` at `base` with `prefixesReserved`
    reserved is valid under `I`. -/
theorem validOnTracesVerifier_coreProgram (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (hgen : σ.genState.WF)
    (h : insertLoopInvariantAsserts p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss)
    (hnc : Statements.noCalls ss = Bool.true) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      ∀ {I : ConditionInterp Expression},
        I.StableUnder (EventArg.SameValue (WellFormedSemanticEval (P := Expression))) →
        I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)) →
      ∀ {analyze : Statements → Bool},
        Analysis.ValidOnTracesVerifier (EventLang.coreBlock π) I (BlockInitEnvWF base)
          analyze →
        analyze ss' = Bool.true →
        AllAssertsValidOnTracesWhen (EventLang.coreBlock π) I
          (BlockInitEnvWF (base.extend prefixesReserved) ss) ss :=
  have ⟨ss', hd, hrel⟩ := insertLoopInvariantAsserts_body_blockRel hgen h hproc hbody
  ⟨ss', hd, fun {_} hstable htrue {_} hsound hpass ρ₀ cfg trace hwf htrace =>
    validOnTracesVerifier_of_blockRel π base hprefixes (single_blockRel hrel) hstable htrue
      hsound ss (by simpa [Analysis.thenVerify] using hpass) ρ₀ cfg trace ⟨hnc, hwf⟩ htrace⟩

end -- public section

end Core.InsertLoopInvAsserts

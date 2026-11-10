/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.InsertLoopInvariantAssertsCorrect
public import Strata.Transform.InsertLoopInvariantAssertsProps
public import Strata.Transform.SpecificationProps
public import Strata.Transform.SpecHoareConnection
public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.DL.Imperative.Logic.HoareTemplate
import Strata.Transform.DeadDefElimProps
import Strata.Languages.Core.Logic.LangDefProps
import Strata.DL.Imperative.BigStep.Adequacy
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.DL.Imperative.Logic.TraceInterpProps

/-! # Core insertion of loop invariant checks over `BlockRel` images

The Core-level trace results of `InsertLoopInvariantAssertsCoreCorrect`, stated for every
transformation `T` whose outputs are `BlockRel []` images of its inputs: each body the pass
`Core.insertLoopInvariantAsserts` returns gives one
(`Core.InsertLoopInvAsserts.insertLoopInvariantAsserts_body_blockRel`).  The proofs bridge the
call-free Core event semantics to the big-step semantics and use the simulations of
`InsertLoopInvariantAssertsCorrect`.  They are Core-level, so they are not in
`InsertLoopInvariantAssertsCorrect`, which is Imperative-level, nor in
`InsertLoopInvariantAssertsProps`, which `InsertLoopInvariantAssertsCorrect` imports.

From every entry satisfying the gate `BlockInitEnvWF` with the prefix of the measure snapshot
variables reserved, the source's traces relate to the output's by inserting assertions
(`Trace.InsertsAsserts`) and then assumptions that evaluate to `true` or copy an earlier inserted
assertion of an invariant (`Trace.InsertsCheckedAssumes`).  The gate's `measuresTyped` gives
each measure the integer type under its annotations, which, with `fvarTypesOk`, makes it
evaluate to an integer where its loop is entered: the measure snapshot `init` of the output never
blocks.  An inserted assumption of an invariant holds only where the assertion before it does,
so transporting the validity of one assertion asks for that of the inserted invariant assertions
as well, and a Hoare triple or a verifier, which make every assertion of the output valid,
transport without more.

Key theorems: `Core.InsertLoopInvAsserts.overapproximatesTraces_of_blockRel`,
`Core.InsertLoopInvAsserts.overapproximatesTraces_over_of_blockRel`,
`Core.InsertLoopInvAsserts.assertValid_of_blockRel`,
`Core.InsertLoopInvAsserts.triple_of_blockRel`,
`Core.InsertLoopInvAsserts.validOnTracesVerifier_of_blockRel`,
`Core.InsertLoopInvAsserts.single_blockRel`. -/

namespace Core.InsertLoopInvAsserts

open Core Core.Logic Imperative Imperative.BigStep Imperative.InsertLoopInvAsserts
  Core.DeadDefElim Imperative.Specification Imperative.Specification.Transform Strata.Logic

public section

variable (π : String → Option Procedure)

/-- The facts the simulation needs, from an entry satisfying the gate with `prefixesReserved`
    reserved: completed runs of `ss` are replayed by `ss'` with traces related by inserting
    assertions and then checked assumptions, under the entry's factory. -/
private theorem runs_of_gate {base : InitEnvWFParams} {ss ss' : Statements}
    (hrel : BlockRel [] ss ss') (hnc : Statements.noCalls ss = Bool.true) {ρ₀ : Env Expression}
    (hwf : BlockInitEnvWF (base.extend prefixesReserved) ss ρ₀)
    {R : Trace Expression → Trace Expression → Prop}
    (hmono : ∀ {t t' : Trace Expression}, RComp (Trace.InsertsAsserts (· = ρ₀.factory))
      (Trace.InsertsCheckedAssumes (· = ρ₀.factory) InvCheck []) t t' → R t t') :
    (∀ ρ' trace, (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss ρ₀) trace
        ((EventLang.coreBlock π).terminalCfg ρ') →
      ∃ ρ'' trace', (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss' ρ₀)
        trace' ((EventLang.coreBlock π).terminalCfg ρ'') ∧ ρ' = ρ'' ∧ R trace trace') ∧
    (∀ l ρ' trace, (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss ρ₀)
        trace ((EventLang.coreBlock π).exitingCfg l ρ') →
      ∃ ρ'' trace', (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss' ρ₀)
        trace' ((EventLang.coreBlock π).exitingCfg l ρ'') ∧ ρ' = ρ'' ∧ R trace trace') := by
  have hp : measurePrefix ∈ (base.extend prefixesReserved).prefixIdents := by
    simp [Imperative.Logic.InitEnvWFParams.extend, prefixesReserved]
  have hid := idents_not_reserved hwf
  obtain ⟨σ₀, F⟩ := ρ₀
  have hF : WellFormedSemanticEval (P := Expression) F := hwf.toWellFormedSemanticEval
  have hσ : ∀ x, (σ₀ x).isSome → ¬ measurePrefix.toList.isPrefixOf x.name.toList :=
    fun x hx => hwf.reservedFreshCore x hx _ hp
  have hmeas : ∀ m ∈ Block.measures ss, MeasureEvaluates F m := fun m hm Γ σ hΓ hann =>
    Core.eval_of_annotates F Γ σ m _ hΓ hann (hwf.measuresTyped m hm)
  -- A big-step run of the source has one of the output with the same outcome.
  have hsim : ∀ {trace o}, BRun F ss σ₀ trace o → ∃ evs', BRun F ss' σ₀ evs' o ∧ R trace evs' :=
    fun hb =>
      have ⟨evs', hb', hins⟩ := run_sim hF.var hF.bool hF.exprCongr measureIdent_reserved hrel
        hb hwf.storeWellDefined hσ hid hwf.defUseOk hwf.fvarTypesOk hmeas
      ⟨evs', hb', hmono hins⟩
  refine ⟨fun ρ' trace h => ?_, fun l ρ' trace h => ?_⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨σ', F'⟩ := ρ'
    simp only at hE
    subst hE
    obtain ⟨evs', hb, hr⟩ := hsim (star_brun.1 h')
    exact ⟨_, evs', star_core π (brun_star hF.bool hb), rfl, hr⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨σ', F'⟩ := ρ'
    simp only at hE
    subst hE
    obtain ⟨evs', hb, hr⟩ := hsim (star_brun.2 h')
    exact ⟨_, evs', star_core π (brun_star hF.bool hb), rfl, hr⟩

/-- **Inserting the checks of loop invariants and measures over-approximates the traces of a
    Core statement list.**  Let a transformation `T` insert the checks of the loops of its
    input (`BlockRel []`).  For a call-free Core statement list `ss` (`Statements.noCalls`) that
    `T` maps to `ss'`, and every entry environment `ρ₀` satisfying `BlockInitEnvWF` of `ss` at
    `base` with the prefix of the measure snapshot variables reserved (`prefixesReserved`), when
    no prefix `base` reserves is a prefix of `measurePrefix` or starts with it (so that no
    snapshot name starts with one):
    * every finite trace of `ss` from `ρ₀` has a trace of `ss'` from `ρ₀` related to it by
      inserting assertions, each event's condition captured with the same value
      (`Trace.InsertsAsserts`), and then assumptions evaluating to `true` or copying an earlier
      inserted invariant assertion (`Trace.InsertsCheckedAssumes` over `InvCheck`), the
      conditions captured under a factory satisfying `WellFormedSemanticEval`;
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `ss'` from `ρ₀` ending in
      the same environment, in the same way, with a trace so related;
    * `ss'` satisfies `BlockInitEnvWF base` at `ρ₀`. -/
theorem overapproximatesTraces_of_blockRel (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {T : Statements → Option Statements} (hT : ∀ ss ss', T ss = some ss' → BlockRel [] ss ss') :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.InsertsAsserts (WellFormedSemanticEval (P := Expression)))
        (Trace.InsertsCheckedAssumes (WellFormedSemanticEval (P := Expression)) InvCheck []))
      -- Both executions start from the same environment.
      (· = ·)
      -- Completed runs end in the same environment.
      (· = ·)
      (EventLang.coreBlock π) (EventLang.coreBlock π) T
      -- The bridge to the big-step semantics requires a call-free source.
      (fun ss => Statements.noCalls ss = Bool.true)
      (base.extend prefixesReserved) base := by
  intro ss ss' ht hnc ρ₀ ρ₀' hEq hwf
  subst hEq
  have hrel := hT ss ss' ht
  have hp : measurePrefix ∈ (base.extend prefixesReserved).prefixIdents := by
    simp [Imperative.Logic.InitEnvWFParams.extend, prefixesReserved]
  have hF : WellFormedSemanticEval (P := Expression) ρ₀.factory := hwf.toWellFormedSemanticEval
  have hmono : ∀ {t t' : Trace Expression}, RComp (Trace.InsertsAsserts (· = ρ₀.factory))
      (Trace.InsertsCheckedAssumes (· = ρ₀.factory) InvCheck []) t t' →
      RComp (Trace.InsertsAsserts WellFormedSemanticEval)
        (Trace.InsertsCheckedAssumes WellFormedSemanticEval InvCheck []) t t' :=
    Trace.insertsAsserts_insertsCheckedAssumes_mono fun _ h => h ▸ hF
  have hruns := runs_of_gate π hrel hnc hwf hmono
  refine ⟨fun cfg trace h => ?_, hruns.1, hruns.2, blockInitEnvWF_of_blockRel hprefixes hrel hwf⟩
  have h' := star_evalE h hnc
  by_cases htr : trace = []
  · subst htr
    exact ⟨_, [], .refl _, [], .nil, .nil⟩
  obtain ⟨σ₀, F⟩ := ρ₀
  obtain ⟨evs', hb, hins⟩ := reach_sim hF.var hF.bool hF.exprCongr measureIdent_reserved hrel
    (star_breach h' htr) hwf.storeWellDefined (fun x hx => hwf.reservedFreshCore x hx _ hp)
    (idents_not_reserved hwf) hwf.defUseOk hwf.fvarTypesOk fun m hm Γ σ hΓ hann =>
      Core.eval_of_annotates F Γ σ m _ hΓ hann (hwf.measuresTyped m hm)
  obtain ⟨cfg', hc⟩ := breach_star hF.bool hb
  exact ⟨cfg', evs', star_core π hc, hmono hins⟩

/-- **Inserting the checks of loop invariants and measures over-approximates the traces of a
    Core statement list, its runs over one Lambda factory.**  Let a transformation `T` insert
    the checks of the loops of its input (`BlockRel []`).  For a call-free Core statement list
    `ss` that `T` maps to `ss'`, and every entry environment `ρ₀` over the Lambda factory `F`
    (`ρ₀.factory.factory = F`) satisfying `BlockInitEnvWF` of `ss` at `base` with
    `prefixesReserved` reserved, when no prefix `base` reserves is a prefix of `measurePrefix`
    or starts with it:
    * every finite trace of `ss` from `ρ₀` has a trace of `ss'` from `ρ₀` related to it by
      `Trace.InsertsAsserts` and then `Trace.InsertsCheckedAssumes` over `InvCheck`, the
      conditions captured under a factory satisfying `WellFormedSemanticEval`;
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `ss'` from `ρ₀` ending in
      the same environment, in the same way, with a trace so related, the conditions captured
      under a factory over `F`;
    * `ss'` satisfies `BlockInitEnvWF base` at `ρ₀`. -/
theorem overapproximatesTraces_over_of_blockRel (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {T : Statements → Option Statements} (hT : ∀ ss ss', T ss = some ss' → BlockRel [] ss ss')
    (F : Lambda.Factory CoreLParams) :
    OverapproximatesTraces2UptoWhen
      (RComp (Trace.InsertsAsserts (WellFormedSemanticEval (P := Expression)))
        (Trace.InsertsCheckedAssumes (WellFormedSemanticEval (P := Expression)) InvCheck []))
      (RComp (Trace.InsertsAsserts (fun G : Expression.Factory => G.factory = F))
        (Trace.InsertsCheckedAssumes (fun G : Expression.Factory => G.factory = F) InvCheck []))
      -- Both executions start from the same environment, over `F`.
      (fun (ρ₀ ρ₀' : Env Expression) => ρ₀ = ρ₀' ∧ ρ₀.factory.factory = F)
      -- Completed runs end in the same environment.
      (· = ·)
      (EventLang.coreBlock π) (EventLang.coreBlock π) T
      -- The bridge to the big-step semantics requires a call-free source.
      (fun ss => Statements.noCalls ss = Bool.true)
      (base.extend prefixesReserved) base := by
  intro ss ss' ht hnc ρ₀ ρ₀' ⟨hEq, hpin⟩ hwf
  subst hEq
  have h0 := overapproximatesTraces_of_blockRel π base hprefixes hT ss ss' ht hnc ρ₀ ρ₀ rfl hwf
  have hruns := runs_of_gate π (hT ss ss' ht) hnc hwf
    (Trace.insertsAsserts_insertsCheckedAssumes_mono fun _ h => h ▸ hpin)
  exact ⟨h0.1, hruns.1, hruns.2, h0.2.2.2⟩

/-- Sending `ss` to `ss'` and rejecting every other list inserts the checks of the loops of its
    input, when `ss'` is `ss` with the checks of its loops inserted. -/
theorem single_blockRel {ss ss' : Statements} (hrel : BlockRel [] ss ss') :
    ∀ s s'', (if s = ss then some ss' else none) = some s'' → BlockRel [] s s'' := by
  intro s s'' h
  split at h
  · rename_i hs
    subst hs
    cases h
    exact hrel
  · cases h

/-- **Assertion validity transported back through the insertion of loop invariant checks.**
    For an interpretation `I` under which conditions with the same value hold alike and every
    condition that evaluates to `true` holds, under factories satisfying
    `WellFormedSemanticEval`, and a call-free Core statement list `ss` with the checks of its
    loops inserted into `ss'` (`BlockRel []`): if, on every trace of `ss'` from every
    environment satisfying `BlockInitEnvWF base` of it, the inserted assertions of invariants
    (`InvCheck`) and every occurrence of the assertion `aid` hold under their preceding
    assumptions, then every occurrence of `aid` does on every trace of `ss` from every
    environment satisfying `BlockInitEnvWF` of `ss` at `base` with `prefixesReserved` reserved,
    when no prefix `base` reserves is a prefix of `measurePrefix` or starts with it. -/
theorem assertValid_of_blockRel (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {ss ss' : Statements}
    (hrel : BlockRel [] ss ss') (hnc : Statements.noCalls ss = Bool.true)
    {I : ConditionInterp Expression}
    (hstable : I.StableUnder (EventArg.SameValue (WellFormedSemanticEval (P := Expression))))
    (htrue : I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)))
    (hchecks : ∀ ρ₀ cfg trace, BlockInitEnvWF base ss' ρ₀ →
      (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss' ρ₀) trace cfg →
      Trace.AssertionsValidFromP Expression I InvCheck [] trace)
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF base ss') ss'
      aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF (base.extend prefixesReserved) ss) ss aid := by
  intro ρ₀ cfg trace hinit htrace
  have hr := overapproximatesTraces_of_blockRel π base hprefixes (single_blockRel hrel) ss ss'
    (ite_eq_left_iff.mpr fun h => absurd rfl h) hnc ρ₀ ρ₀ rfl hinit
  obtain ⟨cfg', trace', h', hins⟩ := hr.1 cfg trace htrace
  exact Trace.insertsAsserts_insertsCheckedAssumes_assertionsValidFromP_reflect hstable htrue
    (fun _ _ hl hm hk => ⟨hl ▸ hk.1, hm ▸ hk.2⟩) hins
    ((hchecks ρ₀ cfg' trace' hr.2.2.2 h').or I (hvalid ρ₀ cfg' trace' hr.2.2.2 h'))

/-- **A Hoare triple transported back through the insertion of loop invariant checks.**  For a
    call-free Core statement list `ss` with the checks of its loops inserted into `ss'`
    (`BlockRel []`), and a precondition admitting only entry environments over `F`: a Core
    triple `{Pre} ss' {Post}` over `F` (`Core.Logic.Hoare.Triple`, read by
    `DenoteBasedInterp F`) at `base` gives the triple `{Pre} ss {Post}` at `base` with
    `prefixesReserved` reserved, when no prefix `base` reserves is a prefix of `measurePrefix` or
    starts with it.  The triple of `ss'` makes the inserted assertions of invariants valid, so the
    assumptions of invariants following them restrict no run of `ss`. -/
theorem triple_of_blockRel (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {ss ss' : Statements}
    (hrel : BlockRel [] ss ss') (hnc : Statements.noCalls ss = Bool.true)
    {F : Lambda.Factory CoreLParams} {Pre Post : Env Expression → Prop}
    (hpin : ∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F)
    (h : Core.Logic.Hoare.Triple π base Pre ss' Post F) :
    Core.Logic.Hoare.Triple π (base.extend prefixesReserved) Pre ss Post F := by
  -- Conditions captured under a factory over `F` hold when they evaluate to `true`, and alike
  -- when they have the same value.
  have htrue : (DenoteBasedInterp F).TrueStutterHolds (fun G => G.factory = F) :=
    fun _ hc he _ => .inl ⟨hc, he⟩
  have hstable : (DenoteBasedInterp F).StableUnder
      (EventArg.SameValue (fun G : Expression.Factory => G.factory = F)) := by
    intro w a b ⟨ha, hf, _, hv⟩
    show (a.factory.factory = F ∧ Expression.eval a.factory a.store a.expr =
        some (HasBool.ttVal a.factory)) ∨ (a.factory.factory ≠ F ∧ w.offFactoryHolds a) ↔
      (b.factory.factory = F ∧ Expression.eval b.factory b.store b.expr =
        some (HasBool.ttVal b.factory)) ∨ (b.factory.factory ≠ F ∧ w.offFactoryHolds b)
    rw [hv, hf]
    simp only [show a.factory.factory = F from ha, ne_eq, not_true_eq_false, false_and, or_false]
  exact overapproximatesTraces2UptoWhen_triple_general (EventLang.coreBlock π)
    (EventLang.coreBlock π) (DenoteBasedInterp F) _ _ (· = ·) _ _ _ base ss ss'
    (ite_eq_left_iff.mpr fun h => absurd rfl h)
    (overapproximatesTraces_over_of_blockRel π base hprefixes (single_blockRel hrel) F) h hnc
    (fun ρ₀ hpre => ⟨rfl, hpin ρ₀ hpre⟩)
    (fun _ _ hins hv =>
      Trace.insertsAsserts_insertsCheckedAssumes_assertionsValid_reflect hstable htrue hins hv)
    (fun _ _ hins hv hr => Trace.insertsAsserts_insertsCheckedAssumes_reachable_transfer hstable
      htrue hins (Trace.AssertionsValidFromP.mono_keep _ (fun _ _ => trivial) hv) hr)
    (fun _ _ h hp => h ▸ hp)

/-- **A verifier run after inserting the checks of loop invariants and measures is sound on the
    source.**  For a transformation `T` inserting the checks of the loops of its input
    (`BlockRel []`), an interpretation `I` under which conditions with the same value hold alike
    and every condition that evaluates to `true` holds, under factories satisfying
    `WellFormedSemanticEval`, and a verifier `analyze` that passes only lists whose traces from
    entries satisfying `BlockInitEnvWF base` have every assertion valid under `I`: running `T`
    and then `analyze` passes only call-free lists whose traces, from entries satisfying the
    gate at `base` with `prefixesReserved` reserved, have every assertion valid, when no prefix
    `base` reserves is a prefix of `measurePrefix` or starts with it.  The verifier checks the
    inserted assertions of invariants as well. -/
theorem validOnTracesVerifier_of_blockRel (base : InitEnvWFParams)
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {T : Statements → Option Statements} (hT : ∀ ss ss', T ss = some ss' → BlockRel [] ss ss')
    {I : ConditionInterp Expression}
    (hstable : I.StableUnder (EventArg.SameValue (WellFormedSemanticEval (P := Expression))))
    (htrue : I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)))
    {analyze : Statements → Bool}
    (hsound : Analysis.ValidOnTracesVerifier (EventLang.coreBlock π) I (BlockInitEnvWF base)
      analyze) :
    Analysis.ValidOnTracesVerifier (EventLang.coreBlock π) I
      (fun ss ρ₀ => Statements.noCalls ss = Bool.true ∧
        BlockInitEnvWF (base.extend prefixesReserved) ss ρ₀)
      (Analysis.thenVerify (L₁ := EventLang.coreBlock π) (L₂ := EventLang.coreBlock π) T
        analyze) :=
  fun ss hpass ρ₀ cfg trace ⟨hnc, hwf⟩ htrace =>
    Analysis.ValidOnTracesVerifier.of_overapproximatesTraces2UptoWhen
      (fun _ _ hins hv =>
        Trace.insertsAsserts_insertsCheckedAssumes_assertionsValid_reflect hstable htrue hins hv)
      (overapproximatesTraces_of_blockRel π base hprefixes hT) hsound ss hpass ρ₀ cfg trace
      ⟨hnc, hwf, ρ₀, rfl⟩ htrace

end -- public section

end Core.InsertLoopInvAsserts

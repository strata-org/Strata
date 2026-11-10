/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopElimCorrect
public import Strata.Transform.SpecificationProps
public import Strata.Transform.SpecHoareConnection
public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.LangDef
public import Strata.DL.Imperative.Logic.HoareTemplate
import Strata.Transform.DeadDefElimProps
import Strata.DL.Imperative.BigStep.Adequacy
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.Transform.LoopElimProps
import all Strata.Languages.Core.Factory

/-! # Core loop elimination over `BlockRel` images

The Core-level trace results of `LoopElimCoreCorrect`, stated for every transformation `T` whose
outputs are `BlockRel` images of its inputs from the entries satisfying the gate
`BlockInitEnvWF` at `params` with block-label prefixes `L` reserved.  The pure pass
`Block.loopElim` is one with `L = [Core.loopElimPrefix]` (`Core.LoopElim.blockRel_of_loopElim`),
and each body the Core pass `Core.loopElim` returns gives one with `L = []`
(`Core.LoopElim.loopElim_body_blockRel`, through `Core.LoopElim.single_blockRel`).  The proofs
bridge the call-free Core event semantics to the big-step semantics and use the simulations of
`LoopElimCorrect`.  They are Core-level, so they are not in `LoopElimCorrect`, which is
Imperative-level, nor in `LoopElimProps`, which `LoopElimCorrect` imports.

Key theorems: `Core.LoopElim.overapproximatesTraces_of_blockRel`,
`Core.LoopElim.overapproximatesTraces_whenLoopExitsLocal_of_blockRel`,
`Core.LoopElim.assertValid_of_blockRel`, `Core.LoopElim.triple_of_blockRel`,
`Core.LoopElim.validOnTracesVerifier_of_blockRel`. -/

namespace Core.LoopElim

open Core Core.Logic Imperative Imperative.BigStep Imperative.LoopElim Core.DeadDefElim
  Imperative.Specification Imperative.Specification.Transform Strata.Logic

public section

variable (π : String → Option Procedure)

/-- **Eliminating the loops of a Core statement list over-approximates its traces.**  Let a
    transformation `T` eliminate the loops of its input (`BlockRel`) from every entry satisfying
    `BlockInitEnvWF` at `params` with the block-label prefixes `L` reserved.  For a call-free
    Core statement list `ss` that `T` maps to `ss'`, and every such entry environment `ρ₀`:
    * every finite trace of `ss` from `ρ₀` has a trace of `ss'` from `ρ₀` ending with its last
      event (`Trace.PreservesLastEvent`) after events related to those before it by dropping
      events (`Trace.MayDropEvents`) and inserting true assumptions
      (`Trace.InsertsTrueAssumes`), followed by true assumptions (`Trace.HasExtraEvents`);
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `ss'` from `ρ₀` ending in
      the same environment, in the same way, with a trace related to the source's by dropping
      events and inserting true assumptions;
    * `ss'` satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem overapproximatesTraces_of_blockRel (params : InitEnvWFParams) (L : List String)
    {T : Statements → Option Statements}
    (hT : ∀ ss ss' ρ, T ss = some ss' → BlockInitEnvWF (params.extendBlockLabels L) ss ρ →
      BlockRel ss ss') :
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
      (EventLang.coreBlock π) (EventLang.coreBlock π) T
      -- The bridge to the big-step semantics requires a call-free source.
      (fun ss => Statements.noCalls ss = Bool.true)
      (params.extendBlockLabels L) params := by
  intro ss ss' ht hnc ρ₀ ρ₀' hEq hwf
  subst hEq
  have hrel := hT ss ss' ρ₀ ht hwf
  obtain ⟨σ₀, F⟩ := ρ₀
  have hWB := hwf.bool
  have hvar := hwf.var
  have hF : WellFormedSemanticEval (P := Expression) F := hwf.toWellFormedSemanticEval
  have hdu := hwf.defUseOk
  have hT := hwf.storeWellDefined
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_, ?_⟩
  · have h' := star_evalE h hnc
    by_cases htr : trace = []
    · subst htr
      exact ⟨_, [], .refl _, [], [], rfl, .inl ⟨rfl, rfl⟩, .nil⟩
    obtain ⟨evs', hb, habs⟩ := reach_sim hvar hWB hF hrel hdu hT (star_breach h' htr)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', evs', star_core π hc, evs', [], by simp, habs, .nil⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨evs', hb, habs⟩ := run_sim hvar hWB hF hrel hdu hT (star_brun.1 h')
    obtain ⟨σ', F'⟩ := ρ'
    simp only at hE
    subst hE
    exact ⟨_, evs', star_core π (brun_star hWB hb), rfl, habs⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨evs', hb, habs⟩ := run_sim hvar hWB hF hrel hdu hT (star_brun.2 h')
    obtain ⟨σ', F'⟩ := ρ'
    simp only at hE
    subst hE
    exact ⟨_, evs', star_core π (brun_star hWB hb), rfl, habs⟩
  · exact blockInitEnvWF_of_blockRel hrel hwf

/-- **Eliminating the loops of a Core statement list whose loop iterations never leave their loop
    by an `exit` over-approximates its traces, its completed runs reflecting assertion validity
    under `DenoteBasedInterp F`.**  For `T` as in `overapproximatesTraces_of_blockRel`, a
    call-free list `ss` with `Block.loopExitsLocal ss` that `T` maps to `ss'`, and every entry
    environment over `F` satisfying the gate at `params` with `L` reserved: as
    `overapproximatesTraces_of_blockRel`, with every terminating or exiting run of `ss` matched
    by a run of `ss'` whose trace also has valid assertions only if the source's has
    (`Trace.ImpliesAssertValidity`) and is reachable if the source's is
    (`Trace.ImpliesReachability`), under `DenoteBasedInterp F`. -/
theorem overapproximatesTraces_whenLoopExitsLocal_of_blockRel (params : InitEnvWFParams)
    (L : List String) {T : Statements → Option Statements}
    (hT : ∀ ss ss' ρ, T ss = some ss' → BlockInitEnvWF (params.extendBlockLabels L) ss ρ →
      BlockRel ss ss')
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
      (EventLang.coreBlock π) (EventLang.coreBlock π) T
      -- The bridge to the big-step semantics requires a call-free source; no loop iteration
      -- leaves its loop by an `exit`.
      (fun ss => Statements.noCalls ss = Bool.true ∧ Block.loopExitsLocal ss)
      (params.extendBlockLabels L) params := by
  intro ss ss' ht ⟨hnc, hloc⟩ ρ₀ ρ₀' ⟨hEq, hpin⟩ hwf
  subst hEq
  have h0 := overapproximatesTraces_of_blockRel π params L hT ss ss' ht hnc ρ₀ ρ₀ rfl hwf
  have hrel := hT ss ss' ρ₀ ht hwf
  obtain ⟨σ₀, F₀⟩ := ρ₀
  have hWB := hwf.bool
  have hvar := hwf.var
  have hF : WellFormedSemanticEval (P := Expression) F₀ := hwf.toWellFormedSemanticEval
  have hdu := hwf.defUseOk
  have hT := hwf.storeWellDefined
  -- A condition captured under the entry factory, over `F`, holds when it evaluates to `true`.
  have htr : (DenoteBasedInterp F).TrueStutterHolds (· = F₀) :=
    fun _ hc he _ => .inl ⟨hc ▸ hpin, he⟩
  -- A run of the source as a big-step run has a run of the output with the same outcome.
  have hsim : ∀ {trace o}, BRun F₀ ss σ₀ trace o → ∃ evs', BRun F₀ ss' σ₀ evs' o ∧
      RComp Trace.MayDropEvents
        (Trace.InsertsTrueAssumes (WellFormedSemanticEval (P := Expression))) trace evs' ∧
      Trace.ImpliesAssertValidity (DenoteBasedInterp F) trace evs' ∧
      Trace.ImpliesReachability (DenoteBasedInterp F) trace evs' := by
    intro trace o hb
    obtain ⟨evs', hb', habs, hv⟩ :=
      run_sim_valid (allowed := (· = F₀)) htr hvar hWB rfl hrel hloc hdu hT hb
    exact ⟨evs', hb', Trace.mayDropEvents_insertsTrueAssumes_mono (fun _ h => h ▸ hF) habs,
      hv, fun ⟨w, hw⟩ => ⟨w, Trace.mayDropEvents_insertsTrueAssumes_assumptionsHold htr habs hw⟩⟩
  refine ⟨h0.1, fun ρ' trace h => ?_, fun l ρ' trace h => ?_, h0.2.2.2⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨σ', F'⟩ := ρ'
    simp only at hE
    subst hE
    obtain ⟨evs', hb, hrel'⟩ := hsim (star_brun.1 h')
    exact ⟨_, evs', star_core π (brun_star hWB hb), rfl, hrel'⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨σ', F'⟩ := ρ'
    simp only at hE
    subst hE
    obtain ⟨evs', hb, hrel'⟩ := hsim (star_brun.2 h')
    exact ⟨_, evs', star_core π (brun_star hWB hb), rfl, hrel'⟩

/-- **Assertion validity transported back through loop elimination.**  For an interpretation `I`
    under which every condition that evaluates to `true` under a factory satisfying
    `WellFormedSemanticEval` holds, and a call-free Core statement list `ss` with its loops
    eliminated into `ss'` (`BlockRel`) from every entry satisfying `BlockInitEnvWF` at `params`
    with `L` reserved: validity of the assertion `aid` on `ss'` from every environment satisfying
    `BlockInitEnvWF params ss'` gives its validity on `ss` from every environment satisfying the
    gate of `ss` at `params` with `L` reserved. -/
theorem assertValid_of_blockRel (params : InitEnvWFParams) (L : List String)
    {ss ss' : Statements}
    (hrel : ∀ ρ, BlockInitEnvWF (params.extendBlockLabels L) ss ρ → BlockRel ss ss')
    (hnc : Statements.noCalls ss = Bool.true) {I : ConditionInterp Expression}
    (htrue : I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)))
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF params ss') ss' aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF (params.extendBlockLabels L) ss) ss aid :=
  overapproximatesTraces2UptoWhen_assertValid_of_reflectsLastAssertion I
    (Trace.PreservesLastEvent.reflectsLastAssertion fun h hw =>
      Trace.mayDropEvents_insertsTrueAssumes_assumptionsHold htrue h hw)
    (· = ·) (EventLang.coreBlock π)
    (EventLang.coreBlock π) _ _ _ params
    (overapproximatesTraces_of_blockRel π params L (single_blockRel hrel))
    (ite_eq_left_iff.mpr fun h => absurd rfl h) hnc
    (fun _ _ _ _ _ h => have ⟨_, hp⟩ := star_prefix (star_evalE h hnc) rfl; ⟨_, star_core π hp⟩)
    hvalid

/-- **A Hoare triple transported back through loop elimination.**  For a call-free Core
    statement list `ss` whose loop iterations never leave their loop by an `exit`
    (`Block.loopExitsLocal`), with its loops eliminated into `ss'` (`BlockRel`) from every entry
    satisfying `BlockInitEnvWF` at `params` with `L` reserved, and a precondition admitting only
    entry environments over `F`: a Core triple `{Pre} ss' {Post}` over `F` at `params` gives the
    triple `{Pre} ss {Post}` at `params` with `L` reserved. -/
theorem triple_of_blockRel (params : InitEnvWFParams) (L : List String)
    {ss ss' : Statements}
    (hrel : ∀ ρ, BlockInitEnvWF (params.extendBlockLabels L) ss ρ → BlockRel ss ss')
    (hnc : Statements.noCalls ss = Bool.true) (hloc : Block.loopExitsLocal ss)
    {F : Lambda.Factory CoreLParams} {Pre Post : Env Expression → Prop}
    (hpin : ∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F)
    (h : Core.Logic.Hoare.Triple π params Pre ss' Post F) :
    Core.Logic.Hoare.Triple π (params.extendBlockLabels L) Pre ss Post F :=
  overapproximatesTraces2UptoWhen_triple_general (EventLang.coreBlock π) (EventLang.coreBlock π)
    (DenoteBasedInterp F) _ _ (· = ·) _ _ _ params ss ss'
    (ite_eq_left_iff.mpr fun h => absurd rfl h)
    (overapproximatesTraces_whenLoopExitsLocal_of_blockRel π params L (single_blockRel hrel) F)
    h ⟨hnc, hloc⟩
    (fun ρ₀ hpre => ⟨rfl, hpin ρ₀ hpre⟩) (fun _ _ h => h.2.1) (fun _ _ h _ => h.2.2)
    (fun _ _ h hp => h ▸ hp)

/-- **A verifier run after loop elimination is sound on the source.**  For a transformation `T`
    eliminating the loops of its input (`BlockRel`) from every entry satisfying `BlockInitEnvWF`
    at `params` with `L` reserved, an interpretation `I` under which every condition that
    evaluates to `true` under a factory satisfying `WellFormedSemanticEval` holds, and a
    verifier `analyze` that passes only lists whose traces from entries satisfying
    `BlockInitEnvWF params` have every assertion valid under `I`: running `T` and then `analyze`
    passes only call-free lists whose traces, from entries satisfying the gate at `params` with
    `L` reserved, have every assertion valid. -/
theorem validOnTracesVerifier_of_blockRel (params : InitEnvWFParams) (L : List String)
    {T : Statements → Option Statements}
    (hT : ∀ ss ss' ρ, T ss = some ss' → BlockInitEnvWF (params.extendBlockLabels L) ss ρ →
      BlockRel ss ss')
    {I : ConditionInterp Expression}
    (htrue : I.TrueStutterHolds (WellFormedSemanticEval (P := Expression)))
    {analyze : Statements → Bool}
    (hsound : Analysis.ValidOnTracesVerifier (EventLang.coreBlock π) I (BlockInitEnvWF params)
      analyze) :
    Analysis.ValidOnTracesVerifier (EventLang.coreBlock π) I
      (fun ss ρ₀ => Statements.noCalls ss = Bool.true ∧
        BlockInitEnvWF (params.extendBlockLabels L) ss ρ₀)
      (Analysis.thenVerify (L₁ := EventLang.coreBlock π) (L₂ := EventLang.coreBlock π) T
        analyze) :=
  Analysis.ValidOnTracesVerifier.of_overapproximatesTraces2UptoWhen_of_reflectsLastAssertion
    (Trace.PreservesLastEvent.reflectsLastAssertion fun h hw =>
      Trace.mayDropEvents_insertsTrueAssumes_assumptionsHold htrue h hw)
    (overapproximatesTraces_of_blockRel π params L hT)
    (fun _ hnc _ _ _ _ _ h =>
      have ⟨_, hp⟩ := star_prefix (star_evalE h hnc) rfl; ⟨_, star_core π hp⟩)
    hsound

end -- public section

end Core.LoopElim

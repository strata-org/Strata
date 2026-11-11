/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SpecHoareConnection
public import Strata.Transform.Specification
public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.Languages.Core.Logic.TraceInterpUsingDenoteProps
public import Strata.Languages.Core.StmtExtendCallBridgeProps
public import Strata.DL.Imperative.BigStep.Sem
import Strata.DL.Imperative.Logic.TraceInterpProps

/-! # Transporting Core Hoare triples across pointwise trace over-approximations

A Core triple (`Core.Logic.Hoare.Triple`) reads conditions by `DenoteBasedInterp F`, which is
stable under an event-argument relation only for conditions captured under a runtime factory over
`F` (`denoteBasedInterp_stableUnder`).  Every event of a call-free Core run is captured under the
factory of its entry (`coreBlock_events_factory`), so for entries over `F` the restriction costs
nothing.

`triple_of_overapproximatesTraces_matches` transports a target triple back to a call-free
source across an `OverapproximatesTracesUptoWhen` whose trace relation matches events pointwise
(`List.Rel₂ (Event.Matches R)`) by a relation `R` under which evaluation to `true` is stable,
such as `Trace.WithWF (EventArg.ExtendsEnv _)` or Dead-definition elimination's `DDEventRel`.

`triple_of_overapproximatesTraces_matches_sameEntry` is its instance for passes whose target runs
from the source's entry.

Key theorems: `triple_of_overapproximatesTraces_matches`,
`triple_of_overapproximatesTraces_matches_sameEntry`. -/

public section

namespace Core.Logic

open Imperative Imperative.Specification Imperative.Specification.Transform Strata.Logic

/-- Pointwise matching by `R` is matching by `R` restricted to source arguments over `F`,
    when every source event is captured over `F`. -/
private theorem rel₂_matches_restrict {R : EventArg Expression → EventArg Expression → Prop}
    {F : Lambda.Factory CoreLParams} :
    ∀ {s t : Trace Expression}, List.Rel₂ (Event.Matches R) s t →
      (∀ ev ∈ s, ev.condition.factory.factory = F) →
      List.Rel₂ (Event.Matches (fun a b => R a b ∧ a.factory.factory = F)) s t
  | _, _, .nil, _ => .nil
  | e :: _, e' :: _, .cons h hrest, hs => by
    refine .cons ?_ (rel₂_matches_restrict hrest fun ev hev => hs ev (List.mem_cons_of_mem _ hev))
    have he := hs e List.mem_cons_self
    cases e <;> cases e' <;> simp_all [Event.Matches, Event.condition]

/-- **A Core triple transported back across a pointwise trace over-approximation.**  Let `T`
    over-approximate the traces of call-free Core statement lists (`EventLang.coreBlock`) by
    those of `L₂`, matching events pointwise by a relation `R` that keeps the factory, label and
    metadata and under which evaluation to `true` is stable.  For a call-free `ss` that `T` maps
    to `s'` and a precondition admitting only entries over `F`: a triple `{Pre'} s' {Post'}` of
    `L₂` read by `DenoteBasedInterp F` gives the Core triple `{Pre} ss {Post}`, when each source
    entry satisfying `Pre` and the gate is related by `Rin` to a target entry satisfying `Pre'`,
    and `Post'` of a target final environment gives `Post` of each source final environment
    related to it by `Rout`; such a source environment has the entry's factory and keeps every
    binding of the entry defined. -/
theorem triple_of_overapproximatesTraces_matches (π : String → Option Procedure)
    {L₂ : EventLang Expression (Event Expression)}
    {R : EventArg Expression → EventArg Expression → Prop}
    (hstable : (Imperative.BigStep.evalInterp : ConditionInterp Expression).StableUnder R)
    (hsame : ∀ {a b}, R a b → b.factory = a.factory ∧ a.label = b.label ∧ a.metadata = b.metadata)
    {Rin Rout : Relation (Env Expression)} {T : Statements → Option L₂.StmtT}
    {pre : Statements → Prop} {params₁ : InitEnvWFParams} {params₂ : L₂.InitEnvWFParamsTy}
    (hsem : OverapproximatesTracesUptoWhen (List.Rel₂ (Event.Matches R)) Rin Rout
      (EventLang.coreBlock π) L₂ T pre params₁ params₂)
    {ss : Statements} {s' : L₂.StmtT} (ht : T ss = some s') (hpre : pre ss)
    (hnc : Statements.noCalls ss = Bool.true)
    {F : Lambda.Factory CoreLParams} {Pre Post Pre' Post' : Env Expression → Prop}
    (hpin : ∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F)
    (hin : ∀ ρ₀, Pre ρ₀ → BlockInitEnvWF params₁ ss ρ₀ → ∃ ρ₀', Rin ρ₀ ρ₀' ∧ Pre' ρ₀')
    (hpost : ∀ ρ₀ ρ' ρ'', Pre ρ₀ → BlockInitEnvWF params₁ ss ρ₀ → ρ'.factory = ρ₀.factory →
      (∀ x, (ρ₀.store x).isSome = Bool.true → (ρ'.store x).isSome = Bool.true) →
      Rout ρ' ρ'' → Post' ρ'' → Post ρ')
    (h : Strata.Logic.Hoare.TripleWith L₂ (DenoteBasedInterp F) params₂ Pre' s' Post') :
    Hoare.Triple π params₁ Pre ss Post F := by
  have hstab := denoteBasedInterp_stableUnder (F := F) hstable fun h => (hsame h).1
  have hsame' : ∀ {a b}, (R a b ∧ a.factory.factory = F) →
      a.label = b.label ∧ a.metadata = b.metadata := fun h => (hsame h.1).2
  refine overapproximatesTraces2UptoWhen_triple_of_sourceRuns (EventLang.coreBlock π) L₂
    (DenoteBasedInterp F) _ Rin Rout T pre params₁ params₂ ss s' ht hsem h hpre
    (fun tr => ∀ ev ∈ tr, ev.condition.factory.factory = F) (fun _ => True) ?_
    (fun _ _ _ _ _ _ _ _ => trivial) hin ?_ ?_ ?_
  · intro ρ₀ ρ' trace hp _ hrun ev hev
    rw [coreBlock_terminatesAt_events_factory hnc hrun ev hev]
    exact hpin ρ₀ hp
  · intro _ _ hs _ hrel hv
    exact Trace.AssertionsValid.of_all_assertionValid _ fun aid =>
      Trace.AssertionValidFrom_matches_reflect hstab hsame' aid .nil
        (rel₂_matches_restrict hrel hs) (Trace.AssertionValid.of_assertionsValid _ aid hv)
  · intro _ _ hs _ hrel _ ⟨w, hw⟩
    exact ⟨w, Trace.AssumptionsHold_matches_transfer hstab (rel₂_matches_restrict hrel hs) hw⟩
  · intro ρ₀ ρ' ρ'' trace hp hwf hrun
    obtain ⟨hf, hd⟩ := coreBlock_terminatesAt_env hnc hrun
    exact hpost ρ₀ ρ' ρ'' hp hwf hf hd

/-- **A Core triple transported back across a pointwise trace over-approximation from the same
    entry.**  For `T` over-approximating the traces of call-free Core statement lists by those of
    `L₂` from the same entry (`Rin` is equality), matching events pointwise by a relation `R`
    that keeps the factory, label and metadata and under which evaluation to `true` is stable:
    for a call-free `ss` that `T` maps to `s'` and a precondition admitting only entries over
    `F`, a triple `{Pre} s' {Post'}` of `L₂` read by `DenoteBasedInterp F` gives the Core triple
    `{Pre} ss {Post}`, when `Post'` of a target final environment gives `Post` of each source
    final environment related to it by `Rout`, for entries satisfying `Pre` and the gate; such
    a source environment has the entry's factory and keeps every binding of the entry
    defined. -/
theorem triple_of_overapproximatesTraces_matches_sameEntry (π : String → Option Procedure)
    {L₂ : EventLang Expression (Event Expression)}
    {R : EventArg Expression → EventArg Expression → Prop}
    (hstable : (Imperative.BigStep.evalInterp : ConditionInterp Expression).StableUnder R)
    (hsame : ∀ {a b}, R a b → b.factory = a.factory ∧ a.label = b.label ∧ a.metadata = b.metadata)
    {Rout : Relation (Env Expression)} {T : Statements → Option L₂.StmtT}
    {pre : Statements → Prop} {params₁ : InitEnvWFParams} {params₂ : L₂.InitEnvWFParamsTy}
    (hsem : OverapproximatesTracesUptoWhen (List.Rel₂ (Event.Matches R)) (· = ·) Rout
      (EventLang.coreBlock π) L₂ T pre params₁ params₂)
    {ss : Statements} {s' : L₂.StmtT} (ht : T ss = some s') (hpre : pre ss)
    (hnc : Statements.noCalls ss = Bool.true)
    {F : Lambda.Factory CoreLParams} {Pre Post Post' : Env Expression → Prop}
    (hpin : ∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = F)
    (hpost : ∀ ρ₀ ρ' ρ'', Pre ρ₀ → BlockInitEnvWF params₁ ss ρ₀ → ρ'.factory = ρ₀.factory →
      (∀ x, (ρ₀.store x).isSome = Bool.true → (ρ'.store x).isSome = Bool.true) →
      Rout ρ' ρ'' → Post' ρ'' → Post ρ')
    (h : Strata.Logic.Hoare.TripleWith L₂ (DenoteBasedInterp F) params₂ Pre s' Post') :
    Hoare.Triple π params₁ Pre ss Post F :=
  triple_of_overapproximatesTraces_matches π hstable hsame hsem ht hpre hnc hpin
    (fun ρ₀ hp _ => ⟨ρ₀, rfl, hp⟩) hpost h

end Core.Logic

end -- public section

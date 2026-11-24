/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.HoareTemplate
public import Strata.DL.Imperative.Logic.TraceRelations
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.DL.Imperative.Logic.TerminationProps

/-! # Bridges between the Hoare logic and the soundness specification

## Connection between `Hoare.TripleWith` and assertion validity

- `allAssertsValidOnTraces_implies_triple_valid` — validity of all assertions
  on every reachable trace implies `Hoare.TripleWith` with the trivial
  postcondition (the converse is
  `Strata.Logic.Hoare.TripleWith.true_iff_allAssertsValidOnTracesWhen`);
- `triple_implies_assertValidOnTracesWhen` — a `Hoare.TripleWith`, together with
  initial-environment well-formedness, implies per-identifier validity on every
  reachable trace.

Both directions hold without termination: the triple validates the assertions of every
finite execution, finished or not.

## Connection between `Hoare.TripleWith` and `OverapproximatesTraces2UptoWhen`

`Strata.Logic.Hoare.TripleWith` is `EventLang`-generic, so a triple proved about
the target of a translation transports back to the source along a trace
overapproximation. The triple reads every finite execution for its assertions and the
completed runs for its postcondition, so a transport reads the prefix clause of the
overapproximation for the former and its run clauses for the latter:

- `overapproximatesTraces2UptoWhen_triple_of_valid` is the run part alone: given the validity
  of the source's assertions on every finite execution, it transports the postcondition across
  the run trace relation `Rtrace_full`.
- `overapproximatesTraces2UptoWhen_triple_of_sourceRuns` transports a `TripleWith` when the
  target runs from an entry related to the source's by `Rin`, under its own precondition and
  postcondition.  It requires target validity to reflect to the source across the prefix
  relation `Rtrace`, source-run reachability to transfer to a target run whose assertions are
  valid across `Rtrace_full`, and the target postcondition to transport backward across `Rout`,
  with the compatibility premises restricted to traces of finite executions (`Src`, `Tgt`) and
  the postcondition transport to final environments of source runs.
- `overapproximatesTraces2UptoWhen_triple_of_reflectsLastAssertion` is the same transport for a
  prefix relation that only reflects the last assertion of a source trace
  (`Trace.ReflectsLastAssertion`).
- `overapproximatesTraces2UptoWhen_triple_general` is `_of_sourceRuns` at `Rin ρ₀ ρ₀`.
- `overapproximatesTracesUptoWhen_triple_general` is its instance for
  `OverapproximatesTracesUptoWhen Rtrace (· = ·) Rout`. It requires target-trace
  validity to reflect to the source trace, source-trace reachability to transfer
  to the target trace, and the target postcondition to transport backward across
  `Rout`.

The all-equality special cases are preserved as corollaries, where the three
compatibility assumptions hold trivially (equal witnesses substitute):

- `overapproximatesTraces_triple` — `OverapproximatesTraces` at trace-relation
  equality preserves `Hoare.TripleWith`.
- `overapproximatesTracesWhen_triple` — the same for `OverapproximatesTracesWhen`,
  under a precondition on the source statement.

## Specialization to `Trace.StuttersEnv`

`overapproximatesTracesUptoWhen_triple_stuttersEnv` instantiates the general
theorem at `Rtrace := Trace.StuttersEnv allowedVarName allowedFactory`. Because
target-only bindings may change a captured condition's meaning, the
specialization requires both `ConditionInterp.StableUnderExtendsEnv` for paired
events and `ConditionInterp.TrueStutterHolds allowedFactory` for events
inserted or removed by stuttering. The trace relation carries the factory restriction only
for conditions that actually stutter, so an interpretation tied to one factory
need not interpret operational truth under unrelated factories.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic

/-! ## Connection between `Hoare.TripleWith` and assertion validity -/

variable {P : PureExpr}

/-- Trace-native validity of every assertion implies a `Hoare.TripleWith` with
    the trivial postcondition: the triple asks for the validity of the assertions of
    every finite execution, which is what `AllAssertsValidOnTracesWhen` gives. -/
theorem allAssertsValidOnTraces_implies_triple_valid
    (EL : EventLang P (Event P)) (I : ConditionInterp P)
    (params : EL.InitEnvWFParamsTy) (Pre : Env P → Prop) (s : EL.StmtT)
    (hvalid : AllAssertsValidOnTracesWhen EL I Pre s) :
    Strata.Logic.Hoare.TripleWith EL I params Pre s (fun _ => True) :=
  fun ρ₀ hpre _ => ⟨fun cfg trace hrun => hvalid ρ₀ cfg trace hpre hrun, fun _ _ _ _ => trivial⟩

/-- A `Hoare.TripleWith` yields per-identifier validity on every reachable
trace when all permitted initial environments are well-formed: the triple
validates the assertions of every finite execution. -/
theorem triple_implies_assertValidOnTracesWhen
    (EL : EventLang P (Event P)) (I : ConditionInterp P)
    (params : EL.InitEnvWFParamsTy) {Pre Post : Env P → Prop} {s : EL.StmtT}
    (htriple : Strata.Logic.Hoare.TripleWith EL I params Pre s Post)
    (hinit : ∀ ρ₀, Pre ρ₀ → EL.initEnvWF params s ρ₀)
    (aid : AssertId P) :
    AssertValidOnTracesWhen EL I Pre s aid := fun ρ₀ cfg trace hpre hrun =>
  Trace.AssertionValid.of_assertionsValid I aid
    ((htriple ρ₀ hpre (hinit ρ₀ hpre)).1 cfg trace hrun)

namespace Transform

variable {P : PureExpr}

/-- **Trace-overapproximation transport for `TripleWith`, given the validity of the source's
    assertions.**  The common part of the transports below: when every finite execution of the
    source `st` from an entry satisfying `Pre` and the gate is already known to have valid
    assertions (`hvalid`), a triple `{Pre'} s' {Post'}` of the target `L₂` gives the
    postcondition part of `{Pre} st {Post}` across the run clauses of an
    `OverapproximatesTraces2UptoWhen` with run trace relation `Rtrace_full`.
    The target runs from an entry `ρ₀'` related to the source's by `Rin` that satisfies `Pre'`;
    `Src` holds of the trace of every completed run of `st` from an entry satisfying `Pre` and
    the gate, and `Tgt` of every completed run of `s'` from a related entry satisfying `Pre'`. -/
theorem overapproximatesTraces2UptoWhen_triple_of_valid
    (L₁ L₂ : EventLang P (Event P)) (I : ConditionInterp P) {Rtrace : Relation (Trace P)}
    (Rtrace_full : Relation (Trace P)) (Rin Rout : Relation (Env P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTraces2UptoWhen Rtrace Rtrace_full Rin Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post Pre' Post' : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre' s' Post')
    (hsource_pre : pre st)
    (hvalid : ∀ ρ₀ cfg trace, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ →
      L₁.traceStar (L₁.stmtCfg st ρ₀) trace cfg → Trace.AssertionsValid P I trace)
    (Src Tgt : Trace P → Prop)
    (hsrc : ∀ ρ₀ ρ' trace, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ →
      L₁.TerminatesAt st ρ₀ trace ρ' → Src trace)
    (htgt : ∀ ρ₀ ρ₀' ρ'' trace', Pre ρ₀ → Rin ρ₀ ρ₀' → Pre' ρ₀' →
      L₂.TerminatesAt s' ρ₀' trace' ρ'' → Tgt trace')
    (hin : ∀ ρ₀, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ → ∃ ρ₀', Rin ρ₀ ρ₀' ∧ Pre' ρ₀')
    (hreach_transfer : ∀ sourceTr targetTr, Src sourceTr → Tgt targetTr →
      Rtrace_full sourceTr targetTr → Trace.AssertionsValid P I targetTr →
      Trace.Reachable P I sourceTr → Trace.Reachable P I targetTr)
    (hpost_transport : ∀ ρ₀ ρ' ρ'' trace, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ →
      L₁.TerminatesAt st ρ₀ trace ρ' → Rout ρ' ρ'' → Post' ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post := by
  intro ρ₀ hpre hinit
  refine ⟨fun cfg trace hrun => hvalid ρ₀ cfg trace hpre hinit hrun,
    fun ρ' trace hrun hreach => ?_⟩
  have hs := hsrc ρ₀ ρ' trace hpre hinit hrun
  obtain ⟨ρ₀', hR, hpre'⟩ := hin ρ₀ hpre hinit
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀' hR hinit
  -- the related target run finishes the same way
  obtain ⟨ρ'', trace', hrun', hout, htr⟩ : ∃ ρ'' trace', L₂.TerminatesAt s' ρ₀' trace' ρ'' ∧
      Rout ρ' ρ'' ∧ Rtrace_full trace trace' := by
    rcases hrun with hterm | ⟨label, hexit⟩
    · obtain ⟨ρ'', trace', hrun', hout, htr⟩ := hr.2.1 ρ' trace hterm
      exact ⟨ρ'', trace', .inl hrun', hout, htr⟩
    · obtain ⟨ρ'', trace', hrun', hout, htr⟩ := hr.2.2.1 label ρ' trace hexit
      exact ⟨ρ'', trace', .inr ⟨label, hrun'⟩, hout, htr⟩
  have hres := Strata.Logic.Hoare.TripleWith.run htriple ρ₀' ρ'' trace' hpre' hr.2.2.2 hrun'
  have ht := htgt ρ₀ ρ₀' ρ'' trace' hpre hR hpre' hrun'
  exact hpost_transport ρ₀ ρ' ρ'' trace hpre hinit hrun hout
    (hres.2 (hreach_transfer trace trace' hs ht htr hres.1 hreach))

/-- **Trace-overapproximation transport for `TripleWith` between related entries.**  Transports
    an event-trace Hoare triple `{Pre'} s' {Post'}` of the target `L₂` to a triple
    `{Pre} st {Post}` of the source `L₁` across an `OverapproximatesTraces2UptoWhen` with prefix
    trace relation `Rtrace`, run trace relation `Rtrace_full`, input relation `Rin` and output
    relation `Rout`: the target runs from an entry `ρ₀'` related to the source's by `Rin` that
    satisfies `Pre'`.  The validity of the target's assertions reflects to the source across
    `Rtrace`, and reachability transfers to the target across `Rtrace_full`.  These premises
    need only hold for source traces satisfying `Src`, a property of every finite execution of
    `st` from an entry satisfying `Pre` and the gate, and target traces satisfying `Tgt`, a
    property of every finite execution of `s'` from a related entry satisfying `Pre'`;
    `Post'` need only give `Post` of the final environments of completed source runs. -/
theorem overapproximatesTraces2UptoWhen_triple_of_sourceRuns
    (L₁ L₂ : EventLang P (Event P)) (I : ConditionInterp P) {Rtrace : Relation (Trace P)}
    (Rtrace_full : Relation (Trace P)) (Rin Rout : Relation (Env P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTraces2UptoWhen Rtrace Rtrace_full Rin Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post Pre' Post' : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre' s' Post')
    (hsource_pre : pre st)
    (Src Tgt : Trace P → Prop)
    (hsrc : ∀ ρ₀ cfg trace, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ →
      L₁.traceStar (L₁.stmtCfg st ρ₀) trace cfg → Src trace)
    (htgt : ∀ ρ₀ ρ₀' cfg' trace', Pre ρ₀ → Rin ρ₀ ρ₀' → Pre' ρ₀' →
      L₂.traceStar (L₂.stmtCfg s' ρ₀') trace' cfg' → Tgt trace')
    (hin : ∀ ρ₀, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ → ∃ ρ₀', Rin ρ₀ ρ₀' ∧ Pre' ρ₀')
    (hvalid_reflect : ∀ sourceTr targetTr, Src sourceTr → Tgt targetTr →
      Rtrace sourceTr targetTr →
      Trace.AssertionsValid P I targetTr → Trace.AssertionsValid P I sourceTr)
    (hreach_transfer : ∀ sourceTr targetTr, Src sourceTr → Tgt targetTr →
      Rtrace_full sourceTr targetTr → Trace.AssertionsValid P I targetTr →
      Trace.Reachable P I sourceTr → Trace.Reachable P I targetTr)
    (hpost_transport : ∀ ρ₀ ρ' ρ'' trace, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ →
      L₁.TerminatesAt st ρ₀ trace ρ' → Rout ρ' ρ'' → Post' ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post := by
  refine overapproximatesTraces2UptoWhen_triple_of_valid L₁ L₂ I Rtrace_full Rin Rout T pre
    params₁ params₂ st s' ht hsem htriple hsource_pre ?_ Src Tgt
    (fun ρ₀ ρ' trace hp hi hrun => by
      rcases hrun with h | ⟨_, h⟩ <;> exact hsrc ρ₀ _ trace hp hi h)
    (fun ρ₀ ρ₀' ρ'' trace' hp hR hp' hrun => by
      rcases hrun with h | ⟨_, h⟩ <;> exact htgt ρ₀ ρ₀' _ trace' hp hR hp' h)
    hin hreach_transfer hpost_transport
  intro ρ₀ cfg trace hpre hinit hrun
  obtain ⟨ρ₀', hR, hpre'⟩ := hin ρ₀ hpre hinit
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀' hR hinit
  obtain ⟨cfg', trace', hrun', hrel⟩ := hr.1 cfg trace hrun
  exact hvalid_reflect trace trace' (hsrc ρ₀ cfg trace hpre hinit hrun)
    (htgt ρ₀ ρ₀' cfg' trace' hpre hR hpre' hrun') hrel
    ((htriple ρ₀' hpre' hr.2.2.2).1 cfg' trace' hrun')

/-- **Trace-overapproximation transport for `TripleWith` across a prefix relation that reflects
    last assertions.**  As `overapproximatesTraces2UptoWhen_triple_of_sourceRuns`, for a prefix
    relation `Rtrace` that relates a source trace ending with an assertion only to target traces
    containing that assertion after assumptions implied by those before it
    (`Trace.ReflectsLastAssertion`), when the finite executions of `st` are closed under
    prefixes ending at an event (`hprefix`).  Each source occurrence is reflected through the
    finite execution ending at it. -/
theorem overapproximatesTraces2UptoWhen_triple_of_reflectsLastAssertion
    (L₁ L₂ : EventLang P (Event P)) (I : ConditionInterp P) {Rtrace : Relation (Trace P)}
    (hR : Trace.ReflectsLastAssertion I Rtrace)
    (Rtrace_full : Relation (Trace P)) (Rin Rout : Relation (Env P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTraces2UptoWhen Rtrace Rtrace_full Rin Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post Pre' Post' : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre' s' Post')
    (hsource_pre : pre st)
    (hprefix : ∀ ρ₀ cfg tr e post, L₁.traceStar (L₁.stmtCfg st ρ₀) (tr ++ e :: post) cfg →
      ∃ cfg', L₁.traceStar (L₁.stmtCfg st ρ₀) (tr ++ [e]) cfg')
    (hin : ∀ ρ₀, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ → ∃ ρ₀', Rin ρ₀ ρ₀' ∧ Pre' ρ₀')
    (hreach_transfer : ∀ sourceTr targetTr, Rtrace_full sourceTr targetTr →
      Trace.AssertionsValid P I targetTr →
      Trace.Reachable P I sourceTr → Trace.Reachable P I targetTr)
    (hpost_transport : ∀ ρ₀ ρ' ρ'' trace, Pre ρ₀ → L₁.initEnvWF params₁ st ρ₀ →
      L₁.TerminatesAt st ρ₀ trace ρ' → Rout ρ' ρ'' → Post' ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post := by
  refine overapproximatesTraces2UptoWhen_triple_of_valid L₁ L₂ I Rtrace_full Rin Rout T pre
    params₁ params₂ st s' ht hsem htriple hsource_pre ?_ (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) hin
    (fun s t _ _ => hreach_transfer s t) hpost_transport
  intro ρ₀ cfg trace hpre hinit htrace
  rw [Trace.AssertionsValid_iff_occurrences]
  intro tr c post htr w hw
  subst htr
  obtain ⟨ρ₀', hRin, hpre'⟩ := hin ρ₀ hpre hinit
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀' hRin hinit
  obtain ⟨cfg₁, h₁⟩ := hprefix ρ₀ cfg tr (.assert c) post htrace
  obtain ⟨cfg', trace', h', hrel⟩ := hr.1 cfg₁ _ h₁
  obtain ⟨tr', post', rfl, hassm⟩ := hR tr c trace' hrel
  have hv := (htriple ρ₀' hpre' hr.2.2.2).1 cfg' _ h'
  rw [Trace.AssertionsValid_iff_occurrences] at hv
  exact hv tr' c post' rfl w (hassm w hw)

/-- **General trace-overapproximation transport for `TripleWith`.**  Transports
    an event-trace Hoare triple from the target `L₂` back to the source `L₁`
    across an `OverapproximatesTraces2UptoWhen` with an *arbitrary* prefix trace relation
    `Rtrace`, run trace relation `Rtrace_full`, input-state relation `Rin` and output-state
    relation `Rout`.  The target runs from the source's initial environment, so `Rin` must
    relate every environment satisfying the precondition to itself.

    Target validity must reflect to the source across `Rtrace`; reachability need only
    transfer across `Rtrace_full` to a target run whose assertions are valid, as the target
    triple provides. -/
theorem overapproximatesTraces2UptoWhen_triple_general
    (L₁ L₂ : EventLang P (Event P)) (I : ConditionInterp P) {Rtrace : Relation (Trace P)}
    (Rtrace_full : Relation (Trace P)) (Rin Rout : Relation (Env P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTraces2UptoWhen Rtrace Rtrace_full Rin Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre s' Post)
    (hsource_pre : pre st)
    (hin : ∀ ρ₀, Pre ρ₀ → Rin ρ₀ ρ₀)
    (hvalid_reflect : ∀ sourceTr targetTr, Rtrace sourceTr targetTr →
      Trace.AssertionsValid P I targetTr → Trace.AssertionsValid P I sourceTr)
    (hreach_transfer : ∀ sourceTr targetTr, Rtrace_full sourceTr targetTr →
      Trace.AssertionsValid P I targetTr →
      Trace.Reachable P I sourceTr → Trace.Reachable P I targetTr)
    (hpost_transport : ∀ ρ' ρ'', Rout ρ' ρ'' → Post ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post :=
  overapproximatesTraces2UptoWhen_triple_of_sourceRuns L₁ L₂ I Rtrace_full Rin Rout T pre
    params₁ params₂ st s' ht hsem htriple hsource_pre (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun ρ₀ hp _ => ⟨ρ₀, hin ρ₀ hp, hp⟩)
    (fun s t _ _ => hvalid_reflect s t) (fun s t _ _ => hreach_transfer s t)
    (fun _ ρ' ρ'' _ _ _ _ hout hp => hpost_transport ρ' ρ'' hout hp)

/-- **General trace-overapproximation transport for `TripleWith`, one trace relation.**
    `overapproximatesTraces2UptoWhen_triple_general` for an `OverapproximatesTracesUptoWhen`
    with an *arbitrary* trace relation `Rtrace` and output-state relation `Rout`.  The input
    relation is fixed to equality, so source and target share the initial environment and
    precondition. -/
theorem overapproximatesTracesUptoWhen_triple_general
    (L₁ L₂ : EventLang P (Event P)) (I : ConditionInterp P)
    (Rtrace : Relation (Trace P)) (Rout : Relation (Env P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTracesUptoWhen Rtrace (· = ·) Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre s' Post)
    (hsource_pre : pre st)
    (hvalid_reflect : ∀ sourceTr targetTr, Rtrace sourceTr targetTr →
      Trace.AssertionsValid P I targetTr → Trace.AssertionsValid P I sourceTr)
    (hreach_transfer : ∀ sourceTr targetTr, Rtrace sourceTr targetTr →
      Trace.Reachable P I sourceTr → Trace.Reachable P I targetTr)
    (hpost_transport : ∀ ρ' ρ'', Rout ρ' ρ'' → Post ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post :=
  overapproximatesTraces2UptoWhen_triple_general L₁ L₂ I Rtrace (· = ·) Rout T pre
    params₁ params₂ st s' ht hsem htriple hsource_pre (fun _ _ => rfl) hvalid_reflect
    (fun s t h _ hr => hreach_transfer s t h hr) hpost_transport

/-- Precondition-bearing equality corollary: if `T` overapproximates traces when
    `pre` holds (trace relation equality) and `pre st` holds, then an event-trace
    Hoare triple on `T(st)` in `L₂` lifts to one on `st` in `L₁`. -/
theorem overapproximatesTracesWhen_triple (L₁ L₂ : EventLang P (Event P))
    (I : ConditionInterp P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTracesWhen (· = ·) L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre s' Post)
    (hsource_pre : pre st) :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post := by
  refine overapproximatesTracesUptoWhen_triple_general L₁ L₂ I
    (· = ·) (· = ·) T pre params₁ params₂ st s' ht hsem htriple hsource_pre
    ?_ ?_ ?_
  · intro _ _ h hv; subst h; exact hv
  · intro _ _ h hr; subst h; exact hr
  · intro _ _ h hp; subst h; exact hp

/-- If `T` overapproximates traces up to trace equality, a `TripleWith` on the
    translated statement transports back to the source statement. -/
theorem overapproximatesTraces_triple (L₁ L₂ : EventLang P (Event P))
    (I : ConditionInterp P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTraces (· = ·) L₁ L₂ T params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre s' Post) :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post :=
  overapproximatesTracesWhen_triple L₁ L₂ I T (fun _ => True) params₁ params₂
    st s' ht hsem htriple trivial

/-- Specialization of trace-overapproximation transport to `Trace.StuttersEnv`.
    `allowedFactory` records which captured factories may stutter. Stability
    handles paired events, while `htrue` handles true events under those
    factories that are inserted or removed by stuttering. -/
theorem overapproximatesTracesUptoWhen_triple_stuttersEnv [HasBool P]
    (L₁ L₂ : EventLang P (Event P)) (I : ConditionInterp P)
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop)
    (Rout : Relation (Env P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTracesUptoWhen
      (Trace.StuttersEnv allowedVarName allowedFactory) (· = ·) Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre s' Post)
    (hsource_pre : pre st)
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    (hpost_transport : ∀ ρ' ρ'', Rout ρ' ρ'' → Post ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post :=
  overapproximatesTracesUptoWhen_triple_general L₁ L₂ I
    (Trace.StuttersEnv allowedVarName allowedFactory) Rout T pre params₁ params₂ st s' ht hsem
    htriple hsource_pre
    (fun _ _ hrel hv =>
      Trace.StuttersEnv.assertionsValid_reflect hstable htrue hrel hv)
    (fun _ _ hrel hr =>
      Trace.StuttersEnv.reachable_transfer hstable htrue hrel hr)
    hpost_transport

end Transform

end Specification

end Imperative

end -- public section

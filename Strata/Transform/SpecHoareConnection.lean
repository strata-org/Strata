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
  postcondition;
- `triple_implies_assertValidOnTracesWhen` — a `Hoare.TripleWith`, together with
  initial-environment well-formedness and must-termination, implies
  per-identifier validity on every reachable trace.

A single `AssertValidOnTracesWhen` cannot imply `Hoare.TripleWith`, because the
triple requires every assertion in its terminating traces to be valid. Without
must-termination, the converse also fails: a partial-correctness triple does not
constrain intermediate prefixes of executions that never reach a terminal or
exiting configuration.

## Connection between `Hoare.TripleWith` and `OverapproximatesTracesUptoWhen`

`Strata.Logic.Hoare.TripleWith` is `EventLang`-generic, so a triple proved about
the target of a translation transports back to the source along a trace
overapproximation. The general transport supports an arbitrary trace relation
`Rtrace` and output-state relation `Rout`:

- `overapproximatesTracesUptoWhen_triple_general` transports a `TripleWith` across
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

## Specialization to `TraceStuttersEnv`

`overapproximatesTracesUptoWhen_triple_stuttersEnv` instantiates the general
theorem at `Rtrace := TraceStuttersEnv allowedVarName allowedFactory`. Because
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
    the trivial postcondition. `AllAssertsValidOnTracesWhen` covers every
    reachable configuration, so in particular it covers each terminal or
    exiting trace admitted by the triple. -/
theorem allAssertsValidOnTraces_implies_triple_valid
    (EL : EventLang P (Event P)) (I : ConditionInterp P)
    (params : EL.InitEnvWFParamsTy) (Pre : Env P → Prop) (s : EL.StmtT)
    (hvalid : AllAssertsValidOnTracesWhen EL I Pre s) :
    Strata.Logic.Hoare.TripleWith EL I params Pre s (fun _ => True) := by
  intro ρ₀ ρ' trace hpre _ hrun
  refine ⟨?_, fun _ => trivial⟩
  rcases hrun with hterm | ⟨label, hexit⟩
  · exact hvalid ρ₀ (EL.terminalCfg ρ') trace hpre hterm
  · exact hvalid ρ₀ (EL.exitingCfg label ρ') trace hpre hexit

/-- A `Hoare.TripleWith` yields per-identifier validity on every reachable
trace when all permitted initial environments are well-formed and every
execution from them must terminate. Must-termination extends each finite prefix
to a completed trace constrained by the triple. -/
theorem triple_implies_assertValidOnTracesWhen
    (EL : EventLang P (Event P)) (I : ConditionInterp P)
    (params : EL.InitEnvWFParamsTy) {Pre Post : Env P → Prop} {s : EL.StmtT}
    (htriple : Strata.Logic.Hoare.TripleWith EL I params Pre s Post)
    (hinit : ∀ ρ₀, Pre ρ₀ → EL.initEnvWF params s ρ₀)
    (hterminates : ∀ ρ₀, Pre ρ₀ → EL.Terminates s ρ₀)
    (aid : AssertId P) :
    AssertValidOnTracesWhen EL I Pre s aid := by
  intro ρ₀ cfg trace hpre hrun
  have hcfgTerm := (hterminates ρ₀ hpre).of_traceStar hrun
  obtain ⟨suffix, ρ', hfinal⟩ := hcfgTerm.reaches_final
  have hfull : EL.TerminatesAt s ρ₀ (trace ++ suffix) ρ' := by
    rcases hfinal with hterminal | ⟨label, hexiting⟩
    · exact .inl (ReflTransTrace.trans EL.step hrun hterminal)
    · exact .inr ⟨label, ReflTransTrace.trans EL.step hrun hexiting⟩
  have hvalid := (htriple ρ₀ ρ' (trace ++ suffix)
    hpre (hinit ρ₀ hpre) hfull).1
  exact Trace.AssertionValid.of_assertionsValid I aid
    (Trace.AssertionsValid.left_of_append I hvalid)

namespace Transform

variable {P : PureExpr}

/-- **General trace-overapproximation transport for `TripleWith`.**  Transports
    an event-trace Hoare triple from the target `L₂` back to the source `L₁`
    across an `OverapproximatesTracesUptoWhen` with an *arbitrary* trace relation
    `Rtrace` and output-state relation `Rout`.  The input relation is fixed to
    equality, so source and target share the initial environment and precondition.

    The terminal and exiting simulations may return a related target trace and
    final environment. The compatibility premises connect those witnesses to
    assertion validity, reachability, and the postcondition. -/
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
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀ rfl hinit
  rcases hrun with hterm | ⟨label, hexit⟩
  · obtain ⟨ρ'', trace', hrun', hout, htr⟩ := hr.2.1 ρ' trace hterm
    have hres := htriple ρ₀ ρ'' trace' hpre hr.2.2.2 (.inl hrun')
    exact ⟨hvalid_reflect trace trace' htr hres.1,
      fun hreach => hpost_transport ρ' ρ'' hout
        (hres.2 (hreach_transfer trace trace' htr hreach))⟩
  · obtain ⟨ρ'', trace', hrun', hout, htr⟩ := hr.2.2.1 label ρ' trace hexit
    have hres := htriple ρ₀ ρ'' trace' hpre hr.2.2.2 (.inr ⟨label, hrun'⟩)
    exact ⟨hvalid_reflect trace trace' htr hres.1,
      fun hreach => hpost_transport ρ' ρ'' hout
        (hres.2 (hreach_transfer trace trace' htr hreach))⟩

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

/-- Specialization of trace-overapproximation transport to `TraceStuttersEnv`.
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
      (TraceStuttersEnv allowedVarName allowedFactory) (· = ·) Rout
      L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.TripleWith L₂ I params₂ Pre s' Post)
    (hsource_pre : pre st)
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    (hpost_transport : ∀ ρ' ρ'', Rout ρ' ρ'' → Post ρ'' → Post ρ') :
    Strata.Logic.Hoare.TripleWith L₁ I params₁ Pre st Post :=
  overapproximatesTracesUptoWhen_triple_general L₁ L₂ I
    (TraceStuttersEnv allowedVarName allowedFactory) Rout T pre params₁ params₂ st s' ht hsem
    htriple hsource_pre
    (fun _ _ hrel hv =>
      TraceStuttersEnv.assertionsValid_reflect hstable htrue hrel hv)
    (fun _ _ hrel hr =>
      TraceStuttersEnv.reachable_transfer hstable htrue hrel hr)
    hpost_transport

end Transform

end Specification

end Imperative

end -- public section

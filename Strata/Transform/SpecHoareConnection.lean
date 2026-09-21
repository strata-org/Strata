/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.HoareTemplate
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

## Connection between `Hoare.Triple` and `OverapproximatesTraces`

`Strata.Logic.Hoare.Triple` is `EventLang`-generic, so a triple proved about the
*target* of a translation transports back to the source along a trace
overapproximation:

- `overapproximatesTraces_triple` — a trace overapproximation
  (`OverapproximatesTraces` at trace-relation equality) preserves
  `Hoare.Triple`.
- `overapproximatesTracesWhen_triple` — the same for
  `OverapproximatesTracesWhen`, under a precondition on the source statement.

Both are instantiated with the trace relation fixed to `(· = ·)`. Because both
the output-environment relation and the trace relation are equality, the
terminal/exiting simulation hands back the *same* environment and the *same*
trace it was given; substituting those equal witnesses turns the source run into
a target run over identical data, which the target triple discharges directly.
Assertion validity and the reachability-guarded postcondition then hold for the
source verbatim — there is nothing to re-derive about the trace.
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

variable {P : PureExpr} [HasBool P]

/-- If `T` overapproximates traces (up to trace equality) and an event-trace
    Hoare triple holds on `T(st)` in `L₂`, then the triple holds on `st` in `L₁`.

    The terminal/exiting trace simulations return the same environment and trace
    witnesses (both relations are `(· = ·)`), so substituting them recovers a
    target run over identical data for the target triple to discharge. -/
theorem overapproximatesTraces_triple (L₁ L₂ : EventLang P (Event P))
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTraces (· = ·) L₁ L₂ T params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.Triple L₂ params₂ Pre s' Post) :
    Strata.Logic.Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  have hr := hsem st s' ht trivial ρ₀ ρ₀ rfl hinit
  refine htriple ρ₀ ρ' trace hpre hr.2.2.2 ?_
  rcases hrun with hterm | ⟨label, hexit⟩
  · obtain ⟨ρ'', trace', hrun', hρeq, htreq⟩ := hr.2.1 ρ' trace hterm
    subst hρeq; subst htreq
    exact .inl hrun'
  · obtain ⟨ρ'', trace', hrun', hρeq, htreq⟩ := hr.2.2.1 label ρ' trace hexit
    subst hρeq; subst htreq
    exact .inr ⟨label, hrun'⟩

/-- Precondition-bearing corollary: if `T` overapproximates traces when `pre`
    holds and `pre st` is satisfied, then an event-trace Hoare triple on `T(st)`
    in `L₂` lifts to one on `st` in `L₁`.

    Generalizes `overapproximatesTraces_triple` to a nontrivial precondition (recover
    the latter with `pre := fun _ => True` and `hsource_pre := trivial`).  The
    transport is identical: equal environment and trace witnesses from the
    terminal/exiting simulations feed the target triple unchanged. -/
theorem overapproximatesTracesWhen_triple (L₁ L₂ : EventLang P (Event P))
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesTracesWhen (· = ·) L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.Triple L₂ params₂ Pre s' Post)
    (hsource_pre : pre st) :
    Strata.Logic.Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀ rfl hinit
  refine htriple ρ₀ ρ' trace hpre hr.2.2.2 ?_
  rcases hrun with hterm | ⟨label, hexit⟩
  · obtain ⟨ρ'', trace', hrun', hρeq, htreq⟩ := hr.2.1 ρ' trace hterm
    subst hρeq; subst htreq
    exact .inl hrun'
  · obtain ⟨ρ'', trace', hrun', hρeq, htreq⟩ := hr.2.2.1 label ρ' trace hexit
    subst hρeq; subst htreq
    exact .inr ⟨label, hrun'⟩

end Transform

end Specification

end Imperative

end -- public section

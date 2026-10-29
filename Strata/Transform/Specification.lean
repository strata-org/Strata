/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.Logic.LangDef
public import Strata.DL.Imperative.Logic.TraceInterp
public import Strata.Util.RelationsProps
public import Strata.DL.Imperative.Analysis.Definitions
public import Strata.DL.Imperative.Analysis.Assertions
import all Strata.DL.Imperative.CmdSemantics

/-! # Soundness Specification

All definitions are parametric over a `Lang P` structure that abstracts the
statement type, configuration type, step relation, and assert detection,
sharing the pure-expression parameter `P`.  `Strata.Logic.Lang` and its
Imperative constructors `Imperative.Logic.Lang.imperative` /
`Imperative.Logic.Lang.imperativeBlock` (with the latter's default condition
`Imperative.Logic.BlockInitEnvWF`) and the CFG constructor `Imperative.Logic.Lang.cfg`
are all defined in `Strata.DL.Imperative.Logic.LangDef`, which this module opens rather
than re-exporting from.

## Assertion validity and satisfiability

The predicates saying an assertion is valid or satisfiable, on configurations
or on event traces, are in `Strata.DL.Imperative.Analysis.Assertions`. The
Hoare-triple definitions and structural rules live in
`Strata.DL.Imperative.Logic.HoareTemplate`.

## Two ways to specify transformation soundness

There are two complementary ways to describe correctness of a transformation:

1. **`Sound`** directly preserves `AssertValidOnTracesWhen` for each assertion
   identifier between two `EventLang` values under a shared
   `ConditionInterp`.

2. **Operational overapproximation** simulates source behavior in the target.
   The `Overapproximates` family relates terminal/exiting states for `Lang`;
   `OverapproximatesTraces` additionally relates every finite trace prefix for
   `EventLang`.

Both styles are bilingual and can relate different source and target languages.
Trace overapproximation with equality traces also preserves `Hoare.TripleWith`
through `overapproximatesTraces_triple`, because the simulated target run has
the same trace and final environment as the source run.

## Key shared definitions for unstructured Imperative

- `Imperative.Logic.Lang.cfg` — the unstructured CFG `Lang P`, whose steps are
  `StepDetCFGStar`.
- `EnvStoreAgree` — an environment relation: store agreement on source-defined
  names, matching failure flags, preserved factory.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic Imperative.Logic

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P]

/-! ## Style B — Hoare logic

The Hoare-logic layer lives in `Strata.DL.Imperative.Logic.HoareTemplate` and does
not depend on this module.  Its language-agnostic `Strata.Logic.Hoare.TripleWith` is
stated over `EventLang`; the Imperative-specific `Imperative.Logic.Hoare` layer
supplies structural rules and `PostWF`.

`Strata.Transform.SpecHoareConnection` proves that
`OverapproximatesTraces(When)` with trace equality transports such a triple from
a transformed target back to its source. -/

namespace Transform

/-! ## Trace-based transformation overapproximation -/

/-- Trace-based overapproximation up to explicit trace and state relations.
It simulates every finite prefix (for safety properties) and terminal/exiting
runs (for partial-correctness postconditions). The definition is independent of
any particular trace property or condition interpretation. -/
@[expose] def OverapproximatesTracesUptoWhen
    {EventT : Type}
    (Rtrace : Relation (List EventT))
    (Rin Rout : Relation (Env P))
    (L₁ L₂ : EventLang P EventT) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' → pre st →
    ∀ (ρ₀ ρ₀' : Env P),
      Rin ρ₀ ρ₀' → L₁.initEnvWF params₁ st ρ₀ →
      -- Every finite source prefix has a related target trace prefix.
      (∀ cfg trace,
        L₁.traceStar (L₁.stmtCfg st ρ₀) trace cfg →
        ∃ cfg' trace',
          L₂.traceStar (L₂.stmtCfg st' ρ₀') trace' cfg' ∧
          Rtrace trace trace') ∧
      -- Terminal traces preserve outcome shape.
      (∀ ρ' trace,
        L₁.traceStar (L₁.stmtCfg st ρ₀) trace (L₁.terminalCfg ρ') →
        ∃ ρ'' trace',
          L₂.traceStar (L₂.stmtCfg st' ρ₀') trace' (L₂.terminalCfg ρ'') ∧
          Rout ρ' ρ'' ∧ Rtrace trace trace') ∧
      -- Exiting traces preserve the exit label and outcome shape.
      (∀ lbl ρ' trace,
        L₁.traceStar (L₁.stmtCfg st ρ₀) trace (L₁.exitingCfg lbl ρ') →
        ∃ ρ'' trace',
          L₂.traceStar (L₂.stmtCfg st' ρ₀') trace' (L₂.exitingCfg lbl ρ'') ∧
          Rout ρ' ρ'' ∧ Rtrace trace trace') ∧
      L₂.initEnvWF params₂ st' ρ₀'

/-- Equality-state trace overapproximation under a statement precondition. -/
@[expose] def OverapproximatesTracesWhen
    {EventT : Type}
    (Rtrace : Relation (List EventT))
    (L₁ L₂ : EventLang P EventT) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesTracesUptoWhen Rtrace (· = ·) (· = ·)
    L₁ L₂ T pre params₁ params₂

/-- Trace overapproximation with equality states and no statement restriction. -/
@[expose] def OverapproximatesTraces
    {EventT : Type}
    (Rtrace : Relation (List EventT))
    (L₁ L₂ : EventLang P EventT) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesTracesWhen Rtrace L₁ L₂ T (fun _ => True) params₁ params₂

/-- A transformation is *sound* when it preserves validity of each
assertion identifier. Source and target may use different event languages but
share one condition interpretation. -/
@[expose] def Sound (I : ConditionInterp P)
    (L₁ L₂ : EventLang P (Event P)) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (s : L₁.StmtT) (s' : L₂.StmtT) (a : AssertId P),
    T s = some s' →
    AssertValidOnTracesWhen L₂ I (L₂.initEnvWF params₂ s') s' a →
    AssertValidOnTracesWhen L₁ I (L₁.initEnvWF params₁ s) s a

/-! ## A family of Overapproximate predicates

`Overapproximates L₁ L₂ T params₁ params₂` says that
(1) any terminal or exiting env reachable from `st` in `L₁` is also reachable
    from `T st` in `L₂`,
(2) if there is a state reachable from `st` in `L₁` that fails an assertion,
    there also is a state reachable from `T st` in `L₂` that fails an assertion, and
(3) target-side well-formedness holds on the target initial env.

The precondition-bearing variant `OverapproximatesWhen`, the state-relation
variant `OverapproximatesUpto(When)`, and the assertion-failure-relaxed
`OverapproximatesAggressively(When)` provide progressively-more-general
formulations, each described below. -/

/-! ## Overapproximation up to a mapping relation of program states

`OverapproximatesUptoWhen Rin Rout` relates the source and target executions up
to two mapping relations: the initial environments are related by an **input**
relation `Rin`, and the final environments by a possibly different **output**
relation `Rout`.  It is the general member of the family — the one definition
that spells out the simulation triple.

`OverapproximatesUpto R` is the diagonal (`Rin = Rout = R`) specialization with
no precondition; `OverapproximatesWhen` (the same-environment version below)
further fixes `R = (· = ·)`. -/

/-- Overapproximation up to an **input** relation `Rin` between the two initial
    environments and a possibly different **output** relation `Rout` between the
    two final environments, under a precondition `pre`.  The most general member
    of the family and the one place the simulation triple is written; the
    diagonal `OverapproximatesUpto` and the equality-relation
    `OverapproximatesWhen`/`Overapproximates` below are all specializations of it.

    For every transformed pair `T st = some st'`, every source initial env `ρ₀`
    that is well-formed, and every target initial env `ρ₀'` related to it by
    `Rin`:
    1. every terminal (resp. exiting) env `ρ'` reachable from `st` in `L₁` has a
       target counterpart `ρ''` reachable from `st'` in `L₂`, related by `Rout`;
    2. failure is preserved (from `ρ₀` in `L₁` to `ρ₀'` in `L₂`);
    3. the target initial env `ρ₀'` is well-formed (`L₂.initEnvWF params₂`),
       so the guarantee can be threaded into a further transform.
-/
@[expose] public def OverapproximatesUptoWhen
    (Rin Rout : Relation (Env P))
    (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    pre st →
    ∀ (ρ₀ ρ₀' : Env P),
      Rin ρ₀ ρ₀' →
      L₁.initEnvWF params₁ st ρ₀ →
      -- Terminal/exiting envs have an `Rout`-related target counterpart.
      (∀ (ρ' : Env P),
        (L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
          ∃ ρ'', Rout ρ' ρ'' ∧ L₂.star (L₂.stmtCfg st' ρ₀') (L₂.terminalCfg ρ''))
        ∧
        (∀ lbl, L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
                ∃ ρ'', Rout ρ' ρ'' ∧ L₂.star (L₂.stmtCfg st' ρ₀') (L₂.exitingCfg lbl ρ'')))
      ∧
      -- Fail preservation.
      (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀')
      ∧
      -- Store WF preservation on the target side, with the target's parameters.
      L₂.initEnvWF params₂ st' ρ₀'

/-- Overapproximation up to a mapping relation `R`, with no precondition.  The
    diagonal (`Rin = Rout = R`) specialization of `OverapproximatesUptoWhen`. -/
@[expose] public def OverapproximatesUpto
    (R : Relation (Env P))
    (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesUptoWhen R R L₁ L₂ T (fun _ => True) params₁ params₂

/-- Overapproximation under a precondition `pre`: terminal/exiting envs
    reachable from the source are also reachable from the target, and failing
    programs are preserved.

    This is the special case of `OverapproximatesUptoWhen` where the state
    relation is equality — source and target run from the *same* initial env
    and reach the *same* final env. -/
@[expose] def OverapproximatesWhen (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesUptoWhen (· = ·) (· = ·) L₁ L₂ T pre params₁ params₂

/-- Overapproximation: `OverapproximatesWhen` with no precondition. -/
@[expose] def Overapproximates (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesWhen L₁ L₂ T (fun _ => True) params₁ params₂


/-! ## Aggressive overapproximation up to a mapping relation

`OverapproximatesAggressivelyUptoWhen Rin Rout` is the common generalization of
`OverapproximatesUptoWhen` (which carries an input/output relation split but
requires the target to reproduce every source terminal exactly) and the
equality-output aggressive relation `OverapproximatesAggressivelyWhen` defined
below (which permits the target to assert-fail spuriously but fixes
source = target initial env and equality of final envs).

Carrying both lets it specify a transform that simultaneously *prunes paths* and
*renames/generates variables*: pruning forces the aggressive `CanFail ∨ …`
disjunction (a source terminal may have no target counterpart, e.g. when an
inserted `assume` blocks the path), while surviving generated names force the
up-to output relation `Rout` (the target's final env agrees with the source's
only modulo those names).  A transform that only prunes — its fresh names never
reaching the final env — instantiates this at `Rout = (· = ·)`. -/

/-- Aggressive overapproximation up to an **input** relation `Rin` between the
    two initial environments and an **output** relation `Rout` between the final
    environments, under a precondition `pre`.

    For every transformed pair `T st = some st'`, source initial env `ρ₀`
    (well-formed) and `Rin`-related target initial env `ρ₀'`:
    1. for every terminal (resp. exiting) env `ρ'` reachable from `st` in `L₁`,
       *either* the target `CanFail`s, *or* — when `ρ'` is failure-free — some
       target env `ρ''` with `Rout ρ' ρ''` is reachable from `st'` in `L₂`;
    2. failure is preserved (`ρ₀`→`ρ₀'`);
    3. the target initial env `ρ₀'` is well-formed.

    Specializing `Rin = Rout = (· = ·)` recovers `OverapproximatesAggressivelyWhen`,
    which is *defined* as that specialization below. -/
@[expose] public def OverapproximatesAggressivelyUptoWhen
    (Rin Rout : Relation (Env P))
    (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    pre st →
    ∀ (ρ₀ ρ₀' : Env P),
      Rin ρ₀ ρ₀' →
      L₁.initEnvWF params₁ st ρ₀ →
      -- Terminal case: CanFail, or a Rout-related target terminal.
      (∀ ρ', L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
        CanFail L₂ st' ρ₀' ∨
        (ρ'.hasFailure = false →
          ∃ ρ'', Rout ρ' ρ'' ∧ L₂.star (L₂.stmtCfg st' ρ₀') (L₂.terminalCfg ρ'')))
      ∧
      -- Exiting case.
      (∀ lbl ρ', L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
        CanFail L₂ st' ρ₀' ∨
        (ρ'.hasFailure = false →
          ∃ ρ'', Rout ρ' ρ'' ∧ L₂.star (L₂.stmtCfg st' ρ₀') (L₂.exitingCfg lbl ρ'')))
      ∧
      -- Fail preservation (source ρ₀ → target ρ₀').
      (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀')
      ∧
      -- Target-side WF.
      L₂.initEnvWF params₂ st' ρ₀'

/-- Aggressive overapproximation up to a single mapping relation `R`, no
    precondition: the diagonal `Rin = Rout = R` specialization. -/
@[expose] public def OverapproximatesAggressivelyUpto
    (R : Relation (Env P))
    (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesAggressivelyUptoWhen R R L₁ L₂ T (fun _ => True) params₁ params₂

/-! ## Aggressive overapproximation

`OverapproximatesAggressively` relaxes `Overapproximates`: the target may
terminate with `hasFailure = true` instead of matching the source's
terminal/exiting env exactly.  -/

/-- Aggressive overapproximation under a precondition `pre`: the target program
    can assert-fail spuriously.  This is the diagonal `Rin = Rout = (· = ·)`
    specialization of `OverapproximatesAggressivelyUptoWhen` — the target shares
    the source's initial env and reproduces its final env exactly (modulo the
    trivial relation), while still permitting spurious assert failures. -/
@[expose] public def OverapproximatesAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesAggressivelyUptoWhen (· = ·) (· = ·) L₁ L₂ T pre params₁ params₂

/-- Aggressive overapproximation: `OverapproximatesAggressivelyWhen` with no
    precondition. -/
@[expose] public def OverapproximatesAggressively (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesAggressivelyWhen L₁ L₂ T (fun _ => True) params₁ params₂

/-! ## Underapproximation

`Underapproximates` is the dual of `Overapproximates`.  Where an
overapproximation guarantees the target reproduces *at least* the source's
behaviours (source ⊆ target), an underapproximation guarantees the target
exhibits *at most* them (target ⊆ source)
-/

@[expose] public def Underapproximates (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    ∀ (ρ₀ : Env P),
      L₂.initEnvWF params₂ st' ρ₀ →
      -- Terminal/exiting envs reachable by the target are reachable by the source.
      (∀ (ρ' : Env P),
        (L₂.star (L₂.stmtCfg st' ρ₀) (L₂.terminalCfg ρ') →
          L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ'))
        ∧
        (∀ lbl, L₂.star (L₂.stmtCfg st' ρ₀) (L₂.exitingCfg lbl ρ') →
                L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ')))
      ∧
      -- Fail reflection (target → source).
      (CanFail L₂ st' ρ₀ → CanFail L₁ st ρ₀)
      ∧
      -- Source-side WF.
      L₁.initEnvWF params₁ st ρ₀

/-! ## Semantic equivalence -/

/-- Semantic equivalence of a transform: `T` both over- and under-approximates.
    The source `st` and target `st'` reach exactly the same terminal/exiting envs and
    fail on exactly the same initial states. -/
@[expose] public def SemanticallyEquivalent (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  Overapproximates L₁ L₂ T params₁ params₂ ∧ Underapproximates L₁ L₂ T params₁ params₂

/-- The output relation shared by the structured-pass overapproximation
instances: the target environment's store agrees with the source's on every
source-defined name, and the failure flags match. `nondetElim`,
`hoistLoopPrefixInits`/`stmtsToCFG`, and the whole pipeline all overapproximate
up to this same relation. -/
@[expose] def EnvStoreAgree {P : PureExpr} (ρ₀ ρ₀' : Env P) : Prop :=
  StoreAgreement ρ₀.store ρ₀'.store
  ∧ ρ₀.hasFailure = ρ₀'.hasFailure

end Transform

end Specification
end Imperative

end -- public section

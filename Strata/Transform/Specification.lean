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

All definitions are parametric over `EventLang P EventT` structures that
abstract the statement type, configuration type, and event-emitting step
relation, sharing the pure-expression parameter `P`.  `Strata.Logic.EventLang`
and its Imperative constructors `Imperative.Logic.EventLang.imperativeE` /
`Imperative.Logic.EventLang.imperativeBlockE` / `Imperative.Logic.EventLang.cfgE`
are all defined in `Strata.DL.Imperative.Logic.LangDef`, which this module opens
rather than re-exporting from.

## Assertion validity and satisfiability

The predicates saying an assertion is valid or satisfiable on event traces are
in `Strata.DL.Imperative.Analysis.Assertions`. The Hoare-triple definitions and
structural rules live in `Strata.DL.Imperative.Logic.HoareTemplate`.

## Two ways to specify transformation soundness

There are two complementary ways to describe correctness of a transformation:

1. **`Sound`** directly preserves `AssertValidOnTracesWhen` for each assertion
   identifier between two `EventLang` values under a shared
   `ConditionInterp`.

2. **Operational overapproximation** simulates source behavior in the target.
   `OverapproximatesTraces` relates every finite trace prefix and every
   terminal/exiting run.

Both styles are bilingual and can relate different source and target languages.
Trace overapproximation with equality traces also preserves `Hoare.TripleWith`
through `overapproximatesTraces_triple`, because the simulated target run has
the same trace and final environment as the source run.

## Key shared definitions

- `EnvStoreAgree` — an environment relation: store agreement on source-defined
  names.
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
    {EventT : Type _}
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
    {EventT : Type _}
    (Rtrace : Relation (List EventT))
    (L₁ L₂ : EventLang P EventT) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesTracesUptoWhen Rtrace (· = ·) (· = ·)
    L₁ L₂ T pre params₁ params₂

/-- Trace overapproximation with equality states and no statement restriction. -/
@[expose] def OverapproximatesTraces
    {EventT : Type _}
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

/-- The output relation shared by the structured-pass overapproximation
instances: the target environment's store agrees with the source's on every
source-defined name. `nondetElim`,
`hoistLoopPrefixInits`/`stmtsToCFG`, and the whole pipeline all overapproximate
up to this same relation. -/
@[expose] def EnvStoreAgree {P : PureExpr} (ρ₀ ρ₀' : Env P) : Prop :=
  StoreAgreement ρ₀.store ρ₀'.store

end Transform

end Specification
end Imperative

end -- public section

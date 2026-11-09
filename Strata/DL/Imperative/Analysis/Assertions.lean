/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.Logic.LangDef
public import Strata.DL.Imperative.Logic.TraceInterp
public import Strata.DL.Imperative.Analysis.Definitions

/-! # Assertion validity and satisfiability

An `assert label expr` command is valid when its expression holds at every
relevant occurrence, and satisfiable when it holds at some occurrence. A
`...When` predicate restricts the initial environments considered through a
precondition `Pre`; its unqualified counterpart uses `fun _ => True`.

This module provides two related formulations:

1. **Event-trace predicates.** `AssertValidOnTracesWhen` requires every matching
   assertion occurrence in every reachable finite trace to hold under its
   preceding assumptions. `AssertSatisfiableOnTracesWhen` existentially selects
   a reachable trace and a matching occurrence whose condition and preceding
   assumptions hold in one shared `ConditionInterp` world. Their
   `AssertValidOnTraces` and `AssertSatisfiableOnTraces` variants remove the
   initial-state restriction; `AllAssertsValidOnTracesWhen` /
   `AllAssertsValidOnTraces` cover whole-trace validity.

2. **`Hoare.TripleWith`.** A partial-correctness triple `{Pre} s {Post}` requires
   every terminating or exiting `EventLang` run to emit an assertion-valid
   trace, and requires `Post` whenever that trace is `Trace.Reachable`.
   Conditions are interpreted by a supplied `ConditionInterp P`.

The Hoare-triple definitions and structural rules live in
`Strata.DL.Imperative.Logic.HoareTemplate`. A triple validates completed traces;
`AllAssertsValidOnTracesWhen` quantifies over every finite prefix, so the two
notions are intentionally distinct without an additional progress or extension
hypothesis.

It also defines `Analysis.ValidOnTracesVerifier`, a verifier that passes only
statements whose traces have every assertion valid.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic Imperative.Logic

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P]

/-! ## Event-trace assertion validity

These trace-native definitions inspect every finite event trace produced by
`EventLang.traceStar`.
-/

/-- Every occurrence of assertion `a` in every reachable finite event trace is
valid under the assumptions preceding that occurrence. -/
@[expose] def AssertValidOnTracesWhen
    (EL : EventLang P (Event P))
    (I : ConditionInterp P)
    (Pre : Env P → Prop) (s : EL.StmtT) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : EL.CfgT) (trace : Trace P),
    Pre ρ₀ →
    EL.traceStar (EL.stmtCfg s ρ₀) trace cfg →
    Trace.AssertionValid P I a trace

/-- Every assertion event in every reachable finite trace is valid. -/
@[expose] def AllAssertsValidOnTracesWhen
    (EL : EventLang P (Event P))
    (I : ConditionInterp P)
    (Pre : Env P → Prop) (s : EL.StmtT) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : EL.CfgT) (trace : Trace P),
    Pre ρ₀ →
    EL.traceStar (EL.stmtCfg s ρ₀) trace cfg →
    Trace.AssertionsValid P I trace

/-- Assertion `a` is satisfiable on traces under `Pre` when some permitted
initial environment produces a finite trace containing a matching assertion
occurrence satisfiable with its preceding assumptions. -/
@[expose] def AssertSatisfiableOnTracesWhen
    (EL : EventLang P (Event P))
    (I : ConditionInterp P)
    (Pre : Env P → Prop) (s : EL.StmtT) (a : AssertId P) : Prop :=
  ∃ (ρ₀ : Env P) (cfg : EL.CfgT) (trace : Trace P),
    Pre ρ₀ ∧
    EL.traceStar (EL.stmtCfg s ρ₀) trace cfg ∧
    Trace.AssertionSatisfiable P I a trace

/-- Trace-native assertion validity with no initial-state restriction. -/
@[expose] def AssertValidOnTraces
    (EL : EventLang P (Event P))
    (I : ConditionInterp P) (s : EL.StmtT) (a : AssertId P) : Prop :=
  AssertValidOnTracesWhen EL I (fun _ => True) s a

/-- Trace-native validity of all assertions with no initial-state restriction. -/
@[expose] def AllAssertsValidOnTraces
    (EL : EventLang P (Event P))
    (I : ConditionInterp P) (s : EL.StmtT) : Prop :=
  AllAssertsValidOnTracesWhen EL I (fun _ => True) s

/-- Trace-native assertion satisfiability with no initial-state restriction. -/
@[expose] def AssertSatisfiableOnTraces
    (EL : EventLang P (Event P))
    (I : ConditionInterp P) (s : EL.StmtT) (a : AssertId P) : Prop :=
  AssertSatisfiableOnTracesWhen EL I (fun _ => True) s a

/-! ## Verifiers on event traces -/

namespace Analysis

/-- `analyze` is a sound verifier for `EL` on event traces, from the entry
    environments `wf` admits: in every finite trace of a statement it passes,
    every assertion is valid under `I`. -/
@[expose] def ValidOnTracesVerifier (EL : EventLang P (Event P)) (I : ConditionInterp P)
    (wf : EL.StmtT → Env P → Prop) (analyze : EL.StmtT → Bool) : Prop :=
  ∀ s, analyze s = true → AllAssertsValidOnTracesWhen EL I (wf s) s

end Analysis

end Specification
end Imperative

end -- public section

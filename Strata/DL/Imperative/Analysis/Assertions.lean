/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.Logic.LangDef
public import Strata.DL.Imperative.Logic.TraceInterp

/-! # Assertion validity and satisfiability

An `assert label expr` command is valid when its expression holds at every
relevant occurrence, and satisfiable when it holds at some occurrence. A
`...When` predicate restricts the initial environments considered through a
precondition `Pre`; its unqualified counterpart uses `fun _ => True`.

This module provides three related formulations:

1. **Configuration-head predicates.** `AssertValidWhen` checks every reachable
   configuration identified by `isAtAssert`, while `AssertSatisfiableWhen`
   existentially selects one such configuration where `P.eval` returns true.
   `AssertValid` and `AssertSatisfiable` remove the initial-state restriction;
   `AllAssertsValidWhen` / `AllAssertsValid` quantify validity over assertion
   identifiers.

2. **Event-trace predicates.** `AssertValidOnTracesWhen` requires every matching
   assertion occurrence in every reachable finite trace to hold under its
   preceding assumptions. `AssertSatisfiableOnTracesWhen` existentially selects
   a reachable trace and a matching occurrence whose condition and preceding
   assumptions hold in one shared `ConditionInterp` world. Their
   `AssertValidOnTraces` and `AssertSatisfiableOnTraces` variants remove the
   initial-state restriction; `AllAssertsValidOnTracesWhen` /
   `AllAssertsValidOnTraces` cover whole-trace validity.

3. **`Hoare.TripleWith`.** A partial-correctness triple `{Pre} s {Post}` requires
   every terminating or exiting `EventLang` run to emit an assertion-valid
   trace, and requires `Post` whenever that trace is `Trace.Reachable`.
   Conditions are interpreted by a supplied `ConditionInterp P`.

The Hoare-triple definitions and structural rules live in
`Strata.DL.Imperative.Logic.HoareTemplate`. A triple validates completed traces;
`AllAssertsValidOnTracesWhen` quantifies over every finite prefix, so the two
notions are intentionally distinct without an additional progress or extension
hypothesis.

On the failure-flag semantics, `Transform.CanFail` says a run of a statement
reaches a configuration whose failure flag is raised.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic Imperative.Logic

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P]
variable (L : Lang P)


/-! ## Style A — Reachability-based assertion validity and satisfiability -/

/-- Assert `a` is *valid* in statement `s` when `Pre` holds on the initial
    environment. -/
@[expose] def AssertValidWhen (Pre : Env P → Prop) (s : L.StmtT) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : L.CfgT),
    Pre ρ₀ →
    L.star (L.stmtCfg s ρ₀) cfg →
    L.isAtAssert cfg a →
    P.eval (L.getEnv cfg).factory (L.getEnv cfg).store a.expr = some HasBool.tt

/-- All asserts are valid in statement `s` when `Pre` holds. -/
def AllAssertsValidWhen (Pre : Env P → Prop) (s : L.StmtT) : Prop :=
  ∀ (a : AssertId P), AssertValidWhen L Pre s a

/-- Assert `a` is *valid* in statement `s` (for all initial environments). -/
@[expose] def AssertValid (s : L.StmtT) (a : AssertId P) : Prop :=
  AssertValidWhen L (fun _ => True) s a

/-- All asserts are valid in statement `s`. -/
@[expose] def AllAssertsValid (s : L.StmtT) : Prop :=
  ∀ (a : AssertId P), AssertValid L s a

/-- Assert `a` is *satisfiable* in statement `s` under `Pre`: there exists some
    initial environment satisfying `Pre` and some reachable configuration where
    the assert is about to execute and evaluates to `true`. -/
@[expose] def AssertSatisfiableWhen (Pre : Env P → Prop) (s : L.StmtT) (a : AssertId P) : Prop :=
  ∃ (ρ₀ : Env P) (cfg : L.CfgT),
    Pre ρ₀ ∧
    L.star (L.stmtCfg s ρ₀) cfg ∧
    L.isAtAssert cfg a ∧
    P.eval (L.getEnv cfg).factory (L.getEnv cfg).store a.expr = some HasBool.tt

/-- Assert `a` is *satisfiable* in statement `s` (for some initial environment). -/
@[expose] def AssertSatisfiable (s : L.StmtT) (a : AssertId P) : Prop :=
  AssertSatisfiableWhen L (fun _ => True) s a


/-! ### Event-trace assertion validity

These trace-native definitions inspect every finite event trace produced by
`EventLang.traceStar`. They coexist with the configuration-head formulation so
existing users of `Lang` and failure-flag semantics remain unchanged.
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



/-! ## Assertion failure on the failure-flag semantics -/

namespace Transform

/-- After steps from `s`, some reachable configuration has `hasFailure = true`.
    The configuration doesn't have to be terminal or exiting. -/
@[expose] public def CanFail (L : Lang P) (s : L.StmtT) (ρ₀ : Env P) : Prop :=
  ∃ cfg, (L.getEnv cfg).hasFailure = true ∧ L.star (L.stmtCfg s ρ₀) cfg

/-- `CanFail` specialized to a list of imperative statements (a block body).
    There exists a reachable config from `(.stmts ss ρ₀)` whose env has
    `hasFailure = true`. -/
@[expose] public def CanFailBlock
    {CmdT : Type} (evalCmd : EvalCmdParam P CmdT)
    (ss : List (Stmt P CmdT)) (ρ₀ : Env P) : Prop :=
  ∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
    StepStmtStar P evalCmd (.stmts ss ρ₀) cfg

end Transform

end Specification
end Imperative

end -- public section

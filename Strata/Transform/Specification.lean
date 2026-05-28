/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.CmdSemantics

/-! # Soundness Specification

All definitions are parametric over a `Lang P` structure that abstracts the
statement type, configuration type, step relation, and assert detection,
sharing the pure-expression parameter `P`.

## Two definitions of assertion validity

An `assert label expr` command is *valid* when its expression evaluates to
true in every reachable configuration where the assert is about to execute.
The primary predicate is **`AssertValidWhen Pre s a`**, which restricts
attention to initial environments satisfying `Pre`.  `AssertValid` is the
special case `AssertValidWhen (fun _ => True)`.

This module provides two equivalent formulations:

1. **`AssertValidWhen` / `AssertValid` (reachability-based)** — for every
   initial environment `ρ₀` (satisfying `Pre`) and every configuration `cfg`
   reachable from `s`, if `cfg` is at the assert (detected by `isAtAssert`),
   then `(cfg.getEnv).eval (cfg.getEnv).store a.expr = some HasBool.tt`.  This is a
   direct, semantic definition: walk the execution graph and check each
   assert site.

2. **`Hoare.Triple` (Hoare-triple-based)** — a partial-correctness triple
   `{Pre} s {Post}` holds when, for every `ρ₀` satisfying `Pre` with a
   well-formed evaluator and no prior failure, if `s` terminates at `ρ'`
   then `Post ρ'` holds and `hasFailure` is still false.  Since assert
   failure is recorded in `hasFailure`, the postcondition
   `ρ'.hasFailure = false` captures that all asserts passed.

The two are shown equivalent by `hoareTriple_implies_assertValid` and
`allAssertsValid_implies_hoareTriple`. Their precise relation is slightly
subtle, and `Hoare.Triple`'s doc string has more info.

## Two ways to specify transformation soundness

There are two predicates for describing the correctness of a program
transformation `T : L₁.StmtT → Option L₂.StmtT`:

1. **`Sound`** — directly states that `T` preserves assertion validity:
   if every assert is valid in the transformed program (`AssertValid L₂`),
   then every assert is valid in the original (`AssertValid L₁`).

2. **`Overapproximates`** — states that the set of reachable terminal/exiting
   environments in the source is a subset of those reachable in the target.
   This is a semantic simulation condition.

Both predicates are *bilingual*: they relate two (possibly different) `Lang P`
values, so they can express cross-language transformations such as
deterministic-to-nondeterministic.

It is proven that both specifications imply assertion validity of the input
program:
- `Sound` does so directly by definition (`sound_assertValid`, `sound_allAsserts`).
- `Overapproximates` does so via Hoare triples: `overapproximates_triple` shows
  that overapproximation preserves `Hoare.Triple`, which is connected to
  assertion validity by `hoareTriple_implies_assertValid` (a `Triple` implies
  `AssertValidWhen InitEnvWF` for the postcondition assert) and
  `allAssertsValid_implies_hoareTriple` (the converse direction).
-/

public section

namespace Imperative

namespace Specification

/-! ## Language bundle -/

/-- Bundles the abstract ingredients for small-step statement semantics,
    parameterized by a shared pure-expression system `P`. -/
structure Lang (P : PureExpr) where
  /-- Statement type. -/
  StmtT : Type
  /-- Configuration type. -/
  CfgT : Type
  /-- Multi-step relation. -/
  star : CfgT → CfgT → Prop
  /-- Embed a single statement and env into a config. -/
  stmtCfg : StmtT → Env P → CfgT
  /-- Terminal configuration. -/
  terminalCfg : Env P → CfgT
  /-- Exiting configuration. -/
  exitingCfg : String → Env P → CfgT
  /-- Assert detection in configurations. -/
  isAtAssert : CfgT → AssertId P → Prop
  /-- Extract env from a configuration. -/
  getEnv : CfgT → Env P
  /-- The type of parameters threaded into `initEnvWF`.
      The Core language uses a record bundling reserved
      "fresh-prefixes" and a `declaredFuncs` predicate (see
      `Core.Specification.InitEnvWFParams`). -/
  InitEnvWFParamsTy : Type
  /-- Initial environment well-formedness: The language-specific well-formedness
      parameters are passed via `InitEnvWFParamsTy`. -/
  initEnvWF : InitEnvWFParamsTy → StmtT → Env P → Prop

/-- Generic initial-environment well-formedness for the imperative layer. -/
structure InitEnvWF {P : PureExpr} [HasBool P] [HasBoolOps P] [HasVal P] [HasFvar P]
    (ρ : Env P) : Prop where
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfVal  : WellFormedSemanticEvalVal ρ.eval
  wfVar  : WellFormedSemanticEvalVar ρ.eval

/-- Build a `Lang` from `Imperative.Stmt`/`Config` with a given command
    type and evaluator.

    `ParamsTy` is the `InitEnvWFParamsTy` for the resulting language; it defaults
    to `Unit` (no parameters), in which case `initEnvWF` defaults to the generic
    `InitEnvWF`.  The Core language overrides both. -/
abbrev Lang.imperative (P : PureExpr) [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P]
    (CmdT : Type) (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (isAtAssert : Config P CmdT → AssertId P → Prop)
    (ParamsTy : Type := Unit)
    (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop :=
      fun _ _ ρ => InitEnvWF ρ) :
    Lang P :=
  ⟨Stmt P CmdT, Config P CmdT, StepStmtStar P evalCmd extendEval,
   .stmt, .terminal, .exiting, isAtAssert, Config.getEnv, ParamsTy, initEnvWF⟩

/-- The standard `Lang` for `Cmd P` / `EvalCmd P` / `isAtAssert`. -/
abbrev Lang.standard (P : PureExpr) [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P]
    (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (Imperative.isAtAssert P)


variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P]
variable (L : Lang P)


/-! ## Style A — Reachability-based assertion validity and satisfiability.

The primary predicate is `AssertValidWhen`, parameterized by a precondition
on the initial environment.  `AssertValid` is `AssertValidWhen (fun _ => True)`.
`AllAssertsValidWhen` / `AllAssertsValid` universally quantify over assert ids. -/

/-- Assert `a` is *valid* in statement `s` when `Pre` holds on the initial
    environment.  This is the general form; `AssertValid` is the special case
    with `Pre = fun _ => True`. -/
@[expose] def AssertValidWhen (Pre : Env P → Prop) (s : L.StmtT) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : L.CfgT),
    Pre ρ₀ →
    L.star (L.stmtCfg s ρ₀) cfg →
    L.isAtAssert cfg a →
    (L.getEnv cfg).eval (L.getEnv cfg).store a.expr = some HasBool.tt

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
    the assert is about to execute and evaluates to `true`.

    This is the existential dual of `AssertValidWhen` and is the natural
    target for bug-finding modes: the analyzer is trying to demonstrate that
    *some* execution actually reaches the assert with a passing expression
    (i.e., the assert is not vacuously unreachable). -/
@[expose] def AssertSatisfiableWhen (Pre : Env P → Prop) (s : L.StmtT) (a : AssertId P) : Prop :=
  ∃ (ρ₀ : Env P) (cfg : L.CfgT),
    Pre ρ₀ ∧
    L.star (L.stmtCfg s ρ₀) cfg ∧
    L.isAtAssert cfg a ∧
    (L.getEnv cfg).eval (L.getEnv cfg).store a.expr = some HasBool.tt

/-- Assert `a` is *satisfiable* in statement `s` (for some initial environment). -/
@[expose] def AssertSatisfiable (s : L.StmtT) (a : AssertId P) : Prop :=
  AssertSatisfiableWhen L (fun _ => True) s a


/-! ## Style B — Hoare-triple assertion validity

**Usage note:** When building Hoare-logic proofs for a transformation, use
`Triple` (not `TripleBlock`). `Triple` is the top-level specification that
connects to `AssertValid` via `hoareTriple_implies_assertValid` /
`assertValid_implies_hoareTriple`. `TripleBlock` is an internal helper for
reasoning about statement-list bodies inside blocks — it accounts for exiting
configurations that the enclosing block may catch. Structural rules like
`seq_cons` produce `TripleBlock` results, which are then lifted back to
`Triple` via `TripleBlock.toTriple` when wrapping in a block. -/

namespace Hoare

/-- Partial-correctness Hoare triple.

    `AllAssertsValid` is strictly stronger than `Triple`.
    For example, `{True} (assert false; loop_forever) {anything}` triple holds
    vacuously whereas `AllAssertsValid` does not hold due to the first `assert`.

    Note that for this reason `hoareTriple_implies_assertValid` therefore relates
    `Triple` only to the *postcondition* assertion in a `PredicatedStmt`,
    not to assertions inside the body, whereas `allAssertsValid_implies_hoareTriple`
    relates all asserts in the `PredicatedStmt` to `Triple`.

    TODO: We will want to define Triple for total correctness. It will be useful
    when proving preservation of termination after program transformation.
-/
@[expose] def Triple
    (params : L.InitEnvWFParamsTy)
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → L.initEnvWF params s ρ₀ → ρ₀.hasFailure = false →
    L.star (L.stmtCfg s ρ₀) (L.terminalCfg ρ') →
    Post ρ' ∧ ρ'.hasFailure = false


/-! ## Structural Hoare rules (Imperative-specific) -/

section StmtRules

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

/-- Partial-correctness Hoare triple for a block body.
    The output configuration is allowed to be still in an exiting mode
    (see Config.exiting) because the outer block can catch the exit. -/
@[expose] def TripleBlock
    {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (Pre : Env P → Prop) (ss : List (Stmt P CmdT)) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → InitEnvWF ρ₀ → ρ₀.hasFailure = false →
    (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') ∨
     ∃ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ')) →
    Post ρ' ∧ ρ'.hasFailure = false

omit [HasVal P] in
/-- A postcondition is well-formed if it is stable under `projectStore` and
    `eval`-replacement by any parent eval that the inner `ρ.eval` extends. -/
def PostWF (Post : Env P → Prop) : Prop :=
  ∀ ρ σ_parent e_parent,
    EvalExtensionOf extendEval e_parent ρ.eval →
    Post ρ → ρ.hasFailure = false →
    Post { ρ with store := projectStore σ_parent ρ.store, eval := e_parent } ∧
      ({ ρ with store := projectStore σ_parent ρ.store, eval := e_parent } : Env P).hasFailure = false

end StmtRules


/-! ## Definitions for connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasBool P'] [HasBoolOps P'] [HasFvars P']
variable (extendEval : ExtendEval P')

/-- The composite statement `assume pre; st; assert post` wrapped in a block. -/
@[expose] def PredicatedStmt
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P') : Stmt P' (Cmd P') :=
  .block block_label
    [.cmd (.assume pre_label pre_expr pre_md), st, .cmd (.assert post_label post_expr post_md)]
    block_md

end StandardConnection

end Hoare


namespace Transform

/-- A transformation is *sound* if it preserves assertion validity.
    Bilingual: source and target may live in different languages. -/
@[expose] def Sound (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT) : Prop :=
  ∀ (s : L₁.StmtT) (s' : L₂.StmtT) (a : AssertId P),
    T s = some s' → AssertValid L₂ s' a → AssertValid L₁ s a

/-! ## Overapproximate predicate family

`Overapproximates L₁ L₂ T` says that
(1) any terminal or exiting env reachable from `st` in `L₁` is also reachable
from `T st` in `L₂`, and
(2) if there is a state reachable from `st` in `L₁` that fails an assertion,
there also is a state  reachable from `T st` in `L₂` that fails an assertion.

There are more generic predicates such as `OverapproximatesWhen`,
`OverapproximatesUpto`, `OverapproximatesUptoWhen` and
`OverapproximatesAggressivelyWhen`, each of which will be described below. -/

/-- After steps from s, it reaches to a configuration whose hasFailure is
    true. Doesn't have to be terminalCfg or exitingCfg. -/
@[expose] public def CanFail (L : Lang P) (s : L.StmtT) (ρ₀ : Env P) : Prop :=
  ∃ cfg, (L.getEnv cfg).hasFailure = true ∧ L.star (L.stmtCfg s ρ₀) cfg

/-- `CanFail` specialized to a list of imperative statements (a block body).
    There exists a reachable config from `(.stmts ss ρ₀)` whose env has
    `hasFailure = true`. -/
@[expose] public def CanFailBlock
    {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (ss : List (Stmt P CmdT)) (ρ₀ : Env P) : Prop :=
  ∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
    StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) cfg

/-! ## Overapproximation up to a relation on states

`OverapproximatesUptoWhen R` relates the source and target executions up to a
single state relation `R`: initial environments are related by `R` and final
environments by `R`.  This is useful for transformations that
rename/restructure the state.

`OverapproximatesWhen` (the same-environment version below) is the special case
`R = (· = ·)`. -/

/-- Overapproximation up to a state relation `R`, under a precondition `pre`.

    For every transformed pair `T st = some st'`, every source initial env `ρ₀`
    that is well-formed, and every target initial env `ρ₀'` related to it by `R`:
    1. every terminal (resp. exiting) env `ρ'` reachable from `st` in `L₁` has a
       target counterpart `ρ''` reachable from `st'` in `L₂`, related by `R`;
    2. failure is preserved (from `ρ₀` in `L₁` to `ρ₀'` in `L₂`);
    3. the target initial env `ρ₀'` is well-formed (`L₂.initEnvWF params₂`),
       so the guarantee can be threaded into a further transform.

    `R` is used on both the input (as a hypothesis) and the output (under an
    existential). -/
@[expose] public def OverapproximatesUptoWhen
    (R : Relation (Env P))
    (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    pre st →
    ∀ (ρ₀ ρ₀' : Env P),
      R ρ₀ ρ₀' →
      L₁.initEnvWF params₁ st ρ₀ →
      -- Terminal/exiting envs have an `R`-related target counterpart.
      (∀ (ρ' : Env P),
        (L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
          ∃ ρ'', R ρ' ρ'' ∧ L₂.star (L₂.stmtCfg st' ρ₀') (L₂.terminalCfg ρ''))
        ∧
        (∀ lbl, L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
                ∃ ρ'', R ρ' ρ'' ∧ L₂.star (L₂.stmtCfg st' ρ₀') (L₂.exitingCfg lbl ρ'')))
      ∧
      -- Fail preservation.
      (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀')
      ∧
      -- Store WF preservation on the target side, with the target's parameters.
      L₂.initEnvWF params₂ st' ρ₀'

/-- Overapproximation up to a relation `R`, with no precondition. -/
@[expose] public def OverapproximatesUpto
    (R : Relation (Env P))
    (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesUptoWhen R L₁ L₂ T (fun _ => True) params₁ params₂

/-- Overapproximation under a precondition `pre`: terminal/exiting envs
    reachable from the source are also reachable from the target, and failing
    programs are preserved.

    This is the special case of `OverapproximatesUptoWhen` where the state
    relation is equality — source and target run from the *same* initial env
    and reach the *same* final env. -/
@[expose] def OverapproximatesWhen (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesUptoWhen (· = ·) L₁ L₂ T pre params₁ params₂

/-- Overapproximation: `OverapproximatesWhen` with no precondition. -/
@[expose] def Overapproximates (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesWhen L₁ L₂ T (fun _ => True) params₁ params₂

/-! ## Aggressive overapproximation

`OverapproximatesAggressively` relaxes `Overapproximates`: the target may
terminate with `hasFailure = true` instead of matching the source's
terminal/exiting env exactly.  -/

/-- Aggressive overapproximation under a precondition `pre`: the target program
    can assert-fail spuriously. -/
@[expose] public def OverapproximatesAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    pre st →
    ∀ (ρ₀ : Env P),
      L₁.initEnvWF params₁ st ρ₀ →
      -- Terminal case
      (∀ ρ', L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
        CanFail L₂ st' ρ₀ ∨
        (ρ'.hasFailure = false →
          L₂.star (L₂.stmtCfg st' ρ₀) (L₂.terminalCfg ρ')))
      ∧
      -- Exiting case
      (∀ lbl ρ', L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
        CanFail L₂ st' ρ₀ ∨
        (ρ'.hasFailure = false →
          L₂.star (L₂.stmtCfg st' ρ₀) (L₂.exitingCfg lbl ρ')))
      ∧
      -- Fail preservation, but does not exactly track the counterexample.
      (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀)
      ∧
      -- Store WF preservation on the target side, with the target's parameters.
      L₂.initEnvWF params₂ st' ρ₀

/-- Aggressive overapproximation: `OverapproximatesAggressivelyWhen` with no
    precondition. -/
@[expose] public def OverapproximatesAggressively (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) : Prop :=
  OverapproximatesAggressivelyWhen L₁ L₂ T (fun _ => True) params₁ params₂

/-! ## Statement-list overapproximation (Imperative-specific)

Uses `Overapproximates L L T` (single-language): the proof decomposes
seq execution into terminal/exiting outcomes of individual statements,
which is exactly what `Overapproximates` provides. -/

section ImperativeStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

/-- `Lang` for block-level (statement-list) overapproximation.
    `StmtT` is `List (Stmt P CmdT)` and `stmtCfg` embeds via `.stmts`. -/
abbrev Lang.imperativeBlock : Lang P where
  StmtT := List (Stmt P CmdT)
  CfgT := Config P CmdT
  star := StepStmtStar P evalCmd extendEval
  stmtCfg := .stmts
  terminalCfg := .terminal
  exitingCfg := .exiting
  isAtAssert := isAtAssertFn
  getEnv := Config.getEnv
  InitEnvWFParamsTy := Unit
  initEnvWF := fun _ _ ρ => InitEnvWF ρ

end ImperativeStmts

end Transform



/-! ## Analysis -/

/-- An `Analysis` over programs `ℙ` producing diagnostics `D`.
    `ℙ` is written double-struck (\bbP) to avoid clashing with the
    pure-expression parameter `P` used elsewhere in this file. -/
structure Analysis (ℙ D : Type) where
  /-- The property we want every program to satisfy. -/
  desirableProperty : ℙ → Prop
  /-- The analysis function: produce a diagnostic from a program. -/
  analyze : ℙ → D
  /-- Whether a diagnostic is considered passing. -/
  pass : D → Prop

namespace Analysis

variable {ℙ D : Type}

/-- An analysis is *sound* when a passing diagnostic implies the desirable
    property holds of the analyzed program. -/
def Sound (a : Analysis ℙ D) : Prop :=
  ∀ (p : ℙ) (d : D), a.analyze p = d ∧ a.pass d → a.desirableProperty p

/-- An analysis is *complete* when every program with the desirable property
    yields a passing diagnostic. -/
def Complete (a : Analysis ℙ D) : Prop :=
  ∀ (p : ℙ) (d : D), a.analyze p = d ∧ a.desirableProperty p → a.pass d


/-- An analysis whose desirable property is `AssertValid L s a` for a fixed
    language `L` and assertion `a`. -/
def AssertValidityChecker
    {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasVal P]
    {D : Type} (L : Lang P) (a : AssertId P)
    (analyze : L.StmtT → D) (pass : D → Prop) :
    Analysis L.StmtT D :=
  { desirableProperty := fun s => AssertValid L s a
    analyze := analyze
    pass := pass }

/-- An analysis whose desirable property is `AssertSatisfiable L s a` for a
    fixed language `L` and assertion `a`. The dual of `AssertValidityChecker`:
    a passing diagnostic witnesses that *some* execution reaches the assert
    with a passing expression (the natural target for bug-finding analyses). -/
def AssertSatisfiabilityChecker
    {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasVal P]
    {D : Type} (L : Lang P) (a : AssertId P)
    (analyze : L.StmtT → D) (pass : D → Prop) :
    Analysis L.StmtT D :=
  { desirableProperty := fun s => AssertSatisfiable L s a
    analyze := analyze
    pass := pass }

end Analysis

end Specification
end Imperative

end -- public section

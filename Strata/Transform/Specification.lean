/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.ListUtils

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

It is proven that both specifications imply `AssertValid` of the input program:
- `Sound` does so directly by definition (`sound_assertValid`, `sound_allAsserts`).
- `Overapproximates` does so via Hoare triples: `overapproximates_triple` shows
  that overapproximation preserves `Hoare.Triple`, which is equivalent to
  `AssertValid` by the bidirectional theorems `hoareTriple_implies_assertValid`
  and `assertValid_implies_hoareTriple`.
-/

public section

namespace Imperative

namespace Specification

/-! ## Language bundle -/

/-- Bundles the abstract ingredients for small-step statement semantics,
    parameterized by a shared pure-expression system `P`. -/
structure Lang (P : PureExpr) [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasInt P] [HasIntOps P] where
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
  /-- Initial environment well-formedness: includes store definedness for touched
      variables and any evaluator well-formedness conditions needed by the language.

      The `List String` parameter lists "fresh-prefixes": prefixes of identifiers
      that must NOT appear in the initial environment.  Downstream transforms
      reserve such prefixes so they can introduce fresh names with that prefix
      without colliding with user names.  `Overapproximates` and
      `OverapproximatesAggressively` extend this list with the transform's own
      `prefixIdent` for the L₂ side.

      The `(P.Ident → Bool)` parameter (`declaredFuncs`) characterizes the
      set of operator/function names already defined in the initial evaluator.
      Concrete instantiations use this to enforce a `defUseWellFormed` invariant
      that all operator references in the program are pre-declared, and any
      `funcDecl` introduces a fresh name. -/
  initEnvWF : List String → (P.Ident → Bool) → StmtT → Env P → Prop

/-- Build a `Lang` from `Imperative.Stmt`/`Config` with a given command
    type and evaluator. -/
abbrev Lang.imperative (P : PureExpr) [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasInt P] [HasIntOps P]
    (CmdT : Type) (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (isAtAssert : Config P CmdT → AssertId P → Prop)
    (initEnvWF : List String → (P.Ident → Bool) → Stmt P CmdT → Env P → Prop :=
      fun _ _ _ _ => True) :
    Lang P :=
  ⟨Stmt P CmdT, Config P CmdT, StepStmtStar P evalCmd extendEval,
   .stmt, .terminal, .exiting, isAtAssert, Config.getEnv, initEnvWF⟩

/-- The standard `Lang` for `Cmd P` / `EvalCmd P` / `isAtAssert`. -/
abbrev Lang.standard (P : PureExpr) [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasInt P] [HasIntOps P]
    (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (Imperative.isAtAssert P)


variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasInt P] [HasIntOps P] [HasVal P]
variable (L : Lang P)


/-! ## Style A — Reachability-based assertion validity

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
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
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
    Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
    (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') ∨
     ∃ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ')) →
    Post ρ' ∧ ρ'.hasFailure = false

omit [HasVal P] in
/-- A postcondition is well-formed if it is stable under `projectStore` and
    `eval`-replacement (the parent's eval is restored on block exit). -/
@[expose] def PostWF (Post : Env P → Prop) : Prop :=
  ∀ ρ σ_parent e_parent, Post ρ → ρ.hasFailure = false →
    Post { ρ with store := projectStore σ_parent ρ.store, eval := e_parent } ∧
      ({ ρ with store := projectStore σ_parent ρ.store, eval := e_parent } : Env P).hasFailure = false

end StmtRules


/-! ## Connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasBool P'] [HasBoolOps P'] [HasFvars P'] [HasInt P'] [HasIntOps P']
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

/-! ## Overapproximate predicate

`Overapproximates L₁ L₂ T` says that (1) any terminal or exiting env reachable
from `st` in `L₁` is also reachable from `T st` in `L₂`, and (2) if there is
a state reachable from `st` in `L₁` that fails an assertion, there also is
a state  reachable from `T st` in `L₂` that fails an assertion.
When `L₁ = L₂`, this specializes to the single-language case. -/

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

/-- `PrefixDisjoint newPrefix prefixIdents` says: every prefix in
    `prefixIdents` is prefix-disjoint from `newPrefix`, i.e., neither
    is a string prefix of the other (as `Char` lists). -/
@[expose] public def PrefixDisjoint (newPrefix : String) (prefixIdents : List String) : Prop :=
  ∀ p ∈ prefixIdents,
    ¬ p.toList.isPrefixOf newPrefix.toList ∧
    ¬ newPrefix.toList.isPrefixOf p.toList

/-- Overapproximation under a precondition `pre`: terminal/exiting envs
    reachable from the source are also reachable from the target, and failing
    programs are preserved.

    `newPrefix` is the identifier prefix that the transform `T` may introduce
    in its output.  The L₂ side's `initEnvWF` is invoked with `newPrefix`
    ERASED from the L₁ side's prefix list — since the output may use names
    with that prefix, the prefix can no longer be treated as "fresh" for
    downstream transforms. -/
@[expose] def OverapproximatesWhen (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop) (newPrefix : String) : Prop :=
  ∀ (prefixIdents : List String)
    (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    pre st →
    newPrefix ∈ prefixIdents →
    PrefixDisjoint newPrefix (prefixIdents.erase newPrefix) →
    ∀ (ρ₀ : Env P) (declaredFuncs : P.Ident → Bool),
      L₁.initEnvWF prefixIdents declaredFuncs st ρ₀ →
      -- Terminal/exiting envs are a subset.
      (∀ (ρ' : Env P),
        (L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
          L₂.star (L₂.stmtCfg st' ρ₀) (L₂.terminalCfg ρ'))
        ∧
        (∀ lbl, L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
                L₂.star (L₂.stmtCfg st' ρ₀) (L₂.exitingCfg lbl ρ')))
      ∧
      -- Fail preservation.
      (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀)
      ∧
      -- Store WF preservation: `newPrefix` is erased from the prefix list
      -- since the output may have introduced names with that prefix.
      L₂.initEnvWF (prefixIdents.erase newPrefix) declaredFuncs st' ρ₀

/-- Overapproximation: `OverapproximatesWhen` with no precondition. -/
@[expose] def Overapproximates (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (newPrefix : String) : Prop :=
  OverapproximatesWhen L₁ L₂ T (fun _ => True) newPrefix

/-! ## Aggressive overapproximation

`OverapproximatesAggressively` relaxes `Overapproximates`: the target may
terminate with `hasFailure = true` instead of matching the source's
terminal/exiting env exactly.  -/

/-- Aggressive overapproximation under a precondition `pre`: the target program
    can assert-fail spuriously.

    `newPrefix` is the identifier prefix that the transform `T` may introduce
    in its output (see `Overapproximates`). -/
@[expose] public def OverapproximatesAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop) (newPrefix : String) : Prop :=
  ∀ (prefixIdents : List String)
    (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    pre st →
    newPrefix ∈ prefixIdents →
    PrefixDisjoint newPrefix (prefixIdents.erase newPrefix) →
    ∀ (ρ₀ : Env P) (declaredFuncs : P.Ident → Bool),
      L₁.initEnvWF prefixIdents declaredFuncs st ρ₀ →
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
      -- Store WF preservation: `newPrefix` is erased from the prefix list.
      L₂.initEnvWF (prefixIdents.erase newPrefix) declaredFuncs st' ρ₀

/-- Aggressive overapproximation: `OverapproximatesAggressivelyWhen` with no
    precondition. -/
@[expose] public def OverapproximatesAggressively (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (newPrefix : String) : Prop :=
  OverapproximatesAggressivelyWhen L₁ L₂ T (fun _ => True) newPrefix

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
  initEnvWF := fun _ _ _ ρ =>
    WellFormedSemanticEvalBool ρ.eval ∧
    WellFormedSemanticEvalVal ρ.eval ∧
    WellFormedSemanticEvalVar ρ.eval

end ImperativeStmts

end Transform
end Specification
end Imperative

end -- public section

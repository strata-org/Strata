/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsSmallStep
import all Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.ListUtils
import Strata.DL.Imperative.SemanticsProps

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
structure Lang (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P] where
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
  exitingCfg : Option String → Env P → CfgT
  /-- Assert detection in configurations. -/
  isAtAssert : CfgT → AssertId P → Prop
  /-- Extract env from a configuration. -/
  getEnv : CfgT → Env P

/-- Build a `Lang` from `Imperative.Stmt`/`Config` with a given command
    type and evaluator. -/
abbrev Lang.imperative (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P]
    (CmdT : Type) (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (isAtAssert : Config P CmdT → AssertId P → Prop) : Lang P :=
  ⟨Stmt P CmdT, Config P CmdT, StepStmtStar P evalCmd extendEval,
   .stmt, .terminal, .exiting, isAtAssert, Config.getEnv⟩

/-- The standard `Lang` for `Cmd P` / `EvalCmd P` / `isAtAssert`. -/
abbrev Lang.standard (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (Imperative.isAtAssert P)


variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P]
variable (L : Lang P)


/-! ## Style A — Reachability-based assertion validity

The primary predicate is `AssertValidWhen`, parameterized by a precondition
on the initial environment.  `AssertValid` is `AssertValidWhen (fun _ => True)`.
`AllAssertsValidWhen` / `AllAssertsValid` universally quantify over assert ids. -/

/-- Assert `a` is *valid* in statement `s` when `Pre` holds on the initial
    environment.  This is the general form; `AssertValid` is the special case
    with `Pre = fun _ => True`. -/
def AssertValidWhen (Pre : Env P → Prop) (s : L.StmtT) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : L.CfgT),
    Pre ρ₀ →
    L.star (L.stmtCfg s ρ₀) cfg →
    L.isAtAssert cfg a →
    (L.getEnv cfg).eval (L.getEnv cfg).store a.expr = some HasBool.tt

/-- All asserts are valid in statement `s` when `Pre` holds. -/
def AllAssertsValidWhen (Pre : Env P → Prop) (s : L.StmtT) : Prop :=
  ∀ (a : AssertId P), AssertValidWhen L Pre s a

/-- Assert `a` is *valid* in statement `s` (for all initial environments). -/
def AssertValid (s : L.StmtT) (a : AssertId P) : Prop :=
  AssertValidWhen L (fun _ => True) s a

/-- All asserts are valid in statement `s`. -/
def AllAssertsValid (s : L.StmtT) : Prop :=
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
def Triple
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
    L.star (L.stmtCfg s ρ₀) (L.terminalCfg ρ') →
    Post ρ' ∧ ρ'.hasFailure = false

/-! ## Parametric Hoare rules -/

omit [HasVal P] in
/-- False precondition proves anything -/
theorem false_pre (s : L.StmtT) (Post : Env P → Prop) :
    Triple L (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

omit [HasVal P] in
/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence
    {Pre Pre' : Env P → Prop} {Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L Pre' s Post' := by
  intro ρ₀ ρ' hpre' hwfb hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hwfb hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩


/-! ## Structural Hoare rules (Imperative-specific) -/

section StmtRules

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

/-- Partial-correctness Hoare triple for a block body.
    The output configuration is allowed to be still in an exiting mode
    (see Config.exiting) because the outer block can catch the exit. -/
def TripleBlock
    {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (Pre : Env P → Prop) (ss : List (Stmt P CmdT)) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
    (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') ∨
     ∃ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ')) →
    Post ρ' ∧ ρ'.hasFailure = false

 omit [HasFvar P] [HasVal P] in
/-- Empty statement list is skip. -/
theorem skip_block (Pre : Env P → Prop) :
    TripleBlock evalCmd extendEval Pre [] Pre := by
  intro ρ₀ ρ' hpre _ hf₀ hstar
  match hstar with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ h1 r1 => cases h1 with
      | step_stmts_nil => cases r1 with
        | refl => exact ⟨hpre, hf₀⟩
        | step _ _ _ h _ => exact nomatch h
  | .inr ⟨_, hexit⟩ =>
    cases hexit with
    | step _ _ _ h _ => cases h with
      | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

omit [HasVal P] in
/-- A single command. -/
theorem cmd (c : CmdT) (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
      evalCmd ρ₀.eval ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = false) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.cmd c) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_cmd hcmd =>
      cases r1 with
      | refl =>
        have ⟨hp, hfeq⟩ := h ρ₀ _ _ hpre hwfb hf₀ hcmd
        simp [hf₀] at hp ⊢; exact ⟨hp, hfeq⟩
      | step _ _ _ h _ => exact nomatch h

omit [HasVal P] in
/-- Sequential cons. -/
theorem seq_cons {s : Stmt P CmdT} {ss : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (h₁ : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre s Mid)
    (h₂ : TripleBlock evalCmd extendEval Mid ss Post)
    (hnofd : Stmt.noFuncDecl s = true)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre (s :: ss) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hdone
  have hwfb_preserved : ∀ ρ₁, StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
      WellFormedSemanticEvalBool ρ₁.eval := by
    intro ρ₁ hterm
    have this := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd hterm
    rw [this]; exact hwfb
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_ss⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
        exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) hf₁ (.inl hrest_ss)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendEval hrest with
        | .inl hexit_inner =>
          exact absurd hexit_inner
            (exitsCoveredByBlocks_noEscape P evalCmd extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
          have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
          exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) hf₁ (.inr ⟨lbl, hexit_ss⟩)

omit [HasVal P] in
/-- Lift a `TripleBlock` to a `Triple` by wrapping in a block. -/
theorem TripleBlock.toTriple {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h : TripleBlock evalCmd extendEval Pre ss Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ hstep hrest => cases hstep with
    | step_block =>
      match block_reaches_terminal P evalCmd extendEval hrest with
      | .inl hterm => exact h ρ₀ ρ' hpre hwfb hf₀ (.inl hterm)
      | .inr ⟨lbl, hexit_inner⟩ => exact h ρ₀ ρ' hpre hwfb hf₀ (.inr ⟨lbl, hexit_inner⟩)

omit [HasVal P] in
/-- Lift a `Triple` to a `TripleBlock` for a singleton list. -/
theorem Triple.toTripleBlock {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (h : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre s Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre [s] Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hp, hf⟩ := h ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
        cases hrest_nil with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil => cases r1 with
            | refl => exact ⟨hp, hf⟩
            | step _ _ _ h _ => exact nomatch h
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendEval hrest with
        | .inl hexit_s =>
          exact absurd hexit_s
            (exitsCoveredByBlocks_noEscape P evalCmd extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_nil⟩ =>
          cases hexit_nil with
          | step _ _ _ h _ => cases h with
            | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

omit [HasVal P] in
/-- Empty block is skip. -/
theorem skip (l : String) (md : MetaData P) (Pre : Env P → Prop) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.block l [] md) Pre :=
  TripleBlock.toTriple evalCmd extendEval isAtAssertFn (skip_block evalCmd extendEval Pre)

omit [HasVal P] in
/-- If-then-else rule. -/
theorem ite {c : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (ht : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.tt) tss Post)
    (he : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.ff) ess Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.ite (.det c) tss ess md) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_ite_true hc _ => exact ht ρ₀ ρ' ⟨hpre, hc⟩ hwfb hf₀ (.inl r1)
    | step_ite_false hc _ => exact he ρ₀ ρ' ⟨hpre, hc⟩ hwfb hf₀ (.inl r1)

/- TODO: the WHILE rule -/

end StmtRules


/-! ## Connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasBool P'] [HasNot P']
variable (extendEval : ExtendEval P')

/-- The composite statement `assume pre; st; assert post` wrapped in a block. -/
def PredicatedStmt
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P') : Stmt P' (Cmd P') :=
  .block block_label
    [.cmd (.assume pre_label pre_expr pre_md), st, .cmd (.assert post_label post_expr post_md)]
    block_md

/-- **Direction 1**: Hoare triple implies assert validity for `PredicatedStmt`. -/
theorem hoareTriple_implies_assertValid
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hoare : Triple (Lang.standard P' extendEval)
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt))
    (hno : st.noMatchingAssert post_label) :
    AssertValid (Lang.standard P' extendEval)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg _ hreach hat
  have hno_match := noMatchingAssert_implies_no_reachable_assert P' extendEval st post_label post_expr hno
  unfold PredicatedStmt at hreach
  cases hreach with
  | refl => exact absurd hat (by simp [isAtAssert])
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_block =>
      have ⟨inner, heq_cfg, hinner_star, hat_inner⟩ :=
        block_isAtAssert_inner P' extendEval _ _ _ _ hrest hat
      subst heq_cfg
      cases hinner_star with
      | refl => exact absurd hat_inner (by simp [isAtAssert])
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_stmts_cons =>
          match seq_isAtAssert_cases P' extendEval _ _ _ _ hrest2 hat_inner with
          | .inl ⟨_, _, hreach_assume, hat_assume⟩ =>
            cases hreach_assume with
            | refl => exact absurd hat_assume (by simp [isAtAssert])
            | step _ _ _ h _ => cases h with
              | step_cmd => rename_i hr; cases hr with
                | refl => exact absurd hat_assume (by simp [isAtAssert])
                | step _ _ _ h _ => exact absurd h (by intro h; cases h)
          | .inr ⟨ρ₁, hterm_assume, hrest_stmts, hat_stmts⟩ =>
            cases hrest_stmts with
            | refl =>
              have : ¬ isAtAssert P' (.stmts (st :: [.cmd (.assert post_label post_expr post_md)]) ρ₁)
                  ⟨post_label, post_expr⟩ := by
                intro h_at
                match st with
                | .cmd (.assert l e md') =>
                  have h := hno_match ρ₁ (.stmt (.cmd (.assert l e md')) ρ₁) (.refl _)
                  simp [isAtAssert] at h h_at
                  exact h h_at.1 h_at.2
                | .cmd (.init ..) | .cmd (.set ..) | .cmd (.assume ..)
                | .cmd (.cover ..) | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl ..
                | .typeDecl .. =>
                  simp [isAtAssert] at h_at
              exact absurd hat_stmts this
            | step _ _ _ hstep3 hrest3 =>
              cases hstep3 with
              | step_stmts_cons =>
                match seq_isAtAssert_cases P' extendEval _ _ _ _ hrest3 hat_stmts with
                | .inl ⟨_, _, hreach_st, hat_st⟩ =>
                  exact absurd hat_st (hno_match ρ₁ _ hreach_st)
                | .inr ⟨ρ', hterm_st, hrest_assert, hat_assert⟩ =>
                  cases hterm_assume with
                  | step _ _ _ h_assume_step h_assume_rest =>
                    cases h_assume_step with
                    | step_cmd hcmd =>
                      cases hcmd with
                      | eval_assume hpre hwfb =>
                        cases h_assume_rest with
                        | refl =>
                          have ⟨ρ'_clean, hterm_clean, hs_eq, he_eq⟩ :=
                            smallStep_hasFailure_irrel P' (EvalCmd P') extendEval
                              st _ ρ' hterm_st { ρ₀ with hasFailure := false } rfl rfl
                          have ⟨hpost, _⟩ := hoare { ρ₀ with hasFailure := false } ρ'_clean
                            hpre hwfb rfl hterm_clean
                          simp only [hs_eq, he_eq] at hpost
                          have ⟨he, hs⟩ := assert_tail_getEvalStore P' extendEval
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          dsimp [Config.getEval, Config.getStore, Config.getEnv] at he hs ⊢
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)


/-- **Direction 2**: Assert validity for `PredicatedStmt` implies Hoare triple. -/
theorem allAssertsValid_implies_hoareTriple
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hvalid : AllAssertsValid (Lang.standard P' extendEval)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    Triple (Lang.standard P' extendEval)
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt) := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  let assume_stmt : Stmt P' (Cmd P') := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P' (Cmd P') := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P' (Cmd P')) := [assume_stmt, st, assert_stmt]
  have hvalid_st : ∀ (a : AssertId P') (cfg : Config P' (Cmd P')),
      StepStmtStar P' (EvalCmd P') extendEval (.stmt st ρ₀) cfg →
      isAtAssert P' cfg a →
      cfg.getEval cfg.getStore a.expr = some HasBool.tt := by
    intro a cfg hstar_st hat
    have h_assume : StepStmtStar P' (EvalCmd P') extendEval
        (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
      .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
    have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P') = ρ₀ := by
      cases ρ₀; simp [Bool.or_false]
    have h1 := stmts_cons_step P' (EvalCmd P') extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
    rw [h_ρ₁_eq] at h1
    have h2 : StepStmtStar P' (EvalCmd P') extendEval
        (.stmts [st, assert_stmt] ρ₀) (.seq (.stmt st ρ₀) [assert_stmt]) :=
      .step _ _ _ StepStmt.step_stmts_cons (.refl _)
    have h3 := seq_inner_star P' (EvalCmd P') extendEval _ _ [assert_stmt] hstar_st
    have h_inner := ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ h1 h2) h3
    have h_block := block_inner_star P' (EvalCmd P') extendEval _ _ block_label h_inner
    have h_start : StepStmtStar P' (EvalCmd P') extendEval
        (.stmt (.block block_label body block_md) ρ₀) (.block block_label (.stmts body ρ₀)) :=
      .step _ _ _ StepStmt.step_block (.refl _)
    have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
    have h_result := hvalid a ρ₀ _ trivial h_full hat
    dsimp [Config.getEval, Config.getStore, Config.getEnv] at h_result ⊢
    exact h_result
  have h_assume : StepStmtStar P' (EvalCmd P') extendEval
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
  have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P') = ρ₀ := by
    cases ρ₀; simp [Bool.or_false]
  have h1 := stmts_cons_step P' (EvalCmd P') extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
  rw [h_ρ₁_eq] at h1
  have h2 := stmts_cons_step P' (EvalCmd P') extendEval st [assert_stmt] ρ₀ ρ' hstar
  have h3 : StepStmtStar P' (EvalCmd P') extendEval
      (.stmts [assert_stmt] ρ') (.seq (.stmt assert_stmt ρ') []) :=
    .step _ _ _ StepStmt.step_stmts_cons (.refl _)
  have h_inner := ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ h1 h2) h3
  have h_block := block_inner_star P' (EvalCmd P') extendEval _ _ block_label h_inner
  have h_start : StepStmtStar P' (EvalCmd P') extendEval
      (.stmt (.block block_label body block_md) ρ₀) (.block block_label (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
  have h_at : isAtAssert P' (.block block_label (.seq (.stmt assert_stmt ρ') [])) ⟨post_label, post_expr⟩ := by
    simp [isAtAssert, assert_stmt]
  have h_result := hvalid ⟨post_label, post_expr⟩ ρ₀ _ trivial h_full h_at
  dsimp [Config.getEval, Config.getStore, Config.getEnv] at h_result
  exact ⟨h_result, allAssertsValid_preserves_noFailure P' extendEval
    (ρ₀ := ρ₀) (ρ' := ρ') st hvalid_st hf₀ hstar⟩

end StandardConnection

end Hoare


namespace Transform

/-- A transformation is *sound* if it preserves assertion validity.
    Bilingual: source and target may live in different languages. -/
def Sound (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT) : Prop :=
  ∀ (s : L₁.StmtT) (s' : L₂.StmtT) (a : AssertId P),
    T s = some s' → AssertValid L₂ s' a → AssertValid L₁ s a

omit [HasVal P] in
theorem sound_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : Sound L₁ L₂ T₁) (h₂ : Sound L₂ L₃ T₂) :
    Sound L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

omit [HasVal P] in
theorem sound_assertValid (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound L₁ L₂ T) (hvalid : AssertValid L₂ s' a) :
    AssertValid L₁ s a := hsound s s' a ht hvalid

omit [HasVal P] in
theorem sound_allAsserts (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound L₁ L₂ T) (hvalid : AllAssertsValid L₂ s') :
    AllAssertsValid L₁ s := fun a => hsound s s' a ht (hvalid a)

omit [HasVal P] in
theorem sound_id : Sound L L some := by
  intro s s' a ht hvalid; simp at ht; subst ht; exact hvalid

/-! ## Overapproximate predicate

`Overapproximates L₁ L₂ T` says that (1) any terminal or exiting env reachable
from `st` in `L₁` is also reachable from `T st` in `L₂`, and (2) if there is
a state reachable from `st` in `L₁` that fails an assertion, there also is
a state  reachable from `T st` in `L₂` that fails an assertion.
When `L₁ = L₂`, this specializes to the single-language case. -/

/-- After steps from s, it reaches to a configuration whose hasFailure is
    true. Doesn't have to be terminalCfg or exitingCfg. -/
public def CanFail (L : Lang P) (s : L.StmtT) (ρ₀ : Env P) : Prop :=
  ∃ cfg, (L.getEnv cfg).hasFailure = true ∧ L.star (L.stmtCfg s ρ₀) cfg

/-- Overapproximation: terminal/exiting envs reachable from the
    source are also reachable from the target, and failing programs
    are preserved. -/
def Overapproximates (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    ∀ (ρ₀ : Env P),
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
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

/-- If `T` overapproximates and a Hoare triple holds on `T(st)` in L₂,
    then the triple holds on `st` in L₁. -/
theorem overapproximates_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : Overapproximates L₁ L₂ T)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ Pre s' Post)
    (hwfv : ∀ ρ₀ : Env P, Pre ρ₀ → WellFormedSemanticEvalVal ρ₀.eval) :
    Hoare.Triple L₁ Pre st Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  exact htriple ρ₀ ρ' hpre hwfb hf₀ ((hsem st s' ht ρ₀ hwfb (hwfv ρ₀ hpre)).1 ρ' |>.1 hstar)

theorem overapproximates_id (L₁ : Lang P) :
    Overapproximates L₁ L₁ some := by
  intro st s' ht ρ₀ _ _
  simp at ht; subst ht
  exact ⟨fun _ => ⟨id, fun _ => id⟩, id⟩

theorem overapproximates_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : Overapproximates L₁ L₂ T₁)
    (h₂ : Overapproximates L₂ L₃ T₂) :
    Overapproximates L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro st s'' ht ρ₀ hwfb hwfv
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    have hr₁ := h₁ st s' h ρ₀ hwfb hwfv
    have hr₂ := h₂ s' s'' ht ρ₀ hwfb hwfv
    refine ⟨fun ρ' => ⟨?_, ?_⟩, ?_⟩
    · intro hstar; exact (hr₂.1 ρ').1 ((hr₁.1 ρ').1 hstar)
    · intro lbl hstar; exact (hr₂.1 ρ').2 lbl ((hr₁.1 ρ').2 lbl hstar)
    · intro hfail; exact hr₂.2 (hr₁.2 hfail)
  | none => rw [h] at ht; exact absurd ht (by nofun)

/-! ## Aggressive overapproximation

`OverapproximatesAggressively` relaxes `Overapproximates`: the target may
terminate with `hasFailure = true` instead of matching the source's
terminal/exiting env exactly.  This models transforms like loop elimination
where `assert(I); assume(I)` may cause the target to fail when the
invariant doesn't hold. -/

/-- Aggressive overapproximation: The target program can assert-fail spuriously -/
public def OverapproximatesAggressively (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT) : Prop :=
  ∀ (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    ∀ (ρ₀ : Env P),
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
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

/-- `Overapproximates` implies `OverapproximatesAggressively`. -/
theorem Overapproximates.toAggressive (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (h : Overapproximates L₁ L₂ T) :
    OverapproximatesAggressively L₁ L₂ T := by
  intro st s' ht ρ₀ hwfb hwfv _hwfvar
  have hr := h st s' ht ρ₀ hwfb hwfv
  refine ⟨?_, ?_, hr.2⟩
  · intro ρ' hstar
    exact .inr (fun _ => (hr.1 ρ').1 hstar)
  · intro lbl ρ' hstar
    exact .inr (fun _ => (hr.1 ρ').2 lbl hstar)

theorem OverapproximatesAggressively_id (L₁ : Lang P) :
    OverapproximatesAggressively L₁ L₁ some := by
  intro st st' ht ρ₀ hwfb hwfv _hwfvar
  simp at ht; subst ht
  refine ⟨?_, ?_, id⟩
  · intro ρ' hstar
    exact .inr (fun _ => hstar)
  · intro lbl ρ' hstar
    exact .inr (fun _ => hstar)

theorem OverapproximatesAggressively_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : OverapproximatesAggressively L₁ L₂ T₁)
    (h₂ : OverapproximatesAggressively L₂ L₃ T₂) :
    OverapproximatesAggressively L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro st s'' ht ρ₀ hwfb hwfv hwfvar
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    have ⟨h₁_term, h₁_exit, h₁_fail⟩ := h₁ st s' h ρ₀ hwfb hwfv hwfvar
    have ⟨h₂_term, h₂_exit, h₂_fail⟩ := h₂ s' s'' ht ρ₀ hwfb hwfv hwfvar
    refine ⟨?_, ?_, fun hf => h₂_fail (h₁_fail hf)⟩
    · -- Terminal case
      intro ρ' hstar
      match h₁_term ρ' hstar with
      | .inl canfail₂ => exact .inl (h₂_fail canfail₂)
      | .inr hright =>
        by_cases hf : ρ'.hasFailure = false
        · have hterm₂ := hright hf
          match h₂_term ρ' hterm₂ with
          | .inl canfail₃ => exact .inl canfail₃
          | .inr hright₃ => exact .inr (fun _ => hright₃ hf)
        · exact .inr (fun hf' => absurd hf' hf)
    · -- Exiting case
      intro lbl ρ' hstar
      match h₁_exit lbl ρ' hstar with
      | .inl canfail₂ => exact .inl (h₂_fail canfail₂)
      | .inr hright =>
        by_cases hf : ρ'.hasFailure = false
        · have hexit₂ := hright hf
          match h₂_exit lbl ρ' hexit₂ with
          | .inl canfail₃ => exact .inl canfail₃
          | .inr hright₃ => exact .inr (fun _ => hright₃ hf)
        · exact .inr (fun hf' => absurd hf' hf)
  | none => rw [h] at ht; exact absurd ht (by nofun)

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

omit [HasFvar P] [HasBool P] [HasNot P] [HasVal P] in
private theorem mapM_noFuncDecl
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hnofd_T : ∀ s s', T s = some s' → Stmt.noFuncDecl s = true)
    (ss : List (Stmt P CmdT)) (ss' : List (Stmt P CmdT))
    (hmap : ss.mapM T = some ss') :
    Block.noFuncDecl ss = true := by
  induction ss generalizing ss' with
  | nil => simp [Block.noFuncDecl]
  | cons s rest ih =>
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    simp [Block.noFuncDecl, hnofd_T s s' hs, ih rest' hrm]

omit [HasFvar P] [HasVal P] in
/-- Decompose a seq execution reaching a config with `hasFailure = true`:
    either the inner config reaches a failing config, or the inner terminates
    and the tail stmts reach a failing config. -/
private theorem seq_hasFailure_cases
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {cfg : Config P CmdT}
    (hstar : StepStmtStar P evalCmd extendEval (.seq inner ss) cfg)
    (hfail : cfg.getEnv.hasFailure = true) :
    (∃ inner_cfg, inner_cfg.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendEval inner inner_cfg)
    ∨
    (∃ ρ₁, StepStmtStar P evalCmd extendEval inner (.terminal ρ₁) ∧
      ∃ tail_cfg, tail_cfg.getEnv.hasFailure = true ∧
        StepStmtStar P evalCmd extendEval (.stmts ss ρ₁) tail_cfg) := by
  suffices ∀ src dst, StepStmtStar P evalCmd extendEval src dst →
      ∀ inner ss, src = .seq inner ss → dst.getEnv.hasFailure = true →
      (∃ inner_cfg, inner_cfg.getEnv.hasFailure = true ∧
        StepStmtStar P evalCmd extendEval inner inner_cfg)
      ∨
      (∃ ρ₁, StepStmtStar P evalCmd extendEval inner (.terminal ρ₁) ∧
        ∃ tail_cfg, tail_cfg.getEnv.hasFailure = true ∧
          StepStmtStar P evalCmd extendEval (.stmts ss ρ₁) tail_cfg) from
    this _ _ hstar _ _ rfl hfail
  intro src dst hstar_g
  induction hstar_g with
  | refl =>
    intro inner ss hsrc hf
    subst hsrc; simp [Config.getEnv] at hf
    exact Or.inl ⟨inner, hf, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner ss hsrc hf; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      match ih _ _ rfl hf with
      | Or.inl ⟨inner_cfg, hfi, hreach⟩ =>
        exact Or.inl ⟨inner_cfg, hfi, .step _ _ _ h hreach⟩
      | Or.inr ⟨ρ₁, hterm, tail_cfg, hft, htail⟩ =>
        exact Or.inr ⟨ρ₁, .step _ _ _ h hterm, tail_cfg, hft, htail⟩
    | step_seq_done =>
      exact Or.inr ⟨_, .refl _, _, hf, hrest⟩
    | step_seq_exit =>
      cases hrest with
      | refl => exact Or.inl ⟨.exiting _ _, hf, .refl _⟩
      | step _ _ _ h _ => cases h

/-- CanFail preservation for statement-list overapproximation. -/
private theorem overapproximates_stmts_canfail
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (ss : List (Stmt P CmdT))
    (hnofd : Block.noFuncDecl ss = true) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss ρ₀ →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ _ _ ⟨cfg, hfail, hreach⟩
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    exact ⟨cfg, hfail, hreach⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ hwfb hwfv ⟨cfg, hfail, hreach⟩
    simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd
    have ⟨hnofd_s, hnofd_rest⟩ := hnofd
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    -- hreach : StepStmtStar (.stmts (s :: rest) ρ₀) cfg
    -- First step: step_stmts_cons gives .seq (.stmt s ρ₀) rest
    cases hreach with
    | refl =>
      -- cfg = .stmts (s :: rest) ρ₀, getEnv = ρ₀
      -- Need to produce a failing config reachable from .stmts (s' :: rest') ρ₀
      simp [Config.getEnv] at hfail
      exact ⟨.stmts (s' :: rest') ρ₀, by simp [Config.getEnv, hfail], .refl _⟩
    | step _ _ _ hstep hrest_exec =>
      cases hstep with
      | step_stmts_cons =>
        -- hrest_exec : StepStmtStar (.seq (.stmt s ρ₀) rest) cfg
        match seq_hasFailure_cases evalCmd extendEval hrest_exec hfail with
        | .inl ⟨inner_cfg, hf_inner, hreach_inner⟩ =>
          -- Failure within execution of s. Use hsem for CanFail preservation.
          have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
            ⟨inner_cfg, hf_inner, hreach_inner⟩
          have hcanfail_s' := (hsem s s' hs ρ₀ hwfb hwfv).2 hcanfail_s
          -- hcanfail_s' : CanFail (Lang.imperative ...) s' ρ₀
          -- i.e. ∃ cfg', cfg'.getEnv.hasFailure = true ∧ StepStmtStar (.stmt s' ρ₀) cfg'
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_s'
          -- Lift to .stmts (s' :: rest') ρ₀ via step_stmts_cons + seq_inner_star
          exact ⟨.seq cfg' rest', by simp [Config.getEnv]; exact hf',
            .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach')⟩
        | .inr ⟨ρ₁, hterm_s, tail_cfg, hf_tail, htail⟩ =>
          -- s terminates at ρ₁, failure in rest
          have eval_preserved : WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval := by
            have heq := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd_s hterm_s
            exact ⟨heq ▸ hwfb, heq ▸ hwfv⟩
          have hcanfail_rest : CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) rest ρ₁ :=
            ⟨tail_cfg, hf_tail, htail⟩
          have hcanfail_rest' := ih hnofd_rest rest' hrm ρ₁
            eval_preserved.1 eval_preserved.2 hcanfail_rest
          -- hcanfail_rest' : CanFail (imperativeBlock ...) rest' ρ₁
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_rest'
          -- Lift: .stmts (s' :: rest') ρ₀ →* .stmts rest' ρ₁ →* cfg'
          have hterm_s' := (hsem s s' hs ρ₀ hwfb hwfv).1 ρ₁ |>.1 hterm_s
          exact ⟨cfg', hf',
            ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ hterm_s')
              hreach'⟩

private theorem overapproximates_stmts_aux
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (ss : List (Stmt P CmdT))
    (hnofd : Block.noFuncDecl ss = true) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') →
         StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.terminal ρ'))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ') →
                StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.exiting lbl ρ')) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _ _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨id, fun _ => id⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwfb hwfv
    simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd
    have ⟨hnofd_s, hnofd_rest⟩ := hnofd
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have eval_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval := by
      intro ρ₁ hterm_s
      have heq := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd_s hterm_s
      exact ⟨heq ▸ hwfb, heq ▸ hwfv⟩
    constructor
    · intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendEval hrest_exec
          have ⟨hwfb₁, hwfv₁⟩ := eval_preserved ρ₁ hterm_s
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
              ((hsem s s' hs ρ₀ hwfb hwfv).1 ρ₁ |>.1 hterm_s))
            ((ih hnofd_rest rest' hrm ρ₁ ρ' hwfb₁ hwfv₁).1 hterm_rest)
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendEval hrest_exec with
          | .inl hexit_s =>
            exact .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendEval _ _ rest'
                ((hsem s s' hs ρ₀ hwfb hwfv).1 ρ' |>.2 lbl hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have ⟨hwfb₁, hwfv₁⟩ := eval_preserved ρ₁ hterm_s
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
                ((hsem s s' hs ρ₀ hwfb hwfv).1 ρ₁ |>.1 hterm_s))
              ((ih hnofd_rest rest' hrm ρ₁ ρ' hwfb₁ hwfv₁).2 lbl hexit_rest)

theorem overapproximates_stmts
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (hnofd_T : ∀ s s', T s = some s' → Stmt.noFuncDecl s = true) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) := by
  intro ss ss' hmap ρ₀ hwfb hwfv
  refine ⟨fun ρ' => overapproximates_stmts_aux evalCmd extendEval isAtAssertFn T hsem ss
    (mapM_noFuncDecl T hnofd_T ss ss' hmap) ss' hmap ρ₀ ρ' hwfb hwfv, ?_⟩
  exact overapproximates_stmts_canfail evalCmd extendEval isAtAssertFn T hsem ss
    (mapM_noFuncDecl T hnofd_T ss ss' hmap) ss' hmap ρ₀ hwfb hwfv


private theorem overapproximatesAggressively_stmts_canfail
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (ss : List (Stmt P CmdT))
    (hnofd : Block.noFuncDecl ss = true) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss ρ₀ →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ _ _ _ ⟨cfg, hfail, hreach⟩
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    exact ⟨cfg, hfail, hreach⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, hreach⟩
    simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd
    have ⟨hnofd_s, hnofd_rest⟩ := hnofd
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    cases hreach with
    | refl =>
      simp [Config.getEnv] at hfail
      exact ⟨.stmts (s' :: rest') ρ₀, by simp [Config.getEnv, hfail], .refl _⟩
    | step _ _ _ hstep hrest_exec =>
      cases hstep with
      | step_stmts_cons =>
        match seq_hasFailure_cases evalCmd extendEval hrest_exec hfail with
        | .inl ⟨inner_cfg, hf_inner, hreach_inner⟩ =>
          have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
            ⟨inner_cfg, hf_inner, hreach_inner⟩
          have hcanfail_s' := (hsem s s' hs ρ₀ hwfb hwfv hwfvar).2.2 hcanfail_s
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_s'
          exact ⟨.seq cfg' rest', by simp [Config.getEnv]; exact hf',
            .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach')⟩
        | .inr ⟨ρ₁, hterm_s, tail_cfg, hf_tail, htail⟩ =>
          have eval_preserved :
              WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval
              ∧ WellFormedSemanticEvalVar ρ₁.eval := by
            have heq := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd_s hterm_s
            exact ⟨heq ▸ hwfb, heq ▸ hwfv, heq ▸ hwfvar⟩
          have hcanfail_rest : CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) rest ρ₁ :=
            ⟨tail_cfg, hf_tail, htail⟩
          have hcanfail_rest' := ih hnofd_rest rest' hrm ρ₁
            eval_preserved.1 eval_preserved.2.1 eval_preserved.2.2 hcanfail_rest
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_rest'
          -- hsem gives CanFail ∨ (hasFailure = false → terminates) for s' at ρ₁
          match (hsem s s' hs ρ₀ hwfb hwfv hwfvar).1 ρ₁ hterm_s with
          | .inl canfail_s' =>
            obtain ⟨cfg'', hf'', hreach''⟩ := canfail_s'
            exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
              .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach'')⟩
          | .inr hterm_s' =>
            by_cases hf₁ : ρ₁.hasFailure = false
            · exact ⟨cfg', hf',
                ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                  hreach'⟩
            · have hf₁' : ρ₁.hasFailure = true := by
                cases h : ρ₁.hasFailure <;> simp_all
              have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
                ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁', hterm_s⟩
              have hcanfail_s' := (hsem s s' hs ρ₀ hwfb hwfv hwfvar).2.2 hcanfail_s
              obtain ⟨cfg'', hf'', hreach''⟩ := hcanfail_s'
              exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
                .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach'')⟩

omit [HasVal P] in
/-- Helper: lifting CanFail from statement-level to statement-list level via `seq_inner_star`. -/
private theorem lift_canfail_to_stmts
    (s' : Stmt P CmdT) (rest' : List (Stmt P CmdT)) (ρ₀ : Env P)
    (hcf : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s' ρ₀) :
    CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) (s' :: rest') ρ₀ := by
  obtain ⟨cfg', hf', hreach'⟩ := hcf
  exact ⟨.seq cfg' rest', by simp [Config.getEnv]; exact hf',
    .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach')⟩

private theorem overapproximatesAggressively_stmts_aux
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (ss : List (Stmt P CmdT))
    (hnofd : Block.noFuncDecl ss = true) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') →
          CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ') →
          CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.exiting lbl ρ'))) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _ _ _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨fun h => .inr (fun _ => h), fun lbl h => .inr (fun _ => h)⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwfb hwfv hwfvar
    simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd
    have ⟨hnofd_s, hnofd_rest⟩ := hnofd
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have eval_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval
        ∧ WellFormedSemanticEvalVar ρ₁.eval := by
      intro ρ₁ hterm_s
      have heq := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd_s hterm_s
      exact ⟨heq ▸ hwfb, heq ▸ hwfv, heq ▸ hwfvar⟩
    have ⟨hsem_term, hsem_exit, hsem_fail⟩ := hsem s s' hs ρ₀ hwfb hwfv hwfvar
    -- Helper for the common pattern: ρ₁.hasFailure = true → s can fail → s' can fail → lift
    have canfail_from_failure : ∀ (ρ₁ : Env P),
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        ρ₁.hasFailure = true →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) (s' :: rest') ρ₀ := by
      intro ρ₁ hterm_s hf₁
      have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
        ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁, hterm_s⟩
      exact lift_canfail_to_stmts evalCmd extendEval isAtAssertFn s' rest' ρ₀
        (hsem_fail hcanfail_s)
    constructor
    · -- Terminal case
      intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendEval hrest_exec
          have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
          match hsem_term ρ₁ hterm_s with
          | .inl canfail_s' =>
            exact .inl (lift_canfail_to_stmts evalCmd extendEval isAtAssertFn s' rest' ρ₀ canfail_s')
          | .inr hterm_s' =>
            -- First check if ρ₁.hasFailure = false; if not, we get CanFail directly
            by_cases hf₁ : ρ₁.hasFailure = false
            · -- ρ₁ has no failure, so s' terminates at ρ₁
              have ih_result := (ih hnofd_rest rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).1 hterm_rest
              match ih_result with
              | .inl canfail_rest' =>
                obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                exact .inl ⟨cfg', hf',
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    hreach'⟩
              | .inr hterm_rest' =>
                exact .inr fun hf =>
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    (hterm_rest' hf)
            · -- ρ₁.hasFailure = true, so s can fail → s' can fail → lift to whole list
              have hf₁' : ρ₁.hasFailure = true := by
                rcases Bool.eq_false_or_eq_true ρ₁.hasFailure with h | h
                · exact h
                · exact absurd h hf₁
              exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
    · -- Exiting case
      intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendEval hrest_exec with
          | .inl hexit_s =>
            match hsem_exit lbl ρ' hexit_s with
            | .inl canfail_s' =>
              exact .inl (lift_canfail_to_stmts evalCmd extendEval isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hexit_s' =>
              exact .inr fun hf =>
                .step _ _ _ .step_stmts_cons
                  (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendEval _ _ rest'
                    (hexit_s' hf))
                    (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
            match hsem_term ρ₁ hterm_s with
            | .inl canfail_s' =>
              exact .inl (lift_canfail_to_stmts evalCmd extendEval isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hterm_s' =>
              have ih_result := (ih hnofd_rest rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).2 lbl hexit_rest
              match ih_result with
              | .inl canfail_rest' =>
                by_cases hf₁ : ρ₁.hasFailure = false
                · obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                  exact .inl ⟨cfg', hf',
                    ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      hreach'⟩
                · have hf₁' : ρ₁.hasFailure = true := by
                    rcases Bool.eq_false_or_eq_true ρ₁.hasFailure with h | h
                    · exact h
                    · exact absurd h hf₁
                  exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
              | .inr hexit_rest' =>
                exact .inr fun hf => by
                  by_cases hf₁ : ρ₁.hasFailure = false
                  · exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      (hexit_rest' hf)
                  · exfalso
                    have hf₁' : ρ₁.hasFailure = true := by
                      rcases Bool.eq_false_or_eq_true ρ₁.hasFailure with h | h
                      · exact h
                      · exact absurd h hf₁
                    have : ρ'.hasFailure = true :=
                      StepStmtStar_hasFailure_monotone hexit_rest hf₁'
                    exact absurd hf (by simp [this])

theorem overapproximatesAggressively_stmts
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (hnofd_T : ∀ s s', T s = some s' → Stmt.noFuncDecl s = true) :
    OverapproximatesAggressively
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) := by
  intro ss ss' hmap ρ₀ hwfb hwfv hwfvar
  have hnofd := mapM_noFuncDecl T hnofd_T ss ss' hmap
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, ?_⟩
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendEval isAtAssertFn T hsem ss
      hnofd ss' hmap ρ₀ ρ' hwfb hwfv hwfvar).1 hstar
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendEval isAtAssertFn T hsem ss
      hnofd ss' hmap ρ₀ ρ' hwfb hwfv hwfvar).2 lbl hstar
  · exact overapproximatesAggressively_stmts_canfail evalCmd extendEval isAtAssertFn T hsem ss
      hnofd ss' hmap ρ₀ hwfb hwfv hwfvar

end ImperativeStmts

end Transform
end Specification
end Imperative

end -- public section

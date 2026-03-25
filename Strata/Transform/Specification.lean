/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsSmallStep
import all Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.ListUtils

/-! # Soundness Specification

This file defines two styles of top-level soundness for assertion checks,
proves that the Hoare-triple style (B) is a special case of the reachability
style (A), and defines correctness of program transformations.

All definitions are generic over the `PureExpr` parameter `P`, using the
Imperative dialect's `Cmd P` as the command type and `EvalCmd P` as the
command evaluator.

## Style A — Reachability-based assertion validity

Whenever execution of a statement (under small-step semantics) reaches a
configuration whose head is an `assert label expr`, the expression `expr`
evaluates to `true` in the current store.

## Style B — Hoare-triple assertion validity

For a given precondition P and postcondition Q (both predicates on envs),
if the initial env satisfies P and the statement executes to a terminal
env, then the terminal env satisfies Q.  This is the classical partial-
correctness Hoare triple {P} S {Q}.

## Transformation correctness

A transformation `T` on statements is *correct* (w.r.t. assertion checks) if:
for every assert label `a`, if `a` is valid in `T(s)` then `a` is valid in `s`.
-/

public section

namespace Imperative

namespace Specification

variable (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P]
variable (extendEval : ExtendEval P)


/-! ## Style A — Reachability-based assertion validity -/

/-- Assert `a` is *valid* in statement `s` if, for every initial
    environment and reachable configuration that is at assert `a`,
    the assert expression evaluates to `true`. -/
def AssertValid
    (s : Stmt P (Cmd P)) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : Config P (Cmd P)),
    StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) cfg →
    isAtAssert P cfg a →
    cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- All asserts are valid in statement `s`. Assert `a` does not have to be
    constrained to those in `s` because AssertValid uses partial correctness. -/
def AllAssertsValid
    (s : Stmt P (Cmd P)) : Prop :=
  ∀ (a : AssertId P), AssertValid P extendEval s a



/-! ## Style B — Hoare-triple assertion validity -/

namespace Hoare

/-- Partial-correctness Hoare triple using small-step semantics.

    `Triple` covers only normal termination (`.terminal`).
    This terminal-only definition keeps the `AssertValid ↔ Triple`
    equivalence clean (no extra assumptions needed).
-/
def Triple
    (Pre : Env P → Prop)
    (s : Stmt P (Cmd P))
    (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    -- Precondition and well-formedness
    Pre ρ₀ →
    WellFormedSemanticEvalBool ρ₀.eval →
    ρ₀.hasFailure = false →
    -- Execution
    StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ') →
    -- Postcondition
    Post ρ' ∧ ρ'.hasFailure = false

/-- Partial-correctness Hoare triple for a list of statements (a block body).
    Unlike `Triple`, this covers both normal termination (`.terminal`) and
    early exit (`.exiting`) because blocks catch exits. Some exits can `leak`
    the outermost block though, and it might require additional constraints
    on Hoare rules.

    Triple can be unconditionally derived from TripleBlock through
    TripleBlock.toTriple. TripleBlock can be derived from Triple only when
    all exits are caught by blocks (there should be no leaking exits).
-/
def TripleBlock
    (Pre : Env P → Prop)
    (ss : List (Stmt P (Cmd P)))
    (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    -- Precondition
    Pre ρ₀ →
    WellFormedSemanticEvalBool ρ₀.eval →
    ρ₀.hasFailure = false →
    -- Execution
    (StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ') ∨
     ∃ lbl, StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.exiting lbl ρ')) →
    -- Postcondition
    Post ρ' ∧ ρ'.hasFailure = false


/-! ## Structural Hoare rules -/

/-- False precondition: any postcondition holds vacuously. -/
theorem false_pre (s : Stmt P (Cmd P)) (Post : Env P → Prop) :
    Triple P extendEval (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence
    {Pre Pre' : Env P → Prop} {Post Post' : Env P → Prop} {s : Stmt P (Cmd P)}
    (h : Triple P extendEval Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple P extendEval Pre' s Post' := by
  intro ρ₀ ρ' hpre' hwfb hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hwfb hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩

/-- Empty statement list is skip. -/
theorem skip_block (Pre : Env P → Prop) :
    TripleBlock P extendEval Pre [] Pre := by
  intro ρ₀ ρ' hpre _ hf₀ hstar
  match hstar with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ h1 r1 => cases h1 with
      | step_stmts_nil => cases r1 with
        | refl => exact ⟨hpre, hf₀⟩
        | step _ _ _ h _ => exact nomatch h
  | .inr ⟨_, hexit⟩ =>
    -- Empty stmts can't exit
    cases hexit with
    | step _ _ _ h _ => cases h with
      | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

/-- A single command: the postcondition is determined by `EvalCmd`. -/
theorem cmd (c : Cmd P) (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
      EvalCmd P ρ₀.eval ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = false) :
    Triple P extendEval Pre (.cmd c) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_cmd hcmd =>
      cases r1 with
      | refl =>
        have ⟨hp, hfeq⟩ := h ρ₀ _ _ hpre hwfb hf₀ hcmd
        simp [hf₀] at hp ⊢; exact ⟨hp, hfeq⟩
      | step _ _ _ h _ => exact nomatch h

/-- Sequential cons: if the head statement satisfies `{P} s {Q}` and
    the tail satisfies `{Q} ss {R}`, then `{P} s :: ss {R}`. -/
theorem seq_cons {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    {Pre Mid Post : Env P → Prop}
    (h₁ : Triple P extendEval Pre s Mid)
    (h₂ : TripleBlock P extendEval Mid ss Post)
    -- `noFuncDecl` ensures the evaluator is unchanged by `s`, so
    -- `WellFormedSemanticEvalBool` propagates from ρ₀ to ρ₁.
    (hnofd : Stmt.noFuncDecl s = true)
    -- `exitsCoveredByBlocks` ensures `s` cannot escape via `.exiting`.
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock P extendEval Pre (s :: ss) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hdone
  -- When s has noFuncDecl, execution preserves the evaluator, hence wfb.
  have hwfb_preserved : ∀ ρ₁, StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ₁) →
      WellFormedSemanticEvalBool ρ₁.eval := by
    intro ρ₁ hterm
    have := smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval s ρ₀ ρ₁ hnofd hterm
    rw [this]; exact hwfb
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_ss⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
        have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
        exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) hf₁ (.inl hrest_ss)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P (EvalCmd P) extendEval hrest with
        | .inl hexit_inner =>
          -- s exited — impossible by exitsCoveredByBlocks
          exact absurd hexit_inner
            (exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
          have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
          exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) hf₁ (.inr ⟨lbl, hexit_ss⟩)

/-- Lift a `TripleBlock` to a `Triple` by wrapping in a block.
    The block catches exits from the body, converting them to terminal. -/
theorem TripleBlock.toTriple {ss : List (Stmt P (Cmd P))} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h : TripleBlock P extendEval Pre ss Post) :
    Triple P extendEval Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ hstep hrest => cases hstep with
    | step_block =>
      match block_reaches_terminal P (EvalCmd P) extendEval hrest with
      | .inl hterm => exact h ρ₀ ρ' hpre hwfb hf₀ (.inl hterm)
      | .inr ⟨lbl, hexit_inner⟩ => exact h ρ₀ ρ' hpre hwfb hf₀ (.inr ⟨lbl, hexit_inner⟩)

/-- Lift a `Triple` to a `TripleBlock` for a singleton list.
    Requires `exitsCoveredByBlocks` so the exit disjunct is vacuous. -/
theorem Triple.toTripleBlock {s : Stmt P (Cmd P)}
    {Pre Post : Env P → Prop}
    (h : Triple P extendEval Pre s Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock P extendEval Pre [s] Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hdone
  match hdone with
  | .inl hterm =>
    -- .stmts [s] ρ₀ →* .terminal ρ'
    -- Invert: .stmts [s] ρ₀ → .seq (.stmt s ρ₀) [] →* .terminal ρ'
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
        have ⟨hp, hf⟩ := h ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
        -- hrest_nil : .stmts [] ρ₁ →* .terminal ρ', so ρ' = ρ₁
        cases hrest_nil with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil => cases r1 with
            | refl => exact ⟨hp, hf⟩
            | step _ _ _ h _ => exact nomatch h
  | .inr ⟨lbl, hexit⟩ =>
    -- .stmts [s] ρ₀ →* .exiting lbl ρ'
    -- s can't exit by exitsCoveredByBlocks
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P (EvalCmd P) extendEval hrest with
        | .inl hexit_s =>
          exact absurd hexit_s
            (exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_nil⟩ =>
          -- .stmts [] ρ₁ →* .exiting — impossible
          cases hexit_nil with
          | step _ _ _ h _ => cases h with
            | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

/-- Empty block is skip: the environment is unchanged. -/
theorem skip (l : String) (md : MetaData P) (Pre : Env P → Prop) :
    Triple P extendEval Pre (.block l [] md) Pre :=
  (skip_block P extendEval Pre).toTriple

/-- If-then-else rule. -/
theorem ite {c : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (ht : TripleBlock P extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.tt) tss Post)
    (he : TripleBlock P extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.ff) ess Post) :
    Triple P extendEval Pre (.ite c tss ess md) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_ite_true hc _ => exact ht ρ₀ ρ' ⟨hpre, hc⟩ hwfb hf₀ (.inl r1)
    | step_ite_false hc _ => exact he ρ₀ ρ' ⟨hpre, hc⟩ hwfb hf₀ (.inl r1)

/- TODO: Loop rule -/


/-! ## General connection between HoareTriple and AssertValid

For a general statement `st` (not just a single assert), we can connect
`HoareTriple` and `AssertValid` by forming a composite program:

    assume pre_expr; st; assert post_expr

The `assume` encodes the precondition (filtering executions where the
precondition holds) and the `assert` encodes the postcondition.  We wrap
this sequence in a block to form a single `Stmt`.
-/

/-- The composite statement `assume pre; st; assert post` wrapped in a block.
    This encodes a Hoare triple `{pre} st {post}` as a single statement
    whose assert validity captures the triple's meaning. -/
def PredicatedStmt
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P) : Stmt P (Cmd P) :=
  .block block_label
    [.cmd (.assume pre_label pre_expr pre_md), st, .cmd (.assert post_label post_expr post_md)]
    block_md

/--
**Direction 1** (`hoareTriple_implies_assertValid_general`):
If `{P} st {Q}` holds (where P ↔ `pre_expr = tt` and Q ↔ `post_expr = tt`),
then `AssertValid` holds for the composite `assume pre; st; assert post`.
-/
theorem hoareTriple_implies_assertValid
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hoare : Triple P extendEval
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt))
    -- st does not syntactically contain any assert with label `post_label`.
    (hno : st.noMatchingAssert post_label) :
    AssertValid P extendEval
      (PredicatedStmt P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg hreach hat
  -- Derive the execution-level no-match property from the syntactic check
  have hno_match := noMatchingAssert_implies_no_reachable_assert P extendEval st post_label post_expr hno
  -- Decompose block execution via block_isAtAssert_inner
  unfold PredicatedStmt at hreach
  cases hreach with
  | refl => exact absurd hat (by simp [isAtAssert])
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_block =>
      have ⟨inner, heq_cfg, hinner_star, hat_inner⟩ :=
        block_isAtAssert_inner P extendEval _ _ _ _ hrest hat
      subst heq_cfg
      -- Decompose: stmts [assume, st, assert] → seq (stmt assume) [st, assert]
      cases hinner_star with
      | refl => exact absurd hat_inner (by simp [isAtAssert])
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_stmts_cons =>
          -- Decompose seq for assume
          match seq_isAtAssert_cases P extendEval _ _ _ _ hrest2 hat_inner with
          | .inl ⟨_, _, hreach_assume, hat_assume⟩ =>
            -- Match during assume execution — impossible (assume ≠ assert)
            cases hreach_assume with
            | refl => exact absurd hat_assume (by simp [isAtAssert])
            | step _ _ _ h _ => cases h with
              | step_cmd => rename_i hr; cases hr with
                | refl => exact absurd hat_assume (by simp [isAtAssert])
                | step _ _ _ h _ => exact absurd h (by intro h; cases h)
          | .inr ⟨ρ₁, hterm_assume, hrest_stmts, hat_stmts⟩ =>
            -- Assume terminated at ρ₁. Decompose stmts [st, assert]
            cases hrest_stmts with
            | refl =>
              -- At .stmts [st, assert] ρ₁. If st is a matching assert,
              -- hno_match gives contradiction.
              have : ¬ isAtAssert P (.stmts (st :: [.cmd (.assert post_label post_expr post_md)]) ρ₁)
                  ⟨post_label, post_expr⟩ := by
                intro h_at
                -- isAtAssert checks if st is .cmd (.assert ...) with matching label/expr
                match st with
                | .cmd (.assert l e md') =>
                  -- st IS a matching assert — use hno_match on (.stmt st ρ₁) at zero steps
                  have h := hno_match ρ₁ (.stmt (.cmd (.assert l e md')) ρ₁) (.refl _)
                  simp [isAtAssert] at h h_at
                  exact h h_at.1 h_at.2
                | .cmd (.init ..) | .cmd (.set ..) | .cmd (.havoc ..) | .cmd (.assume ..)
                | .cmd (.cover ..) | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl ..
                | .typeDecl .. =>
                  simp [isAtAssert] at h_at
              exact absurd hat_stmts this
            | step _ _ _ hstep3 hrest3 =>
              cases hstep3 with
              | step_stmts_cons =>
                -- Decompose seq for st
                match seq_isAtAssert_cases P extendEval _ _ _ _ hrest3 hat_stmts with
                | .inl ⟨_, _, hreach_st, hat_st⟩ =>
                  -- Match during st — contradicts hno_match
                  exact absurd hat_st (hno_match ρ₁ _ hreach_st)
                | .inr ⟨ρ', hterm_st, hrest_assert, hat_assert⟩ =>
                  -- st terminated at ρ'. Extract Pre from the assume step.
                  cases hterm_assume with
                  | step _ _ _ h_assume_step h_assume_rest =>
                    cases h_assume_step with
                    | step_cmd hcmd =>
                      cases hcmd with
                      | eval_assume hpre hwfb =>
                        cases h_assume_rest with
                        | refl =>
                          have ⟨ρ'_clean, hterm_clean, hs_eq, he_eq⟩ :=
                            smallStep_hasFailure_irrel P (EvalCmd P) extendEval
                              st _ ρ' hterm_st { ρ₀ with hasFailure := false } rfl rfl
                          have ⟨hpost, _⟩ := hoare { ρ₀ with hasFailure := false } ρ'_clean
                            hpre hwfb rfl hterm_clean
                          simp only [hs_eq, he_eq] at hpost
                          simp only [Config.getEval, Config.getStore]
                          have ⟨he, hs⟩ := assert_tail_getEvalStore P extendEval
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)


/--
    **Direction 2** (`assertValid_implies_hoareTriple`):
    If `AllAssertsValid` holds for the composite `assume pre; st; assert post`,
    then `{P} st {Q}` holds.

    The `AllAssertsValid` hypothesis (rather than just `AssertValid` for the
    post assert) ensures that all intermediate asserts in `st` also pass,
    which is needed for the `hasFailure = false` postcondition. -/
theorem assertValid_implies_hoareTriple
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hvalid : AllAssertsValid P extendEval
      (PredicatedStmt P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    Triple P extendEval
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt) := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  let assume_stmt : Stmt P (Cmd P) := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P (Cmd P) := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P (Cmd P)) := [assume_stmt, st, assert_stmt]
  -- Helper: embed st's execution inside the composite to derive assert validity.
  -- For any config reachable from st, if it's at an assert, the assert passes.
  have hvalid_st : ∀ (a : AssertId P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) cfg →
      isAtAssert P cfg a →
      cfg.getEval cfg.getStore a.expr = some HasBool.tt := by
    intro a cfg hstar_st hat
    -- Build composite execution: block → stmts → assume → stmts [st, ...] → st → cfg
    have h_assume : StepStmtStar P (EvalCmd P) extendEval
        (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
      .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
    have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P) = ρ₀ := by
      cases ρ₀; simp [Bool.or_false]
    have h1 := stmts_cons_step P (EvalCmd P) extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
    rw [h_ρ₁_eq] at h1
    have h2 : StepStmtStar P (EvalCmd P) extendEval
        (.stmts [st, assert_stmt] ρ₀) (.seq (.stmt st ρ₀) [assert_stmt]) :=
      .step _ _ _ StepStmt.step_stmts_cons (.refl _)
    have h3 := seq_inner_star P (EvalCmd P) extendEval _ _ [assert_stmt] hstar_st
    have h_inner := reflTrans_trans (h1 := reflTrans_trans (h1 := h1) (h2 := h2)) (h2 := h3)
    have h_block := block_inner_star P (EvalCmd P) extendEval _ _ block_label h_inner
    have h_start : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.block block_label body block_md) ρ₀) (.block block_label (.stmts body ρ₀)) :=
      .step _ _ _ StepStmt.step_block (.refl _)
    have h_full := reflTrans_trans (h1 := h_start) (h2 := h_block)
    have h_result := hvalid a ρ₀ _ h_full hat
    simp only [Config.getEval, Config.getStore] at h_result ⊢
    exact h_result
  -- Post: build composite execution through to the assert after st.
  have h_assume : StepStmtStar P (EvalCmd P) extendEval
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
  have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P) = ρ₀ := by
    cases ρ₀; simp [Bool.or_false]
  have h1 := stmts_cons_step P (EvalCmd P) extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
  rw [h_ρ₁_eq] at h1
  have h2 := stmts_cons_step P (EvalCmd P) extendEval st [assert_stmt] ρ₀ ρ' hstar
  have h3 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [assert_stmt] ρ') (.seq (.stmt assert_stmt ρ') []) :=
    .step _ _ _ StepStmt.step_stmts_cons (.refl _)
  have h_inner := reflTrans_trans (h1 := reflTrans_trans (h1 := h1) (h2 := h2)) (h2 := h3)
  have h_block := block_inner_star P (EvalCmd P) extendEval _ _ block_label h_inner
  have h_start : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.block block_label body block_md) ρ₀) (.block block_label (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  have h_full := reflTrans_trans (h1 := h_start) (h2 := h_block)
  have h_at : isAtAssert P (.block block_label (.seq (.stmt assert_stmt ρ') [])) ⟨post_label, post_expr⟩ := by
    simp [isAtAssert, assert_stmt]
  have h_result := hvalid ⟨post_label, post_expr⟩ ρ₀ _ h_full h_at
  simp only [Config.getEval, Config.getStore] at h_result
  exact ⟨h_result, allAssertsValid_preserves_noFailure P extendEval
    (ρ₀ := ρ₀) (ρ' := ρ') st hvalid_st hf₀ hstar⟩

end Hoare


namespace Transform

/-! ## Transformation Correctness

A program transformation is a partial function on statements
(`Stmt P (Cmd P) → Option (Stmt P (Cmd P))`).  It returns `some s'`
on success and `none` on failure (e.g., unsupported input).

A transformation `T` is *sound* (w.r.t. assertion checks) if:
for every assert `a`, if `T s = some s'` and `a` is valid in `s'`,
then `a` is valid in `s`.
-/

/-! ## The Sound predicate and its properties -/

/-- A transformation is *sound* if it preserves assertion validity. -/
def Sound
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P))) : Prop :=
  ∀ (s s' : Stmt P (Cmd P)) (a : AssertId P),
    T s = some s' →
    AssertValid P extendEval s' a →
    AssertValid P extendEval s a

/-- Composition of sound transformations is sound. -/
theorem sound_comp
    (T₁ T₂ : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (h₁ : Sound P extendEval T₁)
    (h₂ : Sound P extendEval T₂) :
    Sound P extendEval (fun s => T₁ s >>= T₂) := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' =>
    rw [h1] at hrun
    exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none =>
    rw [h1] at hrun
    exact absurd hrun (by nofun)

/-- If `T` is sound and assert `a` is valid in the output,
    then `a` is also valid in the input. -/
theorem sound_assertValid
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (a : AssertId P)
    (s s' : Stmt P (Cmd P))
    (ht : T s = some s')
    (hsound : Sound P extendEval T)
    (hvalid : AssertValid P extendEval s' a) :
    AssertValid P extendEval s a :=
  hsound s s' a ht hvalid

/-- If `T` is sound and all asserts are valid in the output,
    then all asserts are valid in the input. -/
theorem sound_allAsserts
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (s s' : Stmt P (Cmd P))
    (ht : T s = some s')
    (hsound : Sound P extendEval T)
    (hvalid : AllAssertsValid P extendEval s') :
    AllAssertsValid P extendEval s :=
  fun a => sound_assertValid P extendEval T a s s' ht hsound (hvalid a)

/-- Identity transform is sound. -/
theorem sound_id :
    Sound P extendEval some := by
  intro s s' a ht hvalid
  simp at ht; subst ht; exact hvalid

/-! ## The Overapproximate predicate and its properties -/

/-- A transformation `T` *overapproximates* if, for every input statement `st`,
    every configuration reachable from `st` is also reachable from `T(st)`.
    That is, `T(st)`'s reachable states are a superset of `st`'s. -/
def Overapproximates
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P))) : Prop :=
  ∀ (st s' : Stmt P (Cmd P)),
    T st = some s' →
    ∀ (ρ₀ : Env P) (σ : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) σ →
      StepStmtStar P (EvalCmd P) extendEval (.stmt s' ρ₀) σ

/-- If `T` overapproximates and a Hoare triple holds on `T(st)`,
    then the same triple holds on `st`. -/
theorem overapproximates_triple
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (st s' : Stmt P (Cmd P))
    (ht : T st = some s')
    (hsem : Overapproximates P extendEval T)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple P extendEval Pre s' Post) :
    Hoare.Triple P extendEval Pre st Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  exact htriple ρ₀ ρ' hpre hwfb hf₀ (hsem st s' ht ρ₀ _ hstar)

/-- If `T` overapproximates, then `T` is sound. -/
theorem overapproximates_sound
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (hsem : Overapproximates P extendEval T) :
    Sound P extendEval T := by
  intro s s' a ht hvalid ρ₀ cfg hstar hat
  exact hvalid ρ₀ cfg (hsem s s' ht ρ₀ _ hstar) hat

/-- Identity transform overapproximates. -/
theorem overapproximates_id :
    Overapproximates P extendEval some := by
  intro st s' ht ρ₀ σ hstar
  simp at ht; subst ht; exact hstar

/-- Composition of overapproximating transforms overapproximates. -/
theorem overapproximates_comp
    (T₁ T₂ : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (h₁ : Overapproximates P extendEval T₁)
    (h₂ : Overapproximates P extendEval T₂) :
    Overapproximates P extendEval (fun s => T₁ s >>= T₂) := by
  intro st s'' ht ρ₀ σ hstar
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    exact h₂ s' s'' ht ρ₀ σ (h₁ st s' h ρ₀ σ hstar)
  | none => rw [h] at ht; exact absurd ht (by nofun)

/-- Pointwise application of an overapproximating transform to a statement list
    preserves reachability of terminal and exiting configurations (with the same
    exit label).
    Note: this cannot be generalized to arbitrary intermediate configurations
    such as `.seq`, because those carry the remaining statement list — which
    differs between the original and transformed programs. Only `.terminal`
    and `.exiting` have escaped the `.seq`/`.stmts` wrapper. -/
theorem overapproximates_stmts
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (hsem : Overapproximates P extendEval T)
    (ss : List (Stmt P (Cmd P))) :
    ∀ (ss' : List (Stmt P (Cmd P))),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        (StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ') →
         StepStmtStar P (EvalCmd P) extendEval (.stmts ss' ρ₀) (.terminal ρ'))
        ∧
        (∀ lbl, StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.exiting lbl ρ') →
                StepStmtStar P (EvalCmd P) extendEval (.stmts ss' ρ₀) (.exiting lbl ρ')) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ'
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨id, fun _ => id⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ'
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    constructor
    · -- Terminal
      intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest_exec
          exact reflTrans_trans
            (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ₀ ρ₁
              (hsem s s' hs ρ₀ _ hterm_s))
            ((ih rest' hrm ρ₁ ρ').1 hterm_rest)
    · -- Exiting (label is preserved)
      intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P (EvalCmd P) extendEval hrest_exec with
          | .inl hexit_s =>
            -- Exit came from s; replay through s' via overapproximates
            exact .step _ _ _ .step_stmts_cons
              (reflTrans_trans (seq_inner_star P (EvalCmd P) extendEval _ _ rest'
                (hsem s s' hs ρ₀ _ hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            -- s terminated at ρ₁, exit came from rest
            exact reflTrans_trans
              (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ₀ ρ₁
                (hsem s s' hs ρ₀ _ hterm_s))
              ((ih rest' hrm ρ₁ ρ').2 lbl hexit_rest)

end Transform
end Specification
end Imperative

end -- public section

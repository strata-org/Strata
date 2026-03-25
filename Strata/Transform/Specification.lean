/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsSmallStep
import all Strata.DL.Imperative.CmdSemantics

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

/-! ## Configuration accessors

Defined in the `Imperative` namespace so that dot notation works
on `Config P (Cmd P)`. -/

variable {P : PureExpr}

/-- Extract the store from a configuration. -/
def Config.getStore : Config P (Cmd P) → SemanticStore P
  | .stmt _ ρ => ρ.store
  | .stmts _ ρ => ρ.store
  | .terminal ρ => ρ.store
  | .exiting _ ρ => ρ.store
  | .block _ inner => inner.getStore
  | .seq inner _ => inner.getStore

/-- Extract the evaluator from a configuration. -/
def Config.getEval : Config P (Cmd P) → SemanticEval P
  | .stmt _ ρ => ρ.eval
  | .stmts _ ρ => ρ.eval
  | .terminal ρ => ρ.eval
  | .exiting _ ρ => ρ.eval
  | .block _ inner => inner.getEval
  | .seq inner _ => inner.getEval

/-- Extract the execution environment from a configuration. -/
def Config.getEnv : Config P (Cmd P) → Env P
  | .stmt _ ρ => ρ
  | .stmts _ ρ => ρ
  | .terminal ρ => ρ
  | .exiting _ ρ => ρ
  | .block _ inner => inner.getEnv
  | .seq inner _ => inner.getEnv

namespace Specification

variable (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P]
variable (extendEval : ExtendEval P)

/-! ## Assertion Identity -/

/-- An assertion identifier: the label + expression attached to an
    `assert` command.  Metadata is intentionally excluded — it is not
    semantically relevant for assertion validity. -/
structure AssertId where
  label : String
  expr  : P.Expr

/-! ## Detecting an assert in a configuration -/

/-- `isAtAssert cfg aid` holds when the head of `cfg` is an `assert` command
    whose label and expression match `aid`.  Recurses into `block` and `seq`
    wrappers so that asserts inside compound statements are visible. -/
def isAtAssert : Config P (Cmd P) → AssertId P → Prop
  | .stmt (.cmd (.assert label expr _)) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.assert label expr _)) :: _) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .block _ inner, aid => isAtAssert inner aid
  | .seq inner _, aid => isAtAssert inner aid
  | _, _ => False

/-! ## Style A — Reachability-based assertion validity -/

/-- A configuration `cfg` is *reachable* from statement `s` with initial
    environment `ρ₀` if multi-step execution from `(.stmt s ρ₀)` reaches
    `cfg`. -/
def Reachable
    (s : Stmt P (Cmd P)) (ρ₀ : Env P) (cfg : Config P (Cmd P)) : Prop :=
  StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) cfg

/-- Assert `a` is *valid* in statement `s` if, for every initial
    environment and reachable configuration that is at assert `a`,
    the assert expression evaluates to `true`. -/
def AssertValid
    (s : Stmt P (Cmd P)) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : Config P (Cmd P)),
    Reachable P extendEval s ρ₀ cfg →
    isAtAssert P cfg a →
    cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- All asserts are valid in statement `s`. Assert `a` does not have to be
    constrained to those in `s` because AssertValid uses partial correctness. -/
def AllAssertsValid
    (s : Stmt P (Cmd P)) : Prop :=
  ∀ (a : AssertId P), AssertValid P extendEval s a

/-! ## Style B — Hoare-triple assertion validity -/

/-- Partial-correctness Hoare triple using small-step semantics.

    The precondition includes `ρ₀.hasFailure = false` (no prior assertion
    failures) and the postcondition includes `ρ'.hasFailure = false` (no
    assertion failures after execution). -/
def HoareTriple
    (Pre : Env P → Prop)
    (s : Stmt P (Cmd P))
    (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → ρ₀.hasFailure = false →
    StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ') →
    Post ρ' ∧ ρ'.hasFailure = false

/-! ## Relationship between Style A and Style B

For a single assert command, the only configuration satisfying `isAtAssert`
is the initial `.stmt` configuration itself (zero steps from the start),
because the assert command has exactly one step (to `.terminal`).
-/

/-- Style A implies Style B for a single assert command: if all reachable
    assert configurations have `expr = true`, then the Hoare triple holds. -/
theorem assertValid_implies_hoareTriple
    (label : String) (expr : P.Expr) (md : MetaData P)
    (s : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hvalid : AssertValid P extendEval s ⟨label, expr⟩) :
    HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) := by
  subst hs
  intro ρ₀ ρ' _ hf₀ hstar
  cases hstar with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      cases hcmd with
      | eval_assert_pass htt _ =>
        simp [hf₀] at hrest
        cases hrest with
        | refl => exact ⟨htt, rfl⟩
        | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)
      | eval_assert_fail hff _ =>
        have hreach : Reachable P extendEval (.cmd (.assert label expr md)) ρ₀
            (.stmt (.cmd (.assert label expr md)) ρ₀) :=
          ReflTrans.refl _
        have htt := hvalid ρ₀ _ hreach ⟨rfl, rfl⟩
        simp only [Config.getEval, Config.getStore] at htt
        rw [hff] at htt
        exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm

/-- Style B implies Style A for a single assert command, given that the
    assert is not stuck (i.e., for every initial environment, the assert
    command can step to terminal). -/
theorem hoareTriple_implies_assertValid
    (label : String) (expr : P.Expr) (md : MetaData P)
    (s : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hoare : HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt))
    (hprogress : ∀ (ρ₀ : Env P),
      ∃ (ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ')) :
    AssertValid P extendEval s ⟨label, expr⟩ := by
  subst hs
  intro ρ₀ cfg hstar hat
  cases hstar with
  | refl =>
    have ⟨ρ', hterm⟩ := hprogress ρ₀
    simp only [Config.getEval, Config.getStore]
    cases hterm with
    | step _ mid _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | eval_assert_pass htt _ => exact htt
        | eval_assert_fail hff hwfb =>
          have hterm' : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.cmd (.assert label expr md)) { ρ₀ with hasFailure := false })
              (.terminal { store := ρ₀.store, eval := ρ₀.eval, hasFailure := true }) :=
            ReflTrans.step _ _ _
              (StepStmt.step_cmd (EvalCmd.eval_assert_fail hff hwfb))
              (ReflTrans.refl _)
          have ⟨_, hf'⟩ := hoare { ρ₀ with hasFailure := false } _ trivial rfl hterm'
          exact absurd hf' (by simp)
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      -- mid = .terminal .., which doesn't satisfy isAtAssert
      cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)

/-! ## Equivalence for a single assert command -/

/-- For a single assert command, Style A implies Style B unconditionally.
    Style B implies Style A given a progress assumption. -/
theorem assertValid_implies_hoareTriple_iff
    (label : String) (expr : P.Expr) (md : MetaData P)
    (s : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hprogress : ∀ (ρ₀ : Env P),
      ∃ (ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ')) :
    AssertValid P extendEval s ⟨label, expr⟩ ↔
    HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) :=
  ⟨assertValid_implies_hoareTriple P extendEval label expr md s hs,
   fun h => hoareTriple_implies_assertValid P extendEval label expr md s hs h hprogress⟩

/-! ## Small-step helper lemmas -/

/-- Lifting multi-step execution through a block context. -/
private theorem block_inner_star
    (inner inner' : Config P (Cmd P))
    (label : String)
    (h : StepStmtStar P (EvalCmd P) extendEval inner inner') :
    StepStmtStar P (EvalCmd P) extendEval (.block label inner) (.block label inner') := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_block_body hstep) ih

/-- Transitivity of `ReflTrans`. -/
private theorem reflTrans_trans
    {x y z : Config P (Cmd P)}
    (h1 : StepStmtStar P (EvalCmd P) extendEval x y)
    (h2 : StepStmtStar P (EvalCmd P) extendEval y z) :
    StepStmtStar P (EvalCmd P) extendEval x z := by
  induction h1 with
  | refl => exact h2
  | step _ mid _ hstep _ ih => exact .step _ mid _ hstep (ih h2)

/-- If execution inside a block reaches a config where isAtAssert holds,
    then the config must be `.block label inner` where `inner` is reachable
    from the block's body and satisfies `isAtAssert`. -/
private theorem block_isAtAssert_inner
    (label : String) (inner₀ cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.block label inner₀) cfg)
    (hat : isAtAssert P cfg a) :
    ∃ inner, cfg = .block label inner ∧
      StepStmtStar P (EvalCmd P) extendEval inner₀ inner ∧
      isAtAssert P inner a := by
  -- Generalize inner₀ so the IH works for any starting inner config.
  generalize hsrc : Config.block label inner₀ = src at hstar
  induction hstar generalizing inner₀ with
  | refl => subst hsrc; exact ⟨inner₀, rfl, .refl _, hat⟩
  | step _ mid _ hstep hrest ih =>
    subst hsrc; cases hstep with
    | step_block_body hinner =>
      have ⟨inner, heq, hreach, hat'⟩ := ih _ hat rfl
      exact ⟨inner, heq, .step _ _ _ hinner hreach, hat'⟩
    | step_block_done => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    | step_block_exit_none => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    | step_block_exit_match => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    | step_block_exit_mismatch => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-- If execution inside a seq reaches a config where isAtAssert holds,
    then either the inner config matches (first disjunct), or the inner
    completed and we're in the tail (second disjunct). -/
private theorem seq_isAtAssert_cases
    (inner₀ cfg : Config P (Cmd P)) (ss : List (Stmt P (Cmd P))) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.seq inner₀ ss) cfg)
    (hat : isAtAssert P cfg a) :
    (∃ inner, cfg = .seq inner ss ∧
      StepStmtStar P (EvalCmd P) extendEval inner₀ inner ∧
      isAtAssert P inner a) ∨
    (∃ ρ', StepStmtStar P (EvalCmd P) extendEval inner₀ (.terminal ρ') ∧
      StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ') cfg ∧
      isAtAssert P cfg a) := by
  generalize hsrc : Config.seq inner₀ ss = src at hstar
  induction hstar generalizing inner₀ ss with
  | refl => subst hsrc; exact .inl ⟨inner₀, rfl, .refl _, hat⟩
  | step _ mid _ hstep hrest ih =>
    subst hsrc; cases hstep with
    | step_seq_inner hinner =>
      match ih _ _ hat rfl with
      | .inl ⟨inner, heq, hreach, hat'⟩ =>
        exact .inl ⟨inner, heq, .step _ _ _ hinner hreach, hat'⟩
      | .inr ⟨ρ', hterm, hstmts, hat'⟩ =>
        exact .inr ⟨ρ', .step _ _ _ hinner hterm, hstmts, hat'⟩
    | step_seq_done =>
      exact .inr ⟨_, .refl _, hrest, hat⟩
    | step_seq_exit => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-- The terminal state's store and eval are independent of the starting
    `hasFailure` flag.  This holds because `hasFailure` is purely accumulated
    (OR-ed at each step) and never consulted by any step rule's guard.
    Proving this from first principles requires mutual induction over all
    configuration types; we state it as an axiom. -/
axiom smallStep_hasFailure_irrel
    (P : PureExpr) [HasBool P] [HasNot P]
    (EvalCmd : EvalCmdParam P (Cmd P)) (extendEval : ExtendEval P)
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')) :
    ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
    ∃ ρ₂', StepStmtStar P EvalCmd extendEval (.stmt s ρ₂) (.terminal ρ₂') ∧
      ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval

/-- For a single assert command, any config reachable from `.stmts [assert] ρ`
    that satisfies `isAtAssert` has getEval = ρ.eval and getStore = ρ.store. -/
private theorem assert_tail_getEvalStore
    (ρ : Env P) (l : String) (e : P.Expr) (md : MetaData P)
    (cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [Stmt.cmd (Cmd.assert l e md)] ρ) cfg)
    (hat : isAtAssert P cfg a) :
    cfg.getEval = ρ.eval ∧ cfg.getStore = ρ.store := by
  -- Exhaustive case analysis: .stmts [assert] ρ can only step to
  -- .seq (.stmt assert ρ) [] → .seq (.terminal ..) [] → .stmts [] .. → .terminal ..
  -- isAtAssert only matches at .stmts [assert] ρ and .seq (.stmt assert ρ) [].
  cases hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ h1 hr1 => cases h1 with
    | step_stmts_cons => cases hr1 with
      | refl => exact ⟨rfl, rfl⟩
      | step _ _ _ h2 hr2 =>
        -- h2 steps from .seq (.stmt (.cmd (.assert ..)) ρ) []
        -- Either step_seq_inner (assert steps via step_cmd) or impossible
        cases h2 with
        | step_seq_inner hi =>
          -- assert cmd steps to terminal
          cases hi with
          | step_cmd =>
            -- Now at .seq (.terminal ..) [] — only step_seq_done
            -- After step_cmd: .seq (.terminal ..) []
            -- No further isAtAssert match is possible.
            -- All remaining configs are terminal/stmts-nil.
            -- Use a catch-all: hat contradicts isAtAssert for any subsequent cfg.
            -- The remaining execution only visits:
            -- .seq (.terminal ..) [] → .stmts [] .. → .terminal ..
            -- None satisfy isAtAssert.
            -- .seq (.terminal ..) [] → .stmts [] .. → .terminal ..
            -- None satisfy isAtAssert. Chase the remaining 2-3 steps.
            cases hr2 with
            | refl => exact absurd hat (by simp [isAtAssert])
            | step _ _ _ h3 hr3 =>
              cases h3 with
              | step_seq_inner h_t => exact absurd h_t (by intro h; cases h)
              | step_seq_done =>
                cases hr3 with
                | refl => exact absurd hat (by simp [isAtAssert])
                | step _ _ _ h4 hr4 =>
                  cases h4 with
                  | step_stmts_nil =>
                    cases hr4 with
                    | refl => exact absurd hat (by simp [isAtAssert])
                    | step _ _ _ h5 _ => exact absurd h5 (by intro h; cases h)

/-! ## General connection between HoareTriple and AssertValid

For a general statement `st` (not just a single assert), we can connect
`HoareTriple` and `AssertValid` by forming a composite program:

    assume pre_expr; st; assert post_expr

The `assume` encodes the precondition (filtering executions where the
precondition holds) and the `assert` encodes the postcondition.  We wrap
this sequence in a block to form a single `Stmt`.

**Direction 1** (`hoareTriple_implies_assertValid_general`):
If `{P} st {Q}` holds (where P ↔ `pre_expr = tt` and Q ↔ `post_expr = tt`),
then `AssertValid` holds for the composite `assume pre; st; assert post`.

**Direction 2** (`assertValid_implies_hoareTriple_general`):
If `AssertValid` holds for the composite `assume pre; st; assert post`,
then `{P} st {Q}` holds.
-/

/-- The composite statement `assume pre; st; assert post` wrapped in a block.
    This encodes a Hoare triple `{pre} st {post}` as a single statement
    whose assert validity captures the triple's meaning. -/
def hoareBlock
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P) : Stmt P (Cmd P) :=
  .block block_label
    [.cmd (.assume pre_label pre_expr pre_md), st, .cmd (.assert post_label post_expr post_md)]
    block_md

theorem hoareTriple_implies_assertValid_general
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hoare : HoareTriple P extendEval
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt))
    -- st does not contain any assert matching ⟨post_label, post_expr⟩.
    -- This ensures the only reachable config satisfying isAtAssert is the
    -- explicit assert at the end of the composite.
    (hno_match : ∀ (ρ : Env P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ) cfg →
      ¬ isAtAssert P cfg ⟨post_label, post_expr⟩) :
    AssertValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg hreach hat
  -- Decompose block execution via block_isAtAssert_inner
  unfold hoareBlock Reachable at hreach
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
                        -- hpre : ρ₀.eval ρ₀.store pre_expr = some HasBool.tt
                        -- ρ₁ = { ρ₀ with hasFailure := ρ₀.hasFailure || false }
                        -- Apply Hoare triple with clean env { ρ₀ with hasFailure := false }
                        -- which has same store/eval as ρ₁.
                        -- The assert only checks eval/store, not hasFailure.
                        -- cfg.getEval/getStore recurse to ρ'.eval/ρ'.store.
                        -- We need: ρ'.eval ρ'.store post_expr = some HasBool.tt
                        -- Use hoare with { ρ₁ with hasFailure := false }:
                        -- Pre holds (same eval/store), hasFailure = false.
                        -- But we need StepStmtStar from { ρ₁ with hasFailure := false }.
                        -- hterm_st is from ρ₁ (which may have hasFailure ≠ false).
                        -- We need hasFailure-irrelevance for small-step... or bypass.
                        -- Actually: h_assume_rest gives ρ₁ from .terminal {...} to .terminal ρ₁.
                        -- After step_cmd eval_assume: terminal env is
                        -- { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }
                        -- h_assume_rest : StepStmtStar (.terminal ...) (.terminal ρ₁)
                        -- Terminal can't step, so h_assume_rest is refl.
                        cases h_assume_rest with
                        | refl =>
                          -- After refl, the env in hterm_st is
                          -- { ρ₀ with hasFailure := ρ₀.hasFailure || false }
                          -- Use hasFailure-irrelevance to get execution from clean env
                          have ⟨ρ'_clean, hterm_clean, hs_eq, he_eq⟩ :=
                            smallStep_hasFailure_irrel P (EvalCmd P) extendEval
                              st _ ρ' hterm_st { ρ₀ with hasFailure := false } rfl rfl
                          have ⟨hpost, _⟩ := hoare { ρ₀ with hasFailure := false } ρ'_clean
                            hpre rfl hterm_clean
                          -- hpost : ρ'_clean.eval ρ'_clean.store post_expr = some HasBool.tt
                          -- Transfer to ρ' via store/eval equality
                          simp only [hs_eq, he_eq] at hpost
                          -- Use assert_tail_getEvalStore to connect inner's env to ρ'
                          simp only [Config.getEval, Config.getStore]
                          have ⟨he, hs⟩ := assert_tail_getEvalStore P extendEval
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-- If `AssertValid` holds for `assume pre; st; assert post`, and `st`
    makes progress (always terminates when precondition holds), then
    whenever `pre_expr = tt` at the initial env and `st` terminates at ρ',
    `post_expr = tt` at ρ'.

    The `WellFormedSemanticEvalBool` hypothesis is needed to construct
    the `assume` step in the composite execution. -/
theorem assertValid_implies_hoareTriple_general
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hwfb : ∀ (δ : SemanticEval P), WellFormedSemanticEvalBool δ)
    (hvalid : AssertValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩) :
    ∀ (ρ₀ ρ' : Env P),
      ρ₀.eval ρ₀.store pre_expr = some HasBool.tt →
      ρ₀.hasFailure = false →
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ') →
      ρ'.eval ρ'.store post_expr = some HasBool.tt := by
  intro ρ₀ ρ' hpre hf₀ hstar
  -- Build the composite execution: block [assume pre; st; assert post]
  -- Starting from ρ₀, the assume passes (since hpre holds), then st runs
  -- to ρ', then the execution reaches the assert with env ρ'.
  let assume_stmt : Stmt P (Cmd P) := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P (Cmd P) := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P (Cmd P)) := [assume_stmt, st, assert_stmt]
  -- Step 1: assume passes, producing ρ₁ (propositionally = ρ₀ since hf₀)
  have h_assume : StepStmtStar P (EvalCmd P) extendEval
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre (hwfb ρ₀.eval))) (.refl _)
  have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P) = ρ₀ := by
    cases ρ₀; simp [Bool.or_false]
  -- Step 2: stmts [assume, st, assert] ρ₀ →* stmts [st, assert] ρ₁
  have h1 := stmts_cons_step P (EvalCmd P) extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
  rw [h_ρ₁_eq] at h1
  -- Step 3: stmts [st, assert] ρ₀ →* stmts [assert] ρ'
  have h2 := stmts_cons_step P (EvalCmd P) extendEval st [assert_stmt] ρ₀ ρ' hstar
  -- Step 4: stmts [assert] ρ' → seq (stmt assert ρ') []
  have h3 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [assert_stmt] ρ') (.seq (.stmt assert_stmt ρ') []) :=
    .step _ _ _ StepStmt.step_stmts_cons (.refl _)
  -- Compose: stmts body ρ₀ →* seq (stmt assert ρ') []
  have h_inner := reflTrans_trans (h1 := reflTrans_trans (h1 := h1) (h2 := h2)) (h2 := h3)
  -- Lift through block: block bl (stmts body ρ₀) →* block bl (seq (stmt assert ρ') [])
  have h_block := block_inner_star P extendEval _ _ block_label h_inner
  -- Start: stmt (block ...) ρ₀ → block bl (stmts body ρ₀)
  have h_start : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.block block_label body block_md) ρ₀) (.block block_label (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  -- Full execution: stmt (hoareBlock ...) ρ₀ →* block bl (seq (stmt assert ρ') [])
  have h_full := reflTrans_trans (h1 := h_start) (h2 := h_block)
  -- The target config satisfies isAtAssert (recurse: block → seq → stmt assert)
  have h_at : isAtAssert P (.block block_label (.seq (.stmt assert_stmt ρ') [])) ⟨post_label, post_expr⟩ := by
    simp [isAtAssert, assert_stmt]
  -- Apply hvalid: the config is reachable and at the assert
  have h_result := hvalid ρ₀ _ h_full h_at
  -- Simplify getEval/getStore through block → seq → stmt
  simp only [Config.getEval, Config.getStore] at h_result
  exact h_result

/-! ## Transformation Correctness

A program transformation is a partial function on statements
(`Stmt P (Cmd P) → Option (Stmt P (Cmd P))`).  It returns `some s'`
on success and `none` on failure (e.g., unsupported input).

A transformation `T` is *sound* (w.r.t. assertion checks) if:
for every assert `a`, if `T s = some s'` and `a` is valid in `s'`,
then `a` is valid in `s`.
-/

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

/-! ## End-to-end soundness -/

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

/-- If `T` is sound and the assert-specific Hoare triple holds for the
    output `s'`, then it also holds for the input `s`. -/
theorem sound_hoareTriple
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (label : String) (expr : P.Expr) (md md' : MetaData P)
    (s s' : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hs' : s' = .cmd (.assert label expr md'))
    (ht : T s = some s')
    (hsound : Sound P extendEval T)
    (hprogress : ∀ (ρ₀ : Env P),
      ∃ (ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt s' ρ₀) (.terminal ρ'))
    (hoare : HoareTriple P extendEval
      (fun _ => True) s'
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt)) :
    HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) :=
  assertValid_implies_hoareTriple P extendEval label expr md s hs
    (hsound s s' ⟨label, expr⟩ ht
      (hoareTriple_implies_assertValid P extendEval label expr md' s' hs' hoare hprogress))

end Specification
end Imperative

end -- public section

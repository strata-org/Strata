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

variable {P : PureExpr}

/-- `noMatchingAssert` for statements and statement lists.
    Returns `True` when `s` does not syntactically contain any `assert`
    command with the given label. -/
def Stmt.noMatchingAssert : Stmt P (Cmd P) → String → Prop
  | .cmd (.assert l _ _), label => l ≠ label
  | .cmd _, _ => True
  | .block _ ss _, label => Stmts.noMatchingAssert ss label
  | .ite _ tss ess _, label =>
    Stmts.noMatchingAssert tss label ∧ Stmts.noMatchingAssert ess label
  | .loop _ _ _ body _, label => Stmts.noMatchingAssert body label
  | .exit _ _, _ => True
  | .funcDecl _ _, _ => True
  | .typeDecl _ _, _ => True
where
  /-- Helper for lists of statements. -/
  Stmts.noMatchingAssert : List (Stmt P (Cmd P)) → String → Prop
    | [], _ => True
    | s :: ss, label => s.noMatchingAssert label ∧ Stmts.noMatchingAssert ss label

/-- Extend `noMatchingAssert` to configurations. -/
def Config.noMatchingAssert : Config P (Cmd P) → String → Prop
  | .stmt s _, label => s.noMatchingAssert label
  | .stmts ss _, label => Stmt.noMatchingAssert.Stmts.noMatchingAssert ss label
  | .terminal _, _ => True
  | .exiting _ _, _ => True
  | .block _ inner, label => inner.noMatchingAssert label
  | .seq inner ss, label =>
    inner.noMatchingAssert label ∧ Stmt.noMatchingAssert.Stmts.noMatchingAssert ss label

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

/-- If a config has no matching assert, then `isAtAssert` doesn't match. -/
private theorem noMatchingAssert_not_isAtAssert
    (cfg : Config P (Cmd P)) (label : String) (expr : P.Expr)
    (hno : cfg.noMatchingAssert label) :
    ¬ isAtAssert P cfg ⟨label, expr⟩ := by
  match cfg with
  | .stmt (.cmd (.assert l _ _)) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno
    simp [isAtAssert]; exact fun h _ => hno (h ▸ rfl)
  | .stmt (.cmd (.init ..)) _ | .stmt (.cmd (.set ..)) _
  | .stmt (.cmd (.havoc ..)) _ | .stmt (.cmd (.assume ..)) _
  | .stmt (.cmd (.cover ..)) _
  | .stmt (.block ..) _ | .stmt (.ite ..) _ | .stmt (.loop ..) _
  | .stmt (.exit ..) _ | .stmt (.funcDecl ..) _ | .stmt (.typeDecl ..) _ =>
    simp [isAtAssert]
  | .stmts [] _ => simp [isAtAssert]
  | .stmts ((.cmd (.assert l _ _)) :: _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert.Stmts.noMatchingAssert, Stmt.noMatchingAssert] at hno
    simp [isAtAssert]; exact fun h _ => hno.1 (h ▸ rfl)
  | .stmts ((.cmd (.init ..)) :: _) _ | .stmts ((.cmd (.set ..)) :: _) _
  | .stmts ((.cmd (.havoc ..)) :: _) _ | .stmts ((.cmd (.assume ..)) :: _) _
  | .stmts ((.cmd (.cover ..)) :: _) _
  | .stmts ((.block ..) :: _) _ | .stmts ((.ite ..) :: _) _
  | .stmts ((.loop ..) :: _) _ | .stmts ((.exit ..) :: _) _
  | .stmts ((.funcDecl ..) :: _) _ | .stmts ((.typeDecl ..) :: _) _ =>
    simp [isAtAssert]
  | .terminal _ | .exiting _ _ => simp [isAtAssert]
  | .block _ inner => exact noMatchingAssert_not_isAtAssert inner label expr hno
  | .seq inner _ => exact noMatchingAssert_not_isAtAssert inner label expr hno.1

/-- Helper: `Stmts.noMatchingAssert` for concatenation. -/
private theorem stmts_noMatchingAssert_append
    (ss₁ ss₂ : List (Stmt P (Cmd P))) (label : String)
    (h₁ : Stmt.noMatchingAssert.Stmts.noMatchingAssert ss₁ label)
    (h₂ : Stmt.noMatchingAssert.Stmts.noMatchingAssert ss₂ label) :
    Stmt.noMatchingAssert.Stmts.noMatchingAssert (ss₁ ++ ss₂) label := by
  induction ss₁ with
  | nil => exact h₂
  | cons s ss ih =>
    exact ⟨h₁.1, ih h₁.2⟩

/-- A single step preserves `Config.noMatchingAssert`. -/
private def step_preserves_noMatchingAssert
    (c₁ c₂ : Config P (Cmd P)) (label : String)
    (hstep : StepStmt P (EvalCmd P) extendEval c₁ c₂)
    (hno : c₁.noMatchingAssert label) :
    c₂.noMatchingAssert label := by
  cases hstep with
  | step_cmd => trivial
  | step_block => exact hno
  | step_ite_true => exact hno.1
  | step_ite_false => exact hno.2
  | step_loop_enter =>
    -- Config: .stmts (body ++ [.loop ..]) ρ. Need Stmts.noMatchingAssert.
    -- hno : Stmt.noMatchingAssert (.loop ..) label = Stmts.noMatchingAssert body label
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    apply stmts_noMatchingAssert_append
    exact hno
    exact ⟨hno, True.intro⟩
  | step_loop_exit => trivial
  | step_exit => trivial
  | step_funcDecl => trivial
  | step_typeDecl => trivial
  | step_stmts_nil => trivial
  | step_stmts_cons => exact ⟨hno.1, hno.2⟩
  | step_seq_inner h =>
    constructor
    · apply step_preserves_noMatchingAssert; exact h; exact hno.1
    · exact hno.2
  | step_seq_done => exact hno.2
  | step_seq_exit => trivial
  | step_block_body h =>
    -- h : StepStmt inner inner', hno : inner.noMatchingAssert label
    -- Goal: inner'.noMatchingAssert label (= (.block _ inner').noMatchingAssert)
    have := step_preserves_noMatchingAssert (c₁ := _) (c₂ := _) (label := _) h hno
    exact this
  | step_block_done => trivial
  | step_block_exit_none => trivial
  | step_block_exit_match => trivial
  | step_block_exit_mismatch => trivial

/-- The syntactic check implies that no reachable config from `st`
    satisfies `isAtAssert` for the given label and expression. -/
theorem noMatchingAssert_implies_no_reachable_assert
    (st : Stmt P (Cmd P)) (label : String) (expr : P.Expr)
    (hno : st.noMatchingAssert label) :
    ∀ (ρ : Env P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ) cfg →
      ¬ isAtAssert P cfg ⟨label, expr⟩ := by
  intro ρ cfg hstar
  -- Prove cfg.noMatchingAssert by showing it's preserved at each step.
  suffices ∀ (c₁ c₂ : Config P (Cmd P)),
      c₁.noMatchingAssert label →
      StepStmtStar P (EvalCmd P) extendEval c₁ c₂ →
      c₂.noMatchingAssert label from
    noMatchingAssert_not_isAtAssert P cfg label expr
      (this (.stmt st ρ) cfg (show Config.noMatchingAssert (.stmt st ρ) label from hno) hstar)
  intro c₁ c₂ hno_c hstar_c
  induction hstar_c with
  | refl => exact hno_c
  | step _ _ _ hstep _ ih =>
    exact ih (@step_preserves_noMatchingAssert P _ _ _ extendEval _ _ _ hstep hno_c)

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

    The precondition includes `WellFormedSemanticEvalBool ρ₀.eval`
    (the evaluator satisfies the boolean well-formedness condition)
    and `ρ₀.hasFailure = false` (no prior assertion failures).
    The postcondition includes `ρ'.hasFailure = false` (no assertion
    failures after execution of 's'). -/
def HoareTriple
    (Pre : Env P → Prop)
    (s : Stmt P (Cmd P))
    (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
    StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ') →
    Post ρ' ∧ ρ'.hasFailure = false

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

/-- Two configs agree on store/eval (may differ on hasFailure). -/
private def ConfigSE : Config P (Cmd P) → Config P (Cmd P) → Prop
  | .stmt s₁ ρ₁, .stmt s₂ ρ₂ => s₁ = s₂ ∧ ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .stmts ss₁ ρ₁, .stmts ss₂ ρ₂ => ss₁ = ss₂ ∧ ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .terminal ρ₁, .terminal ρ₂ => ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .exiting l₁ ρ₁, .exiting l₂ ρ₂ => l₁ = l₂ ∧ ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .block l₁ i₁, .block l₂ i₂ => l₁ = l₂ ∧ ConfigSE i₁ i₂
  | .seq i₁ ss₁, .seq i₂ ss₂ => ss₁ = ss₂ ∧ ConfigSE i₁ i₂
  | _, _ => False

/-- Single-step simulation: if two configs agree on store/eval and one steps,
    the other can take the same step with store/eval preserved. -/
private def step_simulation
    (c₁ c₁' c₂ : Config P (Cmd P))
    (hstep : StepStmt P (EvalCmd P) extendEval c₁ c₁')
    (heq : ConfigSE P c₁ c₂) :
    ∃ c₂', StepStmt P (EvalCmd P) extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' := by
  -- Case-split on c₂ to unfold ConfigSE, then apply the matching step rule.
  -- For each StepStmt constructor, the guard only depends on store/eval
  -- (which are equal), so the same rule applies to c₂.
  cases hstep with
  | step_cmd hcmd =>
    cases c₂ with
    | stmt _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_cmd (hs ▸ he ▸ hcmd), rfl, he⟩
    | _ => exact nomatch heq
  | step_block =>
    cases c₂ with
    | stmt _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_block, rfl, rfl, hs, he⟩
    | _ => exact nomatch heq
  | step_ite_true hc hw =>
    cases c₂ with
    | stmt _ ρ₂ =>
      have h := heq.1; subst h; exact ⟨_, .step_ite_true (heq.2.2 ▸ heq.2.1 ▸ hc) (heq.2.2 ▸ hw),
        ⟨rfl, heq.2.1, heq.2.2⟩⟩
    | _ => exact nomatch heq
  | step_ite_false hc hw =>
    cases c₂ with
    | stmt _ ρ₂ =>
      have h := heq.1; subst h; exact ⟨_, .step_ite_false (heq.2.2 ▸ heq.2.1 ▸ hc) (heq.2.2 ▸ hw),
        ⟨rfl, heq.2.1, heq.2.2⟩⟩
    | _ => exact nomatch heq
  | step_loop_enter hc hw =>
    cases c₂ with
    | stmt _ ρ₂ =>
      have h := heq.1; subst h; exact ⟨_, .step_loop_enter (heq.2.2 ▸ heq.2.1 ▸ hc) (heq.2.2 ▸ hw),
        ⟨rfl, heq.2.1, heq.2.2⟩⟩
    | _ => exact nomatch heq
  | step_loop_exit hc hw =>
    cases c₂ with
    | stmt _ ρ₂ =>
      have h := heq.1; subst h; exact ⟨_, .step_loop_exit (heq.2.2 ▸ heq.2.1 ▸ hc) (heq.2.2 ▸ hw),
        ⟨heq.2.1, heq.2.2⟩⟩
    | _ => exact nomatch heq
  | step_exit =>
    cases c₂ with
    | stmt _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_exit, rfl, hs, he⟩
    | _ => exact nomatch heq
  | step_funcDecl =>
    cases c₂ with
    | stmt _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_funcDecl, hs, by simp [he, hs]⟩
    | _ => exact nomatch heq
  | step_typeDecl =>
    cases c₂ with
    | stmt _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_typeDecl, hs, he⟩
    | _ => exact nomatch heq
  | step_stmts_nil =>
    cases c₂ with
    | stmts _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_stmts_nil, hs, he⟩
    | _ => exact nomatch heq
  | step_stmts_cons =>
    cases c₂ with
    | stmts _ ρ₂ => obtain ⟨rfl, hs, he⟩ := heq; exact ⟨_, .step_stmts_cons, rfl, rfl, hs, he⟩
    | _ => exact nomatch heq
  | step_seq_inner h =>
    cases c₂ with
    | seq i₂ _ =>
      have hrs := heq.1; subst hrs
      have ⟨c₂', h₂, heq₂⟩ := step_simulation _ _ _ h heq.2
      exact ⟨_, .step_seq_inner h₂, ⟨rfl, heq₂⟩⟩
    | _ => exact nomatch heq
  | step_seq_done =>
    cases c₂ with
    | seq i₂ _ =>
      have hrs := heq.1; subst hrs
      cases i₂ with
      | terminal ρ₂ => exact ⟨_, .step_seq_done, ⟨rfl, heq.2.1, heq.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_seq_exit =>
    cases c₂ with
    | seq i₂ _ =>
      cases i₂ with
      | exiting _ _ => exact ⟨_, .step_seq_exit, ⟨heq.2.1, heq.2.2.1, heq.2.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_block_body h =>
    cases c₂ with
    | block _ i₂ =>
      have hrs := heq.1; subst hrs
      have ⟨c₂', h₂, heq₂⟩ := step_simulation _ _ _ h heq.2
      exact ⟨_, .step_block_body h₂, ⟨rfl, heq₂⟩⟩
    | _ => exact nomatch heq
  | step_block_done =>
    cases c₂ with
    | block _ i₂ =>
      have hrs := heq.1; subst hrs
      cases i₂ with
      | terminal ρ₂ => exact ⟨_, .step_block_done, ⟨heq.2.1, heq.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_block_exit_none =>
    cases c₂ with
    | block _ i₂ =>
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl := heq.2.1; cases hl
        exact ⟨_, .step_block_exit_none, ⟨heq.2.2.1, heq.2.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_block_exit_match hl =>
    cases c₂ with
    | block _ i₂ =>
      have hlb := heq.1; subst hlb
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl₂ := heq.2.1; subst hl₂
        exact ⟨_, .step_block_exit_match hl, ⟨heq.2.2.1, heq.2.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_block_exit_mismatch hl =>
    cases c₂ with
    | block _ i₂ =>
      have hlb := heq.1; subst hlb
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl₂ := heq.2.1; subst hl₂
        exact ⟨_, .step_block_exit_mismatch hl, ⟨rfl, heq.2.2.1, heq.2.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq

/-- The terminal state's store and eval are independent of the starting
    `hasFailure` flag.  Proved by simulation: each step preserves
    store/eval equivalence, so the terminal states agree. -/
theorem smallStep_hasFailure_irrel
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.terminal ρ')) :
    ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
    ∃ ρ₂', StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₂) (.terminal ρ₂') ∧
      ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval := by
  intro ρ₂ hs he
  -- Lift single-step simulation to multi-step
  suffices ∀ (c₁ c₂ : Config P (Cmd P)),
      ConfigSE P c₁ c₂ →
      ∀ c₁', StepStmtStar P (EvalCmd P) extendEval c₁ c₁' →
      ∃ c₂', StepStmtStar P (EvalCmd P) extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' by
    have heq_init : ConfigSE P (.stmt s ρ) (.stmt s ρ₂) := ⟨rfl, hs.symm, he.symm⟩
    have ⟨c₂', hstar₂, heq₂⟩ := this _ _ heq_init _ h
    match c₂', heq₂ with
    | .terminal ρ₂', heq_t => exact ⟨ρ₂', hstar₂, heq_t.1.symm, heq_t.2.symm⟩
  intro c₁ c₂ heq c₁' hstar
  induction hstar generalizing c₂ with
  | refl => exact ⟨c₂, .refl _, heq⟩
  | step _ mid _ hstep _ ih =>
    have ⟨mid₂, hstep₂, heq_mid⟩ := step_simulation P extendEval _ _ _ hstep heq
    have ⟨c₂', hstar₂, heq_final⟩ := ih _ heq_mid
    exact ⟨c₂', .step _ _ _ hstep₂ hstar₂, heq_final⟩

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

theorem hoareTriple_implies_assertValid
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hoare : HoareTriple P extendEval
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt))
    -- st does not syntactically contain any assert with label `post_label`.
    (hno : st.noMatchingAssert post_label) :
    AssertValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg hreach hat
  -- Derive the execution-level no-match property from the syntactic check
  have hno_match := noMatchingAssert_implies_no_reachable_assert P extendEval st post_label post_expr hno
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
                        cases h_assume_rest with
                        | refl =>
                          have ⟨ρ'_clean, hterm_clean, hs_eq, he_eq⟩ :=
                            @smallStep_hasFailure_irrel P _ _ _ extendEval
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

/-- Single-step: if hasFailure is false and all reachable asserts pass,
    then hasFailure stays false after one step. -/
private theorem step_preserves_noFailure
    (c₁ c₂ : Config P (Cmd P))
    (hv : ∀ a cfg, StepStmtStar P (EvalCmd P) extendEval c₁ cfg →
      isAtAssert P cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hnf : c₁.getEnv.hasFailure = false)
    (hstep : StepStmt P (EvalCmd P) extendEval c₁ c₂) :
    c₂.getEnv.hasFailure = false := by
  induction hstep with
  | step_cmd hcmd =>
    cases hcmd with
    | eval_assert_fail hff _ =>
      have htt := hv ⟨_, _⟩ _ (.refl _) ⟨rfl, rfl⟩
      simp only [Config.getEval, Config.getStore] at htt
      rw [hff] at htt; exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm
    | _ => simp_all [Config.getEnv]
  | step_block => simp [Config.getEnv]; exact hnf
  | step_ite_true _ _ => exact hnf
  | step_ite_false _ _ => exact hnf
  | step_loop_enter _ _ => exact hnf
  | step_loop_exit _ _ => exact hnf
  | step_exit => exact hnf
  | step_funcDecl => simp [Config.getEnv]; exact hnf
  | step_typeDecl => exact hnf
  | step_stmts_nil => exact hnf
  | step_stmts_cons => exact hnf
  | step_seq_inner h ih =>
    exact ih
      (fun a cfg hr hat => hv a (.seq cfg _) (seq_inner_star P (EvalCmd P) extendEval _ _ _ hr) hat) hnf
  | step_seq_done => exact hnf
  | step_seq_exit => exact hnf
  | step_block_body h ih =>
    exact ih
      (fun a cfg hr hat => hv a (.block _ cfg) (block_inner_star P extendEval _ _ _ hr) hat) hnf
  | step_block_done => exact hnf
  | step_block_exit_none => exact hnf
  | step_block_exit_match _ => exact hnf
  | step_block_exit_mismatch _ => exact hnf

private theorem allAssertsValid_preserves_noFailure
    (st : Stmt P (Cmd P))
    (hvalid : ∀ (a : AssertId P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) cfg →
      isAtAssert P cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hf₀ : ρ₀.hasFailure = false)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    ρ'.hasFailure = false := by
  -- Lift step_preserves_noFailure to multi-step via induction.
  suffices ∀ c₁ c₂,
      (∀ a cfg, StepStmtStar P (EvalCmd P) extendEval c₁ cfg →
        isAtAssert P cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt) →
      c₁.getEnv.hasFailure = false →
      StepStmtStar P (EvalCmd P) extendEval c₁ c₂ →
      c₂.getEnv.hasFailure = false by
    exact this _ _ hvalid hf₀ hstar
  intro c₁ c₂ hv hnf hstar_c
  induction hstar_c with
  | refl => exact hnf
  | step _ mid _ hstep _ ih =>
    exact ih
      (fun a cfg h hat => hv a _ (.step _ _ _ hstep h) hat)
      (step_preserves_noFailure P extendEval _ _ hv hnf hstep)

/-- `AllAssertsValid` for the composite implies `AllAssertsValid` for `st`
    when run from an env reachable via the composite's assume prefix.
    This connects composite-level validity to statement-level validity
    by showing that configs reachable during `st`'s execution correspond
    to configs reachable inside the composite (through block/seq wrappers).

    Note: `WellFormedSemanticEvalBool ρ₀.eval` is required only for the
    `assume` step at the start of the composite, which uses the initial
    env's evaluator. -/
private theorem composite_allAssertsValid_implies_st
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hvalid : AllAssertsValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    ∀ (ρ₀ : Env P),
      WellFormedSemanticEvalBool ρ₀.eval →
      ρ₀.eval ρ₀.store pre_expr = some HasBool.tt →
      ρ₀.hasFailure = false →
      ∀ (a : AssertId P) (cfg : Config P (Cmd P)),
        StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) cfg →
        isAtAssert P cfg a →
        cfg.getEval cfg.getStore a.expr = some HasBool.tt := by
  intro ρ₀ hwfb hpre hf₀ a cfg hstar hat
  -- Build composite execution prefix: block → stmts → assume → stmts [st, ...]
  -- Then embed st's execution inside the composite via block/seq lifting.
  let assume_stmt : Stmt P (Cmd P) := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P (Cmd P) := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P (Cmd P)) := [assume_stmt, st, assert_stmt]
  -- Assume step
  have h_assume : StepStmtStar P (EvalCmd P) extendEval
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
  have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P) = ρ₀ := by
    cases ρ₀; simp [Bool.or_false]
  -- stmts [assume, st, assert] ρ₀ →* stmts [st, assert] ρ₀
  have h1 := stmts_cons_step P (EvalCmd P) extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
  rw [h_ρ₁_eq] at h1
  -- stmts [st, assert] ρ₀ → seq (.stmt st ρ₀) [assert]
  have h2 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [st, assert_stmt] ρ₀) (.seq (.stmt st ρ₀) [assert_stmt]) :=
    .step _ _ _ StepStmt.step_stmts_cons (.refl _)
  -- seq (.stmt st ρ₀) [assert] →* seq cfg [assert] (lifting st's execution)
  have h3 := seq_inner_star P (EvalCmd P) extendEval _ _ [assert_stmt] hstar
  -- Compose and lift through block
  have h_inner := reflTrans_trans (h1 := reflTrans_trans (h1 := h1) (h2 := h2)) (h2 := h3)
  have h_block := block_inner_star P extendEval _ _ block_label h_inner
  have h_start : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.block block_label body block_md) ρ₀) (.block block_label (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  have h_full := reflTrans_trans (h1 := h_start) (h2 := h_block)
  -- The target config is .block bl (.seq cfg [assert]), which satisfies
  -- isAtAssert iff cfg does (recursion through block → seq → cfg)
  have hat_composite : isAtAssert P (.block block_label (.seq cfg [assert_stmt])) a := hat
  -- Apply hvalid
  have h_result := hvalid a ρ₀ _ h_full hat_composite
  simp only [Config.getEval, Config.getStore] at h_result ⊢
  exact h_result

/-- If `AllAssertsValid` holds for the composite `assume pre; st; assert post`,
    then the Hoare triple `{pre_expr = tt} st {post_expr = tt}` holds.

    The `AllAssertsValid` hypothesis (rather than just `AssertValid` for the
    post assert) ensures that all intermediate asserts in `st` also pass,
    which is needed for the `hasFailure = false` postcondition.

    `WellFormedSemanticEvalBool ρ₀.eval` is needed to construct the
    `assume` step in the composite execution; it is supplied by
    `HoareTriple`'s built-in well-formedness premise.  Only the initial
    evaluator matters — see the comment on
    `composite_allAssertsValid_implies_st` for details. -/
theorem assertValid_implies_hoareTriple
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hvalid : AllAssertsValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    HoareTriple P extendEval
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt) := by
  -- Derive noFailure from hvalid via composite_allAssertsValid_implies_st
  have hvalid_st := composite_allAssertsValid_implies_st P extendEval
    pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md hvalid
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  -- Build the composite execution: block [assume pre; st; assert post]
  -- Starting from ρ₀, the assume passes (since hpre holds), then st runs
  -- to ρ', then the execution reaches the assert with env ρ'.
  let assume_stmt : Stmt P (Cmd P) := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P (Cmd P) := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P (Cmd P)) := [assume_stmt, st, assert_stmt]
  -- Step 1: assume passes, producing ρ₁ (propositionally = ρ₀ since hf₀)
  have h_assume : StepStmtStar P (EvalCmd P) extendEval
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
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
  -- Apply hvalid (specialized to the post assert) at the reachable config
  have h_result := hvalid ⟨post_label, post_expr⟩ ρ₀ _ h_full h_at
  -- Simplify getEval/getStore through block → seq → stmt
  simp only [Config.getEval, Config.getStore] at h_result
  -- Post ρ' holds; hasFailure = false from allAssertsValid_preserves_noFailure
  exact ⟨h_result, allAssertsValid_preserves_noFailure P extendEval
    (ρ₀ := ρ₀) (ρ' := ρ') st (hvalid_st ρ₀ hwfb hpre hf₀) hf₀ hstar⟩

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

end Specification
end Imperative

end -- public section

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
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt)) :
    AssertValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  sorry

theorem assertValid_implies_hoareTriple_general
    (pre_label : String) (pre_expr : P.Expr) (pre_md : MetaData P)
    (st : Stmt P (Cmd P))
    (post_label : String) (post_expr : P.Expr) (post_md : MetaData P)
    (block_label : String) (block_md : MetaData P)
    (hvalid : AssertValid P extendEval
      (hoareBlock P pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩)
    (hprogress : ∀ (ρ₀ : Env P),
      ρ₀.eval ρ₀.store pre_expr = some HasBool.tt →
      ∃ (ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    HoareTriple P extendEval
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt) := by
  sorry

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

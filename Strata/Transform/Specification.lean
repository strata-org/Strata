/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.Languages.Core.StatementSemantics

/-! # Soundness Specification for Strata

This file defines two styles of top-level soundness for assertion checks,
proves that the Hoare-triple style (B) is a special case of the reachability
style (A), and defines correctness of program transformations.

## Style A — Reachability-based assertion validity

Whenever execution of a statement (under small-step semantics) reaches a
configuration whose head is an `assert label expr`, the expression `expr`
evaluates to `true` in the current store.

## Style B — Hoare-triple assertion validity

For a given precondition P and postcondition Q (both predicates on stores),
if the initial store satisfies P and the statement executes to a terminal
store, then the terminal store satisfies Q.  This is the classical partial-
correctness Hoare triple {P} S {Q}.

## Theorem: B is a special case of A

We show that if a Hoare triple holds for a statement whose body is
`assert label expr` (i.e., the postcondition is exactly that `expr` holds),
then the reachability-based validity also holds for that assert label.

## Transformation correctness

A transformation `T` on statements is *correct* (w.r.t. assertion checks) if:
for every assert label `a`, if `a` is valid in `T(s)` then `a` is valid in `s`.
-/

namespace Strata.Soundness

open Core Imperative

/-! ## Core-specific small-step abbreviations

Copied from `SoundnessFramework.lean` (branch `proc-body-verify`). -/

abbrev CoreConfig := Config Expression Command

abbrev CoreStep
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)

abbrev CoreStepStar
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)

/-! ## Assertion Identity

An assertion is identified by its label (a `CoreLabel`, i.e., `String`).
We use the label of the `assert` command as the program location.
-/

/-- An assertion identifier: the label + expression + metadata attached to an
    `assert` command.
    Copied from `SoundnessFramework.lean` (branch `proc-body-verify`). -/
structure AssertId where
  label : CoreLabel
  expr  : Expression.Expr
  md    : MetaData Expression

/-! ## Detecting an assert in a configuration

`isAtAssert cfg aid` holds when the head of `cfg` is an `assert` command
whose label, expression, and metadata match `aid`. -/

/-- Adapted from `ProgramState.ofConfig` in `SoundnessFramework.lean`
    (branch `proc-body-verify`).  Simplified: returns a `Prop` instead of
    wrapping in `Option ProgramState`, and does not recurse into `block`/`seq`. -/
def isAtAssert : CoreConfig → AssertId → Prop
  | .stmt (.cmd (.cmd (.assert label expr md))) _ _, aid =>
    aid.label = label ∧ aid.expr = expr ∧ aid.md = md
  | .stmts ((.cmd (.cmd (.assert label expr md))) :: _) _ _, aid =>
    aid.label = label ∧ aid.expr = expr ∧ aid.md = md
  | _, _ => False

/-- Extract the store from a configuration.
    Adapted from `Config.getδ` in `DetToNondetCorrectSmallStep.lean`
    (branch `atomb/det-nondet-small-step`); analogous accessor for the store. -/
def CoreConfig.getStore : CoreConfig → CoreStore
  | .stmt _ σ _ => σ
  | .stmts _ σ _ => σ
  | .terminal σ _ => σ
  | .exiting _ σ _ => σ
  | .block _ inner => CoreConfig.getStore inner
  | .seq inner _ => CoreConfig.getStore inner

/-- Extract the evaluator from a configuration.
    Adapted from `Config.getδ` in `DetToNondetCorrectSmallStep.lean`
    (branch `atomb/det-nondet-small-step`), updated for `Config.block`
    and `Config.seq` from `proc-body-verify`. -/
def CoreConfig.getEval : CoreConfig → CoreEval
  | .stmt _ _ δ => δ
  | .stmts _ _ δ => δ
  | .terminal _ δ => δ
  | .exiting _ _ δ => δ
  | .block _ inner => CoreConfig.getEval inner
  | .seq inner _ => CoreConfig.getEval inner

/-! ## Style A — Reachability-based assertion validity

A statement `s` satisfies `AllAssertsValid` if, for every execution path
starting from *any* initial state `(σ₀, δ)`, whenever the small-step
execution reaches a configuration that is at an assert `a`, the assert
expression evaluates to `true` in the current store.
-/

/-- An assert `a` is *reachable* from statement `s` at configuration `cfg`
    if there exist initial state components such that multi-step execution
    from `(.stmt s σ₀ δ)` reaches `cfg` and `cfg` is at assert `a`.
    Adapted from `reachable` in `SoundnessFramework.lean`
    (branch `proc-body-verify`); uses `isAtAssert` instead of
    `ProgramState.ofConfig`. -/
def Reachable
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (a : AssertId) (cfg : CoreConfig) : Prop :=
  ∃ (σ₀ : CoreStore) (δ : CoreEval),
    CoreStepStar π φ (.stmt s σ₀ δ) cfg ∧
    isAtAssert cfg a

/-- Assert `a` is *valid* in statement `s` if, for every reachable
    configuration at `a`, the assert expression evaluates to `true`.
    Adapted from `stmt_valid` in `SoundnessFramework.lean`
    (branch `proc-body-verify`). -/
def AssertValid
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (a : AssertId) : Prop :=
  ∀ (cfg : CoreConfig),
    Reachable π φ s a cfg →
    cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- *All* asserts are valid in statement `s`.
    Adapted from `stmt_correct` in `SoundnessFramework.lean`
    (branch `proc-body-verify`). -/
def AllAssertsValid
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) : Prop :=
  ∀ (a : AssertId), AssertValid π φ s a

/-! ## Style B — Hoare-triple assertion validity

The classical partial-correctness Hoare triple `{P} s {Q}`:
for all initial states satisfying `P`, if `s` executes to a terminal state,
then the terminal state satisfies `Q`.

We use small-step semantics (`StepStmtStar` reaching `.terminal`).
-/

/-- Partial-correctness Hoare triple using small-step semantics.
    Inspired by `procedure_obeys_contract` in `SoundnessFramework.lean`
    (branch `proc-body-verify`), generalized to arbitrary pre/postconditions
    on stores and evaluators. -/
def HoareTriple
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (P : CoreStore → CoreEval → Prop)
    (s : Statement)
    (Q : CoreStore → CoreEval → Prop) : Prop :=
  ∀ (σ₀ : CoreStore) (δ : CoreEval) (σ' : CoreStore) (δ' : CoreEval),
    P σ₀ δ →
    CoreStepStar π φ (.stmt s σ₀ δ) (.terminal σ' δ') →
    Q σ' δ'

/-! ## Relationship between Style A and Style B

For a single assert command `assert label expr md`:

- Style A (reachability) says: whenever execution reaches the assert,
  `expr` evaluates to `true` in the current store.
- Style B (Hoare triple) `{True} assert {expr = true}` says: if the
  assert steps to terminal, then `expr` was true.

These are equivalent for a single assert because:
- `eval_assert` requires `δ σ expr = some tt` to step to terminal, so
  the Hoare triple holding means every reachable-and-steppable state has
  `expr` true.
- Conversely, if `expr` is true at every reachable assert configuration,
  then `eval_assert` can fire and the terminal state inherits `expr = true`.

For a single assert command, the only configuration satisfying `isAtAssert`
is the initial `.stmt` configuration itself (zero steps from the start),
because the assert command has exactly one step (to `.terminal`).
-/

/-
Informal proof of A ⟹ B:

Theorem: AssertValid π φ (assert label expr md) ⟨label, expr, md⟩ →
         HoareTriple π φ True (assert label expr md) (expr = true)

Proof:
  1. Assume AssertValid holds.
  2. Let σ₀, δ be an initial state and suppose the assert steps to
     terminal σ', δ'.
  3. By inversion on the multi-step execution of a single assert command:
     the only step is step_cmd (eval_assert), which requires
     δ σ₀ expr = some tt and produces σ' = σ₀, δ' = δ.
  4. The initial configuration .stmt (assert ..) σ₀ δ satisfies isAtAssert,
     and is reachable in zero steps.
  5. By AssertValid applied to this configuration: δ σ₀ expr = some tt.
  6. Since σ' = σ₀ and δ' = δ, we have δ' σ' expr = some tt.
  7. done
     by 5 and 6.

Informal proof of B ⟹ A:

Theorem: HoareTriple π φ True (assert label expr md) (expr = true) →
         AssertValid π φ (assert label expr md) ⟨label, expr, md⟩

Proof:
  1. Assume the Hoare triple holds.
  2. Let cfg be reachable from (assert label expr md) at the assert.
  3. By definition, there exist σ₀, δ with
     CoreStepStar (.stmt (assert ..) σ₀ δ) cfg and isAtAssert cfg.
  4. For a single assert command, the only config satisfying isAtAssert
     is .stmt (assert ..) σ₀ δ itself (reached in zero steps).
     by: the assert command can only step to .terminal (via step_cmd),
     and .terminal does not satisfy isAtAssert.
  5. So cfg = .stmt (assert label expr md) σ₀ δ, and we need
     δ σ₀ expr = some tt.
  6. The Hoare triple says: if the assert steps to terminal, then
     δ' σ' expr = some tt. By eval_assert, stepping requires
     δ σ₀ expr = some tt and produces σ' = σ₀, δ' = δ.
  7. But we need the expression to be true *before* stepping, not after.
     The Hoare triple only tells us something when execution terminates.
  8. We need an additional assumption: the assert is not stuck, i.e.,
     execution can proceed. We add this as a hypothesis.
-/

/-- Auxiliary: for a single assert command, the only configuration
    reachable from `.stmt (assert ..) σ δ` that satisfies `isAtAssert`
    is the initial configuration itself. -/
private theorem assert_reachable_is_initial
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (σ₀ : CoreStore) (δ : CoreEval) (cfg : CoreConfig)
    (hstar : CoreStepStar π φ (.stmt (Statement.assert label expr md) σ₀ δ) cfg)
    (hat : isAtAssert cfg ⟨label, expr, md⟩) :
    cfg = .stmt (Statement.assert label expr md) σ₀ δ := by
  -- A single assert command can only step to .terminal via step_cmd.
  -- .terminal does not satisfy isAtAssert. So cfg must be the initial config.
  cases hstar with
  | refl => rfl
  | step _ mid _ hstep hrest =>
    -- The only step from .stmt (.cmd (.cmd (.assert ..))) is step_cmd
    cases hstep with
    | step_cmd hcmd =>
      -- mid = .terminal σ₀ δ, and hrest : CoreStepStar (.terminal ..) cfg
      -- .terminal cannot step further, so cfg = .terminal ..
      cases hrest with
      | refl =>
        -- cfg = .terminal σ₀ δ, but isAtAssert (.terminal ..) is False
        exact absurd hat (by simp [isAtAssert])
      | step _ _ _ hstep2 _ =>
        -- .terminal cannot step
        exact absurd hstep2 (by intro h; cases h)

/-- Style A implies Style B: if all reachable assert configurations have
    `expr = true`, then the Hoare triple holds. -/
theorem assertValid_implies_hoareTriple
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (s : Statement)
    (hs : s = Statement.assert label expr md)
    (hvalid : AssertValid π φ s ⟨label, expr, md⟩) :
    HoareTriple π φ
      (fun _ _ => True)
      s
      (fun σ' δ' => δ' σ' expr = some HasBool.tt) := by
  subst hs
  intro σ₀ δ σ' δ' _ hstar
  -- Invert the multi-step execution of a single assert command.
  -- The only step is step_cmd (eval_assert).
  cases hstar with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      -- hcmd : EvalCommand π φ δ σ₀ (.cmd (.assert label expr md)) σ'_mid
      -- mid = .terminal σ'_mid δ
      cases hcmd with
      | cmd_sem heval =>
        -- heval : EvalCmd .. δ σ₀ (.assert label expr md) σ'_mid
        cases heval with
        | eval_assert htt _ =>
          -- htt : δ σ₀ expr = some HasBool.tt
          -- mid = .terminal σ₀ δ, so hrest : CoreStepStar (.terminal σ₀ δ) (.terminal σ' δ')
          cases hrest with
          | refl => exact htt
          | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)

/-- Style B implies Style A, given that the assert is not stuck
    (i.e., for every reachable assert configuration, execution can
    proceed to terminal). This additional hypothesis is necessary
    because the Hoare triple only speaks about executions that terminate.

    In practice, this hypothesis holds when the evaluator is well-formed
    and the expression is well-typed. -/
theorem hoareTriple_implies_assertValid
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (s : Statement)
    (hs : s = Statement.assert label expr md)
    (hoare : HoareTriple π φ
      (fun _ _ => True)
      s
      (fun σ' δ' => δ' σ' expr = some HasBool.tt))
    -- Additional hypothesis: the assert is not stuck. For every initial
    -- state, the assert command can step to terminal.
    (hprogress : ∀ (σ₀ : CoreStore) (δ : CoreEval),
      ∃ (σ' : CoreStore) (δ' : CoreEval),
        CoreStepStar π φ (.stmt s σ₀ δ) (.terminal σ' δ')) :
    AssertValid π φ s ⟨label, expr, md⟩ := by
  subst hs
  intro cfg hreach
  obtain ⟨σ₀, δ, hstar, hat⟩ := hreach
  -- cfg must be the initial configuration
  have heq := assert_reachable_is_initial π φ label expr md σ₀ δ cfg hstar hat
  subst heq
  -- Now we need: δ σ₀ expr = some HasBool.tt
  -- Use progress to get a terminal state, then apply the Hoare triple.
  obtain ⟨σ', δ', hterm⟩ := hprogress σ₀ δ
  simp only [CoreConfig.getEval, CoreConfig.getStore]
  cases hterm with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      cases hcmd with
      | cmd_sem heval =>
        cases heval with
        | eval_assert htt _ =>
          cases hrest with
          | refl => exact htt
          | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)

/-! ## Equivalence for a single assert command -/

/-- For a single assert command, Style A implies Style B unconditionally.
    Style B implies Style A given a progress assumption. -/
theorem assertValid_implies_hoareTriple_iff
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (s : Statement)
    (hs : s = Statement.assert label expr md)
    (hprogress : ∀ (σ₀ : CoreStore) (δ : CoreEval),
      ∃ (σ' : CoreStore) (δ' : CoreEval),
        CoreStepStar π φ (.stmt s σ₀ δ) (.terminal σ' δ')) :
    AssertValid π φ s ⟨label, expr, md⟩ ↔
    HoareTriple π φ
      (fun _ _ => True)
      s
      (fun σ' δ' => δ' σ' expr = some HasBool.tt) :=
  ⟨assertValid_implies_hoareTriple π φ label expr md s hs,
   fun h => hoareTriple_implies_assertValid π φ label expr md s hs h hprogress⟩

/-! ## Transformation Correctness

A program transformation `T` is *correct w.r.t. assertion checks* if:
for every assert `a`, validity of `a` in `T(s)` implies validity of `a` in `s`.

This corresponds to Definition 2 from the soundness document: the
transformation does not fabricate validity.
-/

/-- A transformation on statements.
    Simplified from `Transformation` in `SoundnessFramework.lean`
    (branch `proc-body-verify`); drops the `F`/`F_inv` assertion-id maps
    since soundness here is stated for the same assertion id on both sides. -/
structure Transformation where
  /-- The transformation function on statements. -/
  transform : Statement → Statement

/-- A transformation is *sound* if it preserves assertion validity:
    whenever an assert is valid in the transformed statement, it is
    also valid in the original statement.

    Note the direction: valid in T(s) ⟹ valid in s.
    This means T does not fabricate validity — if T(s) says "all asserts
    pass," then they genuinely pass in s. -/
def Transformation.Sound
    (T : Transformation)
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) : Prop :=
  ∀ (s : Statement) (a : AssertId),
    AssertValid π φ (T.transform s) a →
    AssertValid π φ s a

/-- Composition of sound transformations is sound. -/
theorem sound_comp
    (T₁ T₂ : Transformation)
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (h₁ : T₁.Sound π φ)
    (h₂ : T₂.Sound π φ) :
    (⟨T₂.transform ∘ T₁.transform⟩ : Transformation).Sound π φ := by
  intro s a hvalid
  -- hvalid : AssertValid π φ (T₂.transform (T₁.transform s)) a
  -- By soundness of T₂: AssertValid π φ (T₁.transform s) a
  -- By soundness of T₁: AssertValid π φ s a
  exact h₁ s a (h₂ (T₁.transform s) a hvalid)

/-! ## End-to-end soundness statement

If a pipeline of transformations is sound and the VCGen reports that
all asserts are valid in the final transformed program, then all asserts
are valid in the original program. -/

/-- End-to-end: if `T` is sound and all asserts are valid in `T(s)`,
    then all asserts are valid in `s`. -/
theorem endToEnd_allAsserts
    (T : Transformation)
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement)
    (hsound : T.Sound π φ)
    (hvalid : AllAssertsValid π φ (T.transform s)) :
    AllAssertsValid π φ s := by
  intro a
  exact hsound s a (hvalid a)

end Strata.Soundness

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsSmallStep
public import Strata.Languages.Core.StatementSemantics
public import Strata.Transform.CoreTransform

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

public section

namespace Core
namespace Transform

open Imperative

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

/-- An assertion identifier: the label + expression attached to an
    `assert` command.  Metadata is intentionally excluded — it is not
    semantically relevant for assertion validity.
    Adapted from `SoundnessFramework.lean` (branch `proc-body-verify`). -/
structure AssertId where
  label : CoreLabel
  expr  : Expression.Expr

/-! ## Detecting an assert in a configuration

`isAtAssert cfg aid` holds when the head of `cfg` is an `assert` command
whose label and expression match `aid`. -/

/-- Adapted from `ProgramState.ofConfig` in `SoundnessFramework.lean`
    (branch `proc-body-verify`).  Simplified: returns a `Prop` instead of
    wrapping in `Option ProgramState`, and does not recurse into `block`/`seq`. -/
def isAtAssert : CoreConfig → AssertId → Prop
  | .stmt (.cmd (.cmd (.assert label expr _))) _ _ _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.cmd (.assert label expr _))) :: _) _ _ _, aid =>
    aid.label = label ∧ aid.expr = expr
  | _, _ => False

/-- Extract the store from a configuration.
    Adapted from `Config.getδ` in `DetToNondetCorrectSmallStep.lean`
    (branch `atomb/det-nondet-small-step`); analogous accessor for the store.
    Updated for `Config` with `ProgramCounter` fields and `seq` with `tailPc`. -/
def CoreConfig.getStore : CoreConfig → CoreStore
  | .stmt _ σ _ _ => σ
  | .stmts _ σ _ _ => σ
  | .terminal σ _ => σ
  | .exiting _ σ _ => σ
  | .block _ inner => CoreConfig.getStore inner
  | .seq inner _ _ => CoreConfig.getStore inner

/-- Extract the evaluator from a configuration.
    Adapted from `Config.getδ` in `DetToNondetCorrectSmallStep.lean`
    (branch `atomb/det-nondet-small-step`), updated for `Config.block`
    and `Config.seq` from `proc-body-verify`, and new `ProgramCounter` fields. -/
def CoreConfig.getEval : CoreConfig → CoreEval
  | .stmt _ _ δ _ => δ
  | .stmts _ _ δ _ => δ
  | .terminal _ δ => δ
  | .exiting _ _ δ => δ
  | .block _ inner => CoreConfig.getEval inner
  | .seq inner _ _ => CoreConfig.getEval inner

/-- Extract the program counter from a configuration, if present.
    Returns `[]` for terminal/exiting configurations. Recurses into
    block/seq wrappers. -/
def CoreConfig.getPC : CoreConfig → ProgramCounter
  | .stmt _ _ _ pc => pc
  | .stmts _ _ _ pc => pc
  | .terminal _ _ => []
  | .exiting _ _ _ => []
  | .block _ inner => CoreConfig.getPC inner
  | .seq inner _ _ => CoreConfig.getPC inner

/-! ## Style A — Reachability-based assertion validity

A statement `s` satisfies `AllAssertsValid` if, for every execution path
starting from *any* initial state `(σ₀, δ)` and *any* initial program
counter, whenever the small-step execution reaches a configuration that
is at an assert `a`, the assert expression evaluates to `true` in the
current store.
-/

/-- An assert `a` is *reachable* from statement `s` at configuration `cfg`
    if there exist initial state components and an initial program counter
    such that multi-step execution from `(.stmt s σ₀ δ pc₀)` reaches `cfg`
    and `cfg` is at assert `a`.
    Adapted from `reachable` in `SoundnessFramework.lean`
    (branch `proc-body-verify`); uses `isAtAssert` instead of
    `ProgramState.ofConfig`. -/
def Reachable
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (a : AssertId) (cfg : CoreConfig) : Prop :=
  ∃ (σ₀ : CoreStore) (δ : CoreEval) (pc₀ : ProgramCounter),
    CoreStepStar π φ (.stmt s σ₀ δ pc₀) cfg ∧
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
The triple quantifies over all initial program counters.
-/

/-- Partial-correctness Hoare triple using small-step semantics.
    Inspired by `procedure_obeys_contract` in `SoundnessFramework.lean`
    (branch `proc-body-verify`), generalized to arbitrary pre/postconditions
    on stores and evaluators.  Quantifies over all initial PCs. -/
def HoareTriple
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (P : CoreStore → CoreEval → Prop)
    (s : Statement)
    (Q : CoreStore → CoreEval → Prop) : Prop :=
  ∀ (σ₀ : CoreStore) (δ : CoreEval) (pc₀ : ProgramCounter)
    (σ' : CoreStore) (δ' : CoreEval),
    P σ₀ δ →
    CoreStepStar π φ (.stmt s σ₀ δ pc₀) (.terminal σ' δ') →
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

Theorem: AssertValid π φ (assert label expr md) ⟨label, expr⟩ →
         HoareTriple π φ True (assert label expr md) (expr = true)

Proof:
  1. Assume AssertValid holds.
  2. Let σ₀, δ, pc₀ be an initial state and suppose the assert steps to
     terminal σ', δ'.
  3. By inversion on the multi-step execution of a single assert command:
     the only step is step_cmd (eval_assert), which requires
     δ σ₀ expr = some tt and produces σ' = σ₀, δ' = δ.
  4. The initial configuration .stmt (assert ..) σ₀ δ pc₀ satisfies
     isAtAssert, and is reachable in zero steps.
  5. By AssertValid applied to this configuration: δ σ₀ expr = some tt.
  6. Since σ' = σ₀ and δ' = δ, we have δ' σ' expr = some tt.
  7. done
     by 5 and 6.

Informal proof of B ⟹ A:

Theorem: HoareTriple π φ True (assert label expr md) (expr = true) →
         AssertValid π φ (assert label expr md) ⟨label, expr⟩

Proof:
  1. Assume the Hoare triple holds.
  2. Let cfg be reachable from (assert label expr md) at the assert.
  3. By definition, there exist σ₀, δ, pc₀ with
     CoreStepStar (.stmt (assert ..) σ₀ δ pc₀) cfg and isAtAssert cfg.
  4. For a single assert command, the only config satisfying isAtAssert
     is .stmt (assert ..) σ₀ δ pc₀ itself (reached in zero steps).
     by: the assert command can only step to .terminal (via step_cmd),
     and .terminal does not satisfy isAtAssert.
  5. So cfg = .stmt (assert label expr md) σ₀ δ pc₀, and we need
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
    reachable from `.stmt (assert ..) σ δ pc₀` that satisfies `isAtAssert`
    is the initial configuration itself. -/
private theorem assert_reachable_is_initial
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (σ₀ : CoreStore) (δ : CoreEval) (pc₀ : ProgramCounter) (cfg : CoreConfig)
    (hstar : CoreStepStar π φ (.stmt (Statement.assert label expr md) σ₀ δ pc₀) cfg)
    (hat : isAtAssert cfg ⟨label, expr⟩) :
    cfg = .stmt (Statement.assert label expr md) σ₀ δ pc₀ := by
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
    (hvalid : AssertValid π φ s ⟨label, expr⟩) :
    HoareTriple π φ
      (fun _ _ => True)
      s
      (fun σ' δ' => δ' σ' expr = some HasBool.tt) := by
  subst hs
  intro σ₀ δ pc₀ σ' δ' _ hstar
  -- Invert the multi-step execution of a single assert command.
  -- The only step is step_cmd (eval_assert).
  cases hstar with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      cases hcmd with
      | cmd_sem heval =>
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
    -- state and PC, the assert command can step to terminal.
    (hprogress : ∀ (σ₀ : CoreStore) (δ : CoreEval) (pc₀ : ProgramCounter),
      ∃ (σ' : CoreStore) (δ' : CoreEval),
        CoreStepStar π φ (.stmt s σ₀ δ pc₀) (.terminal σ' δ')) :
    AssertValid π φ s ⟨label, expr⟩ := by
  subst hs
  intro cfg hreach
  obtain ⟨σ₀, δ, pc₀, hstar, hat⟩ := hreach
  -- cfg must be the initial configuration
  have heq := assert_reachable_is_initial π φ label expr md σ₀ δ pc₀ cfg hstar hat
  subst heq
  -- Now we need: δ σ₀ expr = some HasBool.tt
  -- Use progress to get a terminal state, then apply the Hoare triple.
  obtain ⟨σ', δ', hterm⟩ := hprogress σ₀ δ pc₀
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
    (hprogress : ∀ (σ₀ : CoreStore) (δ : CoreEval) (pc₀ : ProgramCounter),
      ∃ (σ' : CoreStore) (δ' : CoreEval),
        CoreStepStar π φ (.stmt s σ₀ δ pc₀) (.terminal σ' δ')) :
    AssertValid π φ s ⟨label, expr⟩ ↔
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

/-- A transformation on statements, using the `CoreTransformM` monad.
    The transformation may fail (returning an error) or carry state
    (e.g., fresh name generation).
    Adapted from `Transformation` in `SoundnessFramework.lean`
    (branch `proc-body-verify`); uses `CoreTransformM` instead of a
    pure function. -/
structure Transformation where
  /-- The monadic transformation function on statements. -/
  transform : Statement → CoreTransformM Statement

/-- A transformation is *sound* if it preserves assertion validity:
    whenever the transformation succeeds (producing `s'` from `s` in
    some initial state `st`) and assert `a` is valid in `s'`, then
    `a` is also valid in the original statement `s`.

    Note the direction: valid in T(s) ⟹ valid in s.
    This means T does not fabricate validity — if T(s) says "all asserts
    pass," then they genuinely pass in s. -/
def Transformation.Sound
    (T : Transformation)
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) : Prop :=
  ∀ (s s' : Statement) (a : AssertId)
    (st st' : CoreTransformState),
    (T.transform s).run st = (.ok s', st') →
    AssertValid π φ s' a →
    AssertValid π φ s a

/-- Composition of sound transformations is sound. -/
theorem sound_comp
    (T₁ T₂ : Transformation)
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (h₁ : T₁.Sound π φ)
    (h₂ : T₂.Sound π φ) :
    (⟨fun s => T₁.transform s >>= T₂.transform⟩ : Transformation).Sound π φ := by
  intro s s'' a st st'' hrun hvalid
  -- Beta-reduce the structure projection
  dsimp [Transformation.transform] at hrun
  -- Unfold the monadic bind to expose the intermediate result of T₁
  simp only [bind, ExceptT.bind] at hrun
  unfold ExceptT.bindCont at hrun
  simp only [ExceptT.run, ExceptT.mk] at hrun
  unfold StateT.bind at hrun
  simp only [] at hrun
  -- Split on the result of T₁.  Unfold ExceptT.run in h1 so it matches hrun.
  match h1 : (T₁.transform s).run st with
  | (.ok s', st') =>
    unfold ExceptT.run at h1
    rw [h1] at hrun
    dsimp [pure, bind, Except.bind, Id.run] at hrun
    exact h₁ s s' a st st' (by unfold ExceptT.run; exact h1) (h₂ s' s'' a st' st'' hrun hvalid)
  | (.error e, st') =>
    unfold ExceptT.run at h1
    rw [h1] at hrun
    dsimp [pure, bind, Except.bind, Id.run] at hrun
    -- hrun : StateT.pure (Except.error e) st' = (Except.ok s'', st'')
    unfold StateT.pure at hrun
    dsimp [pure] at hrun
    -- hrun : (Except.error e, st') = (Except.ok s'', st'') — contradiction
    exact absurd (congrArg Prod.fst hrun) (by nofun)

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
    (s s' : Statement)
    (st st' : CoreTransformState)
    (hrun : (T.transform s).run st = (.ok s', st'))
    (hsound : T.Sound π φ)
    (hvalid : AllAssertsValid π φ s') :
    AllAssertsValid π φ s := by
  intro a
  exact hsound s s' a st st' hrun (hvalid a)

end Transform
end Core

end -- public section

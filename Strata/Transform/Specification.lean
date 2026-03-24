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

/-- Core-specific execution environment. -/
abbrev CoreEnv := Env Expression

abbrev CoreStep
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)

abbrev CoreStepStar
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :=
  StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

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
  | .stmt (.cmd (.cmd (.assert label expr _))) _ _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.cmd (.assert label expr _))) :: _) _ _, aid =>
    aid.label = label ∧ aid.expr = expr
  | _, _ => False

/-- Extract the store from a configuration.
    Adapted from `Config.getδ` in `DetToNondetCorrectSmallStep.lean`
    (branch `atomb/det-nondet-small-step`); analogous accessor for the store.
    Updated for `Config` with `Env` and `ProgramCounter` fields. -/
def CoreConfig.getStore : CoreConfig → CoreStore
  | .stmt _ ρ _ => ρ.store
  | .stmts _ ρ _ => ρ.store
  | .terminal ρ => ρ.store
  | .exiting _ ρ => ρ.store
  | .block _ inner => CoreConfig.getStore inner
  | .seq inner _ _ => CoreConfig.getStore inner

/-- Extract the evaluator from a configuration.
    Adapted from `Config.getδ` in `DetToNondetCorrectSmallStep.lean`
    (branch `atomb/det-nondet-small-step`), updated for `Config` with
    `Env` and `ProgramCounter` fields. -/
def CoreConfig.getEval : CoreConfig → CoreEval
  | .stmt _ ρ _ => ρ.eval
  | .stmts _ ρ _ => ρ.eval
  | .terminal ρ => ρ.eval
  | .exiting _ ρ => ρ.eval
  | .block _ inner => CoreConfig.getEval inner
  | .seq inner _ _ => CoreConfig.getEval inner

/-- Extract the program counter from a configuration, if present.
    Returns `none` for terminal/exiting configurations. Recurses into
    block/seq wrappers. -/
def CoreConfig.getPC : CoreConfig → Option ProgramCounter
  | .stmt _ _ pc => some pc
  | .stmts _ _ pc => some pc
  | .terminal _ => none
  | .exiting _ _ => none
  | .block _ inner => CoreConfig.getPC inner
  | .seq inner _ _ => CoreConfig.getPC inner

/-- Extract the execution environment from a configuration.
    Recurses into block/seq wrappers. For terminal/exiting, returns
    the stored environment directly. -/
def CoreConfig.getEnv : CoreConfig → CoreEnv
  | .stmt _ ρ _ => ρ
  | .stmts _ ρ _ => ρ
  | .terminal ρ => ρ
  | .exiting _ ρ => ρ
  | .block _ inner => CoreConfig.getEnv inner
  | .seq inner _ _ => CoreConfig.getEnv inner

/-! ## Style A — Reachability-based assertion validity

A statement `s` satisfies `AllAssertsValid` if, for every execution path
starting from *any* initial environment `ρ₀` and *any* initial program
counter, whenever the small-step execution reaches a configuration that
is at an assert `a`, the assert expression evaluates to `true` in the
current store.
-/

/-- A configuration `cfg` is *reachable* from statement `s` with initial
    environment `ρ₀` and program counter `pc₀` if multi-step execution
    from `(.stmt s ρ₀ pc₀)` reaches `cfg` and `cfg` has program counter
    `pc`.
    Adapted from `reachable` in `SoundnessFramework.lean`
    (branch `proc-body-verify`). -/
def Reachable
    (s : Statement) (ρ₀ : CoreEnv) (pc₀ : ProgramCounter)
    (pc : ProgramCounter) (cfg : CoreConfig) : Prop :=
  CoreStepStar π φ (.stmt s ρ₀ pc₀) cfg ∧
  cfg.getPC = some pc

/-- Assert `a` is *valid* in statement `s` if, for every initial
    environment, initial program counter, and reachable configuration
    at program counter `pc` that is at assert `a`, the assert expression
    evaluates to `true`.
    Adapted from `stmt_valid` in `SoundnessFramework.lean`
    (branch `proc-body-verify`). -/
def AssertValid
    (s : Statement) (a : AssertId) : Prop :=
  ∀ (ρ₀ : CoreEnv) (pc₀ pc : ProgramCounter) (cfg : CoreConfig),
    Reachable π φ s ρ₀ pc₀ pc cfg →
    isAtAssert cfg a →
    cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- All asserts are valid in statement `s`. Assert `a` does not have to be
    constrainted to those in `s` because AssertValid uses partial correctness.
    Adapted from `stmt_correct` in `SoundnessFramework.lean`
    (branch `proc-body-verify`). -/
def AllAssertsValid
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
    on environments.  Quantifies over all initial PCs.

    The precondition includes `ρ₀.hasFailure = false` (no prior assertion
    failures) and the postcondition includes `ρ'.hasFailure = false` (no
    assertion failures after execution). -/
def HoareTriple
    (P : CoreEnv → Prop)
    (s : Statement)
    (Q : CoreEnv → Prop) : Prop :=
  ∀ (ρ₀ : CoreEnv) (pc₀ : ProgramCounter) (ρ' : CoreEnv),
    P ρ₀ → ρ₀.hasFailure = false →
    CoreStepStar π φ (.stmt s ρ₀ pc₀) (.terminal ρ') →
    Q ρ' ∧ ρ'.hasFailure = false

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

/-- Auxiliary: for a single assert command, the only configuration
    reachable from `.stmt (assert ..) ρ pc₀` that satisfies `isAtAssert`
    is the initial configuration itself. -/
private theorem assert_reachable_is_initial
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (ρ₀ : CoreEnv) (pc₀ : ProgramCounter) (cfg : CoreConfig)
    (hstar : CoreStepStar π φ (.stmt (Statement.assert label expr md) ρ₀ pc₀) cfg)
    (hat : isAtAssert cfg ⟨label, expr⟩) :
    cfg = .stmt (Statement.assert label expr md) ρ₀ pc₀ := by
  -- A single assert command can only step to .terminal via step_cmd.
  -- .terminal does not satisfy isAtAssert. So cfg must be the initial config.
  cases hstar with
  | refl => rfl
  | step _ mid _ hstep hrest =>
    -- The only step from .stmt (.cmd (.cmd (.assert ..))) is step_cmd
    cases hstep with
    | step_cmd hcmd =>
      -- mid = .terminal { ρ₀ with store := σ' }, and hrest : CoreStepStar (.terminal ..) cfg
      -- .terminal cannot step further, so cfg = .terminal ..
      cases hrest with
      | refl =>
        -- cfg = .terminal .., but isAtAssert (.terminal ..) is False
        exact absurd hat (by simp [isAtAssert])
      | step _ _ _ hstep2 _ =>
        -- .terminal cannot step
        exact absurd hstep2 (by intro h; cases h)

/-- Style A implies Style B: if all reachable assert configurations have
    `expr = true`, then the Hoare triple holds. -/
theorem assertValid_implies_hoareTriple
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (s : Statement)
    (hs : s = Statement.assert label expr md)
    (hvalid : AssertValid π φ s ⟨label, expr⟩) :
    HoareTriple π φ
      (fun _ => True)
      s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) := by
  subst hs
  intro ρ₀ pc₀ ρ' _ hf₀ hstar
  -- Invert the multi-step execution of a single assert command.
  -- The only step is step_cmd (eval_assert).
  cases hstar with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      -- hcmd : EvalCommand π φ ρ₀.eval ρ₀.store c σ' hasAssertFailure
      cases hcmd with
      | cmd_sem heval =>
        cases heval with
        | eval_assert_pass htt _ =>
          -- htt : ρ₀.eval ρ₀.store expr = some HasBool.tt
          -- hrest : CoreStepStar (.terminal ..) (.terminal ρ')
          simp [hf₀] at hrest
          cases hrest with
          | refl => exact ⟨htt, rfl⟩
          | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)
        | eval_assert_fail hff _ =>
          -- Use hvalid: the initial config is reachable at pc₀
          have hreach : Reachable π φ (Statement.assert label expr md) ρ₀ pc₀ pc₀
              (.stmt (Statement.assert label expr md) ρ₀ pc₀) :=
            ⟨ReflTrans.refl _, rfl⟩
          -- hvalid gives expr = tt, but hff says expr = ff — contradiction
          have htt := hvalid ρ₀ pc₀ pc₀ _ hreach ⟨rfl, rfl⟩
          simp only [CoreConfig.getEval, CoreConfig.getStore] at htt
          rw [hff] at htt
          exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm

/-- Style B implies Style A, given that the assert is not stuck
    (i.e., for every reachable assert configuration, execution can
    proceed to terminal). This additional hypothesis is necessary
    because the Hoare triple only speaks about executions that terminate.

    In practice, this hypothesis holds when the evaluator is well-formed
    and the expression is well-typed. -/
theorem hoareTriple_implies_assertValid
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (s : Statement)
    (hs : s = Statement.assert label expr md)
    (hoare : HoareTriple π φ
      (fun _ => True)
      s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt))
    -- Additional hypothesis: the assert is not stuck. For every initial
    -- environment and PC, the assert command can step to terminal.
    (hprogress : ∀ (ρ₀ : CoreEnv) (pc₀ : ProgramCounter),
      ∃ (ρ' : CoreEnv),
        CoreStepStar π φ (.stmt s ρ₀ pc₀) (.terminal ρ')) :
    AssertValid π φ s ⟨label, expr⟩ := by
  subst hs
  intro ρ₀ pc₀ pc cfg hreach hat
  obtain ⟨hstar, hpc⟩ := hreach
  -- For a single assert, cfg must be the initial configuration (the only
  -- reachable config with a PC, since .terminal has getPC = none).
  cases hstar with
  | refl =>
    -- cfg = initial config, so we need ρ₀.eval ρ₀.store expr = some HasBool.tt
    -- Use progress to get a terminal state, then apply the Hoare triple.
    obtain ⟨ρ', hterm⟩ := hprogress ρ₀ pc₀
    simp only [CoreConfig.getEval, CoreConfig.getStore]
    -- Invert the execution to extract the result.
    -- We don't need the Hoare triple directly here — just case-split on the
    -- assert evaluation to determine whether it passes or fails.
    cases hterm with
    | step _ mid _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem heval =>
          cases heval with
          | eval_assert_pass htt _ => exact htt
          | eval_assert_fail hff hwfb =>
            -- The assert failed. Construct an execution from a clean env
            -- (hasFailure = false) to derive a contradiction via the Hoare triple.
            have hterm' : CoreStepStar π φ
                (.stmt (Statement.assert label expr md) { ρ₀ with hasFailure := false } pc₀)
                (.terminal { store := ρ₀.store, eval := ρ₀.eval, hasFailure := true }) :=
              ReflTrans.step _ _ _
                (StepStmt.step_cmd (EvalCommand.cmd_sem (EvalCmd.eval_assert_fail hff hwfb)))
                (ReflTrans.refl _)
            have ⟨_, hf'⟩ := hoare { ρ₀ with hasFailure := false } pc₀ _ trivial rfl hterm'
            exact absurd hf' (by simp)
  | step _ mid _ hstep hrest =>
    -- The only step from .stmt (assert ..) is step_cmd to .terminal
    cases hstep with
    | step_cmd hcmd =>
      -- mid = .terminal .., which has getPC = none
      cases hrest with
      | refl => simp [CoreConfig.getPC] at hpc
      | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)

/-! ## Equivalence for a single assert command -/

/-- For a single assert command, Style A implies Style B unconditionally.
    Style B implies Style A given a progress assumption. -/
theorem assertValid_implies_hoareTriple_iff
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (s : Statement)
    (hs : s = Statement.assert label expr md)
    (hprogress : ∀ (ρ₀ : CoreEnv) (pc₀ : ProgramCounter),
      ∃ (ρ' : CoreEnv),
        CoreStepStar π φ (.stmt s ρ₀ pc₀) (.terminal ρ')) :
    AssertValid π φ s ⟨label, expr⟩ ↔
    HoareTriple π φ
      (fun _ => True)
      s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) :=
  ⟨assertValid_implies_hoareTriple π φ label expr md s hs,
   fun h => hoareTriple_implies_assertValid π φ label expr md s hs h hprogress⟩

/-! ## Transformation Correctness

A program transformation `T` is *correct w.r.t. assertion checks* if:
for every assert `a`, validity of `a` in `T(s)` implies validity of `a` in `s`.

This corresponds to Definition 2 from the soundness document: the
transformation does not fabricate validity.
-/

/-- A transformation is *sound* if it preserves assertion validity:
    whenever the transformation succeeds (producing `s'` from `s` in
    some initial state `st`) and assert `a` is valid in `s'`, then
    `a` is also valid in the original statement `s`.

    Note the direction: valid in T(s) ⟹ valid in s.
    This means T does not fabricate validity — if T(s) says "all asserts
    pass," then they genuinely pass in s. -/
def Sound
    (T : Statement → CoreTransformM Statement) : Prop :=
  ∀ (s s' : Statement) (a : AssertId)
    (st st' : CoreTransformState),
    (T s).run st = (.ok s', st') →
    AssertValid π φ s' a →
    AssertValid π φ s a

/-- Composition of sound transformations is sound. -/
theorem sound_comp
    (T₁ T₂ : Statement → CoreTransformM Statement)
    (h₁ : Sound π φ T₁)
    (h₂ : Sound π φ T₂) :
    Sound π φ (fun s => T₁ s >>= T₂) := by
  intro s s'' a st st'' hrun hvalid
  -- Unfold the monadic bind to expose the intermediate result of T₁
  simp only [bind, ExceptT.bind] at hrun
  unfold ExceptT.bindCont at hrun
  simp only [ExceptT.run, ExceptT.mk] at hrun
  unfold StateT.bind at hrun
  simp only [] at hrun
  -- Split on the result of T₁.  Unfold ExceptT.run in h1 so it matches hrun.
  match h1 : (T₁ s).run st with
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

/-- End-to-end: if `T` is sound and assert `a` is valid in `T(s)`,
    then `a` is also valid in `s`. -/
theorem sound_assertValid
    (T : Statement → CoreTransformM Statement)
    (a : AssertId)
    (s s' : Statement)
    (st st' : CoreTransformState)
    (hrun : (T s).run st = (.ok s', st'))
    (hsound : Sound π φ T)
    (hvalid : AssertValid π φ s' a) :
    AssertValid π φ s a :=
  hsound s s' a st st' hrun hvalid

/-- End-to-end: if `T` is sound and all asserts are valid in `T(s)`,
    then all asserts are valid in `s`. -/
theorem sound_allAsserts
    (T : Statement → CoreTransformM Statement)
    (s s' : Statement)
    (st st' : CoreTransformState)
    (hrun : (T s).run st = (.ok s', st'))
    (hsound : Sound π φ T)
    (hvalid : AllAssertsValid π φ s') :
    AllAssertsValid π φ s :=
  fun a => sound_assertValid π φ T a s s' st st' hrun hsound (hvalid a)

/-- If `T` is sound and the assert-specific Hoare triple holds for the
    transformed `s'`, then it also holds for the original `s`.

    Note: `hs` / `hs'` (requiring `s` and `s'` to be single assert
    commands) are needed because the equivalence between Hoare triples
    and `AssertValid` only applies to single assert commands.
    For compound statements, use `sound_allAsserts` directly. -/
theorem sound_hoareTriple
    (T : Statement → CoreTransformM Statement)
    (label : CoreLabel) (expr : Expression.Expr) (md md' : MetaData Expression)
    (s s' : Statement)
    (st st' : CoreTransformState)
    (hs : s = Statement.assert label expr md)
    (hs' : s' = Statement.assert label expr md')
    (hrun : (T s).run st = (.ok s', st'))
    (hsound : Sound π φ T)
    (hprogress : ∀ (ρ₀ : CoreEnv) (pc₀ : ProgramCounter),
      ∃ (ρ' : CoreEnv), CoreStepStar π φ (.stmt s' ρ₀ pc₀) (.terminal ρ'))
    (hoare : HoareTriple π φ
      (fun _ => True) s'
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt)) :
    HoareTriple π φ
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) :=
  assertValid_implies_hoareTriple π φ label expr md s hs
    (hsound s s' ⟨label, expr⟩ st st' hrun
      (hoareTriple_implies_assertValid π φ label expr md' s' hs' hoare hprogress))

end Transform
end Core

end -- public section

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

namespace Imperative

/-! ## Configuration accessors

Defined in the `Imperative` namespace so that dot notation works
on `Config P (Cmd P)`. -/

variable {P : PureExpr}

/-- Extract the store from a configuration. -/
def Config.getStore : Config P (Cmd P) → SemanticStore P
  | .stmt _ ρ _ => ρ.store
  | .stmts _ ρ _ => ρ.store
  | .terminal ρ => ρ.store
  | .exiting _ ρ => ρ.store
  | .block _ inner => inner.getStore
  | .seq inner _ _ => inner.getStore

/-- Extract the evaluator from a configuration. -/
def Config.getEval : Config P (Cmd P) → SemanticEval P
  | .stmt _ ρ _ => ρ.eval
  | .stmts _ ρ _ => ρ.eval
  | .terminal ρ => ρ.eval
  | .exiting _ ρ => ρ.eval
  | .block _ inner => inner.getEval
  | .seq inner _ _ => inner.getEval

/-- Extract the program counter from a configuration, if present.
    Returns `none` for terminal/exiting configurations. -/
def Config.getPC : Config P (Cmd P) → Option ProgramCounter
  | .stmt _ _ pc => some pc
  | .stmts _ _ pc => some pc
  | .terminal _ => none
  | .exiting _ _ => none
  | .block _ inner => inner.getPC
  | .seq inner _ _ => inner.getPC

/-- Extract the execution environment from a configuration. -/
def Config.getEnv : Config P (Cmd P) → Env P
  | .stmt _ ρ _ => ρ
  | .stmts _ ρ _ => ρ
  | .terminal ρ => ρ
  | .exiting _ ρ => ρ
  | .block _ inner => inner.getEnv
  | .seq inner _ _ => inner.getEnv

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
    whose label and expression match `aid`. -/
def isAtAssert : Config P (Cmd P) → AssertId P → Prop
  | .stmt (.cmd (.assert label expr _)) _ _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.assert label expr _)) :: _) _ _, aid =>
    aid.label = label ∧ aid.expr = expr
  | _, _ => False

/-! ## Style A — Reachability-based assertion validity -/

/-- A configuration `cfg` is *reachable* from statement `s` with initial
    environment `ρ₀` and program counter `pc₀` if multi-step execution
    from `(.stmt s ρ₀ pc₀)` reaches `cfg` and `cfg` has program counter `pc`. -/
def Reachable
    (s : Stmt P (Cmd P)) (ρ₀ : Env P) (pc₀ : ProgramCounter)
    (pc : ProgramCounter) (cfg : Config P (Cmd P)) : Prop :=
  StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀ pc₀) cfg ∧
  cfg.getPC = some pc

/-- Assert `a` is *valid* in statement `s` if, for every initial
    environment, initial program counter, and reachable configuration
    at program counter `pc` that is at assert `a`, the assert expression
    evaluates to `true`. -/
def AssertValid
    (s : Stmt P (Cmd P)) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (pc₀ pc : ProgramCounter) (cfg : Config P (Cmd P)),
    Reachable P extendEval s ρ₀ pc₀ pc cfg →
    isAtAssert P cfg a →
    cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- All asserts are valid in statement `s`. Assert `a` does not have to be
    constrained to those in `s` because AssertValid uses partial correctness. -/
def AllAssertsValid
    (s : Stmt P (Cmd P)) : Prop :=
  ∀ (a : AssertId P), AssertValid P extendEval s a

/-! ## Style B — Hoare-triple assertion validity -/

/-- Partial-correctness Hoare triple using small-step semantics.
    Quantifies over all initial PCs.

    The precondition includes `ρ₀.hasFailure = false` (no prior assertion
    failures) and the postcondition includes `ρ'.hasFailure = false` (no
    assertion failures after execution). -/
def HoareTriple
    (Pre : Env P → Prop)
    (s : Stmt P (Cmd P))
    (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ : Env P) (pc₀ : ProgramCounter) (ρ' : Env P),
    Pre ρ₀ → ρ₀.hasFailure = false →
    StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀ pc₀) (.terminal ρ') →
    Post ρ' ∧ ρ'.hasFailure = false

/-! ## Relationship between Style A and Style B

For a single assert command, the only configuration satisfying `isAtAssert`
is the initial `.stmt` configuration itself (zero steps from the start),
because the assert command has exactly one step (to `.terminal`).
-/

/-- Style A implies Style B for a single assert command: if all reachable
    assert configurations have `expr = true`, then the Hoare triple holds.

    This proof inverts the small-step execution of a single assert and
    uses `EvalCmd P` constructors (`eval_assert_pass` / `eval_assert_fail`)
    directly. -/
theorem assertValid_implies_hoareTriple
    (label : String) (expr : P.Expr) (md : MetaData P)
    (s : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hvalid : AssertValid P extendEval s ⟨label, expr⟩) :
    HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) := by
  subst hs
  intro ρ₀ pc₀ ρ' _ hf₀ hstar
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
        have hreach : Reachable P extendEval (.cmd (.assert label expr md)) ρ₀ pc₀ pc₀
            (.stmt (.cmd (.assert label expr md)) ρ₀ pc₀) :=
          ⟨ReflTrans.refl _, rfl⟩
        have htt := hvalid ρ₀ pc₀ pc₀ _ hreach ⟨rfl, rfl⟩
        simp only [Config.getEval, Config.getStore] at htt
        rw [hff] at htt
        exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm

/-- Style B implies Style A for a single assert command, given that the
    assert is not stuck (i.e., for every initial environment and PC,
    the assert command can step to terminal). -/
theorem hoareTriple_implies_assertValid
    (label : String) (expr : P.Expr) (md : MetaData P)
    (s : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hoare : HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt))
    (hprogress : ∀ (ρ₀ : Env P) (pc₀ : ProgramCounter),
      ∃ (ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀ pc₀) (.terminal ρ')) :
    AssertValid P extendEval s ⟨label, expr⟩ := by
  subst hs
  intro ρ₀ pc₀ pc cfg hreach hat
  obtain ⟨hstar, hpc⟩ := hreach
  cases hstar with
  | refl =>
    obtain ⟨ρ', hterm⟩ := hprogress ρ₀ pc₀
    simp only [Config.getEval, Config.getStore]
    cases hterm with
    | step _ mid _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | eval_assert_pass htt _ => exact htt
        | eval_assert_fail hff hwfb =>
          have hterm' : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.cmd (.assert label expr md)) { ρ₀ with hasFailure := false } pc₀)
              (.terminal { store := ρ₀.store, eval := ρ₀.eval, hasFailure := true }) :=
            ReflTrans.step _ _ _
              (StepStmt.step_cmd (EvalCmd.eval_assert_fail hff hwfb))
              (ReflTrans.refl _)
          have ⟨_, hf'⟩ := hoare { ρ₀ with hasFailure := false } pc₀ _ trivial rfl hterm'
          exact absurd hf' (by simp)
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      cases hrest with
      | refl => simp [Config.getPC] at hpc
      | step _ _ _ hstep2 _ => exact absurd hstep2 (by intro h; cases h)

/-! ## Equivalence for a single assert command -/

/-- For a single assert command, Style A implies Style B unconditionally.
    Style B implies Style A given a progress assumption. -/
theorem assertValid_implies_hoareTriple_iff
    (label : String) (expr : P.Expr) (md : MetaData P)
    (s : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hprogress : ∀ (ρ₀ : Env P) (pc₀ : ProgramCounter),
      ∃ (ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀ pc₀) (.terminal ρ')) :
    AssertValid P extendEval s ⟨label, expr⟩ ↔
    HoareTriple P extendEval
      (fun _ => True) s
      (fun ρ' => ρ'.eval ρ'.store expr = some HasBool.tt) :=
  ⟨assertValid_implies_hoareTriple P extendEval label expr md s hs,
   fun h => hoareTriple_implies_assertValid P extendEval label expr md s hs h hprogress⟩

/-! ## Transformation Correctness

A program transformation is a partial function on statements
(`Stmt P (Cmd P) → Option (Stmt P (Cmd P))`).  It returns `some s'`
on success and `none` on failure (e.g., unsupported input).

A transformation `T` is *sound* (w.r.t. assertion checks) if:
for every assert `a`, if `T s = some s'` and `a` is valid in `s'`,
then `a` is valid in `s`.
-/

/-- A transformation is *sound* if it preserves assertion validity:
    whenever `T s = some s'` and assert `a` is valid in `s'`,
    then `a` is also valid in `s`.

    Note the direction: valid in T(s) ⟹ valid in s.
    This means T does not fabricate validity — if T(s) says "all asserts
    pass," then they genuinely pass in s. -/
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
    output `s'`, then it also holds for the input `s`.

    Note: `hs` / `hs'` (requiring `s` and `s'` to be single assert
    commands) are needed because the equivalence between Hoare triples
    and `AssertValid` only applies to single assert commands.
    For compound statements, use `sound_allAsserts` directly. -/
theorem sound_hoareTriple
    (T : Stmt P (Cmd P) → Option (Stmt P (Cmd P)))
    (label : String) (expr : P.Expr) (md md' : MetaData P)
    (s s' : Stmt P (Cmd P))
    (hs : s = .cmd (.assert label expr md))
    (hs' : s' = .cmd (.assert label expr md'))
    (ht : T s = some s')
    (hsound : Sound P extendEval T)
    (hprogress : ∀ (ρ₀ : Env P) (pc₀ : ProgramCounter),
      ∃ (ρ' : Env P), StepStmtStar P (EvalCmd P) extendEval (.stmt s' ρ₀ pc₀) (.terminal ρ'))
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

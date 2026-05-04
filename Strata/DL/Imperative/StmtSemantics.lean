/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Imperative

public section

/-! ## Execution Environment

An `Env` bundles the store, expression evaluator, and a cumulative failure
flag into a single record.  The `hasFailure` flag is OR-ed with the
per-command failure flag returned by `EvalCmdParam` at each `cmd_sem`,
so it monotonically accumulates assertion failures along an execution path.
-/

/-- Execution environment: store, evaluator, and cumulative failure flag. -/
structure Env (P : PureExpr) where
  /-- The current variable store. -/
  store : SemanticStore P
  /-- The current expression evaluator. -/
  eval  : SemanticEval P
  /-- Cumulative failure flag — `true` once any command has signalled failure. -/
  hasFailure : Bool := false

/-- Type of a function that extends the semantic evaluator with a new function definition. -/
@[expose] abbrev ExtendEval (P : PureExpr) := SemanticEval P → SemanticStore P → PureFunc P → SemanticEval P

/-! ## Small-Step Operational Semantics for Statements

This module defines small-step operational semantics for the Imperative
dialect's statement constructs.

Key design decisions:
- `Config.seq` enables truly small-step processing of statement lists.
  Without it, `step_stmt_cons` required the first statement to reach
  terminal in a single step, which prevented blocks (multi-step) from
  being processed inside statement lists.
- `Config.block` holds an inner `Config` (not a statement list + store),
  allowing blocks to observe the execution state of their body at each step.
- `assert` is a skip in the operational semantics (`eval_assert` has no
  precondition). Assertion checking is handled by the verification framework,
  not by execution.
-/

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of:
- The current statement (or list of statements) being executed
- An execution environment (`Env`) bundling store, evaluator, and failure flag
-/
inductive Config (P : PureExpr) (CmdT : Type) : Type where
  /-- A single statement to execute next. -/
  | stmt : Stmt P CmdT → Env P → Config P CmdT
  /-- A list of statements to execute next, in order. -/
  | stmts : List (Stmt P CmdT) → Env P → Config P CmdT
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : Env P → Config P CmdT
  /-- An exiting configuration, indicating that an exit statement was encountered.
      The optional label identifies which block to exit to. -/
  | exiting : Option String → Env P → Config P CmdT
  /-- A block context: execute the inner config, then consume matching exits.
      The label is `Option String` — `none` denotes an unnamed block that only
      catches unlabeled exits. -/
  | block : Option String → Config P CmdT → Config P CmdT
  /-- A sequence context: execute the first statement (as a sub-config), then
      continue with the remaining statements. -/
  | seq : Config P CmdT → List (Stmt P CmdT) → Config P CmdT

/-! ## Configuration accessors -/

variable {P : PureExpr} {CmdT : Type}

/-- Extract the execution environment from a configuration. -/
@[expose] def Config.getEnv : Config P CmdT → Env P
  | .stmt _ ρ => ρ
  | .stmts _ ρ => ρ
  | .terminal ρ => ρ
  | .exiting _ ρ => ρ
  | .block _ inner => inner.getEnv
  | .seq inner _ => inner.getEnv

/-- Extract the store from a configuration. -/
@[expose] def Config.getStore (cfg: Config P CmdT): SemanticStore P
  := cfg.getEnv.store

/-- Extract the evaluator from a configuration. -/
@[expose] def Config.getEval (cfg: Config P CmdT): SemanticEval P
  := cfg.getEnv.eval

/-! ## noMatchingAssert

`noMatchingAssert` checks that a statement, list of statements, or
configuration does not syntactically contain an `assert` command with
a given label.  This is specific to `Cmd P`. -/

/-- `noMatchingAssert` for statements and statement lists.
    Returns `True` when `s` does not syntactically contain any `assert`
    command or loop invariant with the given label. -/
@[expose] def Stmt.noMatchingAssert : Stmt P (Cmd P) → String → Prop
  | .cmd (.assert l _ _), label => l ≠ label
  | .cmd _, _ => True
  | .block _ ss _, label => Stmts.noMatchingAssert ss label
  | .ite _ tss ess _, label =>
    Stmts.noMatchingAssert tss label ∧ Stmts.noMatchingAssert ess label
  | .loop _ _ inv body _, label =>
    (∀ (le : String × P.Expr), le ∈ inv → le.1 ≠ label) ∧
    Stmts.noMatchingAssert body label
  | .exit _ _, _ => True
  | .funcDecl _ _, _ => True
  | .typeDecl _ _, _ => True
where
  /-- Helper for lists of statements. -/
  Stmts.noMatchingAssert : List (Stmt P (Cmd P)) → String → Prop
    | [], _ => True
    | s :: ss, label => s.noMatchingAssert label ∧ Stmts.noMatchingAssert ss label

/-- Extend `noMatchingAssert` to configurations. -/
@[expose] def Config.noMatchingAssert : Config P (Cmd P) → String → Prop
  | .stmt s _, label => s.noMatchingAssert label
  | .stmts ss _, label => Stmt.noMatchingAssert.Stmts.noMatchingAssert ss label
  | .terminal _, _ => True
  | .exiting _ _, _ => True
  | .block _ inner, label => inner.noMatchingAssert label
  | .seq inner ss, label =>
    inner.noMatchingAssert label ∧ Stmt.noMatchingAssert.Stmts.noMatchingAssert ss label

/-- Config-level noFuncDecl predicate. -/
def Config.noFuncDecl : Config P CmdT → Prop
  | .stmt s _ => Stmt.noFuncDecl s = true
  | .stmts ss _ => Block.noFuncDecl ss = true
  | .terminal _ => True
  | .exiting _ _ => True
  | .block _ inner => Config.noFuncDecl inner
  | .seq inner ss => Config.noFuncDecl inner ∧ Block.noFuncDecl ss = true

/-- Extend `exitsCoveredByBlocks` to configurations. -/
@[expose] def Config.exitsCoveredByBlocks : List (Option String) → Config P CmdT → Prop
  | labels, .stmt s _ => s.exitsCoveredByBlocks labels
  | labels, .stmts ss _ => Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss
  | _, .terminal _ => True
  | labels, .exiting none _ => labels.length > 0
  | labels, .exiting (some l) _ => .some l ∈ labels
  | labels, .block l inner => Config.exitsCoveredByBlocks (l :: labels) inner
  | labels, .seq inner ss =>
    Config.exitsCoveredByBlocks labels inner ∧ Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss

/-! ## Single-step relation -/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P]

/--
`StepStmt` defines a single execution step from one configuration to another.
The expression evaluator is part of the `Env` and can be extended by
`funcDecl` statements.  The cumulative failure flag in `Env.hasFailure` is
OR-ed with the per-command failure flag at each `step_cmd`.
-/
inductive StepStmt
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P) :
  Config P CmdT → Config P CmdT → Prop where

  /-- A command steps to terminal configuration if it evaluates successfully.
      Commands preserve the evaluator (ρ'.eval = ρ.eval).
      The per-command failure flag `hasAssertFailure` is OR-ed into
      `ρ.hasFailure` to produce the new environment's flag. -/
  | step_cmd :
    EvalCmd ρ.eval ρ.store c σ' hasAssertFailure →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.cmd c) ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure })

  /-- A labeled block steps to a block context that wraps its body as `.stmts`.
      The AST label `label : String` is lifted into `.some label` for the
      `Config.block` wrapper (whose label is `Option String`). -/
  | step_block :
    StepStmt EvalCmd extendEval
      (.stmt (.block label ss _) ρ)
      (.block (.some label) (.stmts ss ρ))

  /-- If the condition of an `ite` statement evaluates to true, step to the
      then branch. -/
  | step_ite_true :
    ρ.eval ρ.store c = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite (.det c) tss ess _) ρ)
      (.stmts tss ρ)

  /-- If the condition of an `ite` statement evaluates to false, step to the
      else branch. -/
  | step_ite_false :
    ρ.eval ρ.store c = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite (.det c) tss ess _) ρ)
      (.stmts ess ρ)

  /-- Non-deterministic ite: step to the then branch. -/
  | step_ite_nondet_true :
    StepStmt EvalCmd extendEval
      (.stmt (.ite .nondet tss ess _) ρ)
      (.stmts tss ρ)

  /-- Non-deterministic ite: step to the else branch. -/
  | step_ite_nondet_false :
    StepStmt EvalCmd extendEval
      (.stmt (.ite .nondet tss ess _) ρ)
      (.stmts ess ρ)

  /-- If a loop guard is true, execute the body (followed by the loop again).
      Each invariant expression must evaluate to a boolean (`tt` or `ff`);
      otherwise execution is stuck here, just as a non-boolean guard would
      block `step_ite_true`.  If any invariant evaluates to `ff`, the
      cumulative `hasFailure` flag is set via `hasInvFailure`, matching the
      pattern `step_cmd` uses for `assert` failure.  The invariants are
      labeled pairs `(String × P.Expr)`; only the expression part is
      evaluated.

      The body+recursion is wrapped in an unnamed `.block`, so an unlabeled
      `exit` inside the body terminates the loop (and nothing else), while a
      labeled `exit` propagates past the loop. -/
  | step_loop_enter {hasInvFailure : Bool} :
    ρ.eval ρ.store g = .some HasBool.tt →
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop (.det g) m inv body md) ρ)
      (.block .none (.stmts (body ++ [.loop (.det g) m inv body md])
        { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))

  /-- If a loop guard is false, terminate the loop.  As with `step_loop_enter`,
      invariants must be boolean-valued and any `ff` result flips `hasFailure`. -/
  | step_loop_exit {hasInvFailure : Bool} :
    ρ.eval ρ.store g = .some HasBool.ff →
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop (.det g) m inv body _) ρ)
      (.terminal { ρ with hasFailure := ρ.hasFailure || hasInvFailure })

  /-- Non-deterministic loop: enter the body.  Same invariant-boolean
      condition as the deterministic case.  As with the det variant, the
      body is wrapped in an unnamed `.block` so that an unlabeled `exit`
      terminates just the loop. -/
  | step_loop_nondet_enter {hasInvFailure : Bool} :
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    StepStmt EvalCmd extendEval
      (.stmt (.loop .nondet m inv body md) ρ)
      (.block .none (.stmts (body ++ [.loop .nondet m inv body md])
        { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))

  /-- Non-deterministic loop: exit the loop. -/
  | step_loop_nondet_exit {hasInvFailure : Bool} :
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    StepStmt EvalCmd extendEval
      (.stmt (.loop .nondet m inv body _) ρ)
      (.terminal { ρ with hasFailure := ρ.hasFailure || hasInvFailure })

  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
    StepStmt EvalCmd extendEval
      (.stmt (.exit label _) ρ)
      (.exiting label ρ)

  /-- A function declaration extends the evaluator with the new function. -/
  | step_funcDecl [HasSubstFvar P] [HasVarsPure P P.Expr] :
    StepStmt EvalCmd extendEval
      (.stmt (.funcDecl decl md) ρ)
      (.terminal { ρ with eval := extendEval ρ.eval ρ.store decl })

  /-- A type declaration is a no-op at runtime. -/
  | step_typeDecl :
    StepStmt EvalCmd extendEval
      (.stmt (.typeDecl _tc _md) ρ)
      (.terminal ρ)

  /-- An empty list of statements steps to `.terminal` with no state changes. -/
  | step_stmts_nil :
    StepStmt EvalCmd extendEval
      (.stmts [] ρ)
      (.terminal ρ)

  /-- To evaluate a non-empty sequence, enter a seq context that processes
      the first statement while remembering the remaining statements. -/
  | step_stmts_cons :
    StepStmt EvalCmd extendEval
      (.stmts (s :: ss) ρ)
      (.seq (.stmt s ρ) ss)

  /-- A seq context steps its inner config forward. -/
  | step_seq_inner :
    StepStmt EvalCmd extendEval inner inner' →
    ----
    StepStmt EvalCmd extendEval
      (.seq inner ss)
      (.seq inner' ss)

  /-- When the inner config of a seq reaches terminal, continue with the
      remaining statements. -/
  | step_seq_done :
    StepStmt EvalCmd extendEval
      (.seq (.terminal ρ') ss)
      (.stmts ss ρ')

  /-- When the inner config of a seq exits, propagate the exit
      (skip remaining statements). -/
  | step_seq_exit :
    StepStmt EvalCmd extendEval
      (.seq (.exiting label ρ') ss)
      (.exiting label ρ')

  /-- A block context steps its inner body one step forward.
      The inner body can be any config (stmts, seq, etc.). -/
  | step_block_body :
    StepStmt EvalCmd extendEval inner inner' →
    ----
    StepStmt EvalCmd extendEval
      (.block label inner)
      (.block label inner')

  /-- When a block's inner body reaches terminal, the block terminates. -/
  | step_block_done :
    StepStmt EvalCmd extendEval
      (.block label (.terminal ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with no label, the block consumes the exit
      (regardless of the block's own label). -/
  | step_block_exit_none :
    StepStmt EvalCmd extendEval
      (.block label (.exiting .none ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with a matching label, the block consumes it. -/
  | step_block_exit_match :
    label = .some l →
    ----
    StepStmt EvalCmd extendEval
      (.block label (.exiting (.some l) ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with a non-matching label, the exit propagates.
      "Non-matching" covers both the unnamed-block (`.none`) case and any other
      mismatched `some` label. -/
  | step_block_exit_mismatch :
    label ≠ .some l →
    ----
    StepStmt EvalCmd extendEval
      (.block label (.exiting (.some l) ρ'))
      (.exiting (.some l) ρ')

end

/-! ## Multi-step execution: reflexive transitive closure of single steps. -/

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)

/-- A multi-step execution of Imperative. -/
abbrev StepStmtStar :
    Config P CmdT → Config P CmdT → Prop :=
  ReflTrans (StepStmt P EvalCmd extendEval)

/-- A statement evaluates successfully if it steps to a terminal configuration. -/
abbrev EvalStmtSmall
    (ρ : Env P) (s : Stmt P CmdT)
    (ρ' : Env P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')

/-- A list of statements evaluates successfully if it steps to a terminal
    configuration. -/
abbrev EvalStmtsSmall
    (ρ : Env P) (ss : List (Stmt P CmdT))
    (ρ' : Env P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.terminal ρ')

---------------------------------------------------------------------

/-! ## Basic Properties and Theorems -/

/-- Empty statement list evaluation. -/
theorem evalStmtsSmallNil
    (ρ : Env P) :
    EvalStmtsSmall P EvalCmd extendEval ρ [] ρ := by
  unfold EvalStmtsSmall
  exact .step _ _ _ StepStmt.step_stmts_nil (.refl _)

/-- Configuration is terminal if no further steps are possible. -/
def IsTerminal
    (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd extendEval c c'

/-- Terminal configurations are indeed terminal. -/
theorem terminalIsTerminal
    (ρ : Env P) :
    IsTerminal P EvalCmd extendEval (.terminal ρ) := by
  unfold IsTerminal
  intro c' h
  cases h

/-!
### Stepping through a statement list

When executing `.stmts (s :: ss) ρ`, the semantics first enters a
`.seq` context (via `step_stmts_cons`), executes `s` to terminal, then
resumes with `.stmts ss ρ'`.

The proof proceeds in two parts:
1. A helper lemma (`seq_inner_star`) showing that multi-step execution of
   the inner config lifts to multi-step execution of the enclosing `.seq`.
2. The main theorem (`stmts_cons_step`) composing the pieces.
-/

/-- Helper: if the inner config of a `.seq` takes multiple steps, the
    enclosing `.seq` takes the same number of steps.
    Proved by induction on the multi-step derivation. -/
theorem seq_inner_star
    (inner inner' : Config P CmdT)
    (ss : List (Stmt P CmdT))
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval
      (.seq inner ss)
      (.seq inner' ss) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih =>
    exact .step _ _ _ (.step_seq_inner hstep) ih

/-- Helper: if the inner config of a `.block` takes multiple steps, the
    enclosing `.block` takes the same number of steps. -/
theorem block_inner_star
    (inner inner' : Config P CmdT)
    (label : Option String)
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval (.block label inner) (.block label inner') := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_block_body hstep) ih

/-- When executing `.stmts (s :: ss) ρ`, if the head statement `s`
    multi-steps to `.terminal ρ'`, then the whole list multi-steps to
    `.stmts ss ρ'`.

    This captures the fundamental sequencing behaviour of statement lists
    in the small-step semantics. -/
theorem stmts_cons_step
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT))
    (ρ ρ' : Env P)
    (hstmt : StepStmtStar P EvalCmd extendEval
      (.stmt s ρ) (.terminal ρ')) :
    StepStmtStar P EvalCmd extendEval
      (.stmts (s :: ss) ρ)
      (.stmts ss ρ') := by
  -- Step 1: .stmts (s :: ss) ρ  →  .seq (.stmt s ρ) ss
  --         via step_stmts_cons
  apply ReflTrans.step _ (.seq (.stmt s ρ) ss)
  · exact .step_stmts_cons
  -- Step 2: .seq (.stmt s ρ) ss  →*  .seq (.terminal ρ') ss
  --         by lifting hstmt through the seq context
  have h2 := seq_inner_star P EvalCmd extendEval _ _ ss hstmt
  -- Step 3: .seq (.terminal ρ') ss  →  .stmts ss ρ'
  --         via step_seq_done, then chain with h2 by induction
  suffices h3 : StepStmtStar P EvalCmd extendEval
      (.seq (.terminal ρ') ss) (.stmts ss ρ') from
    ReflTrans_Transitive _ _ _ _ h2 h3
  exact .step _ _ _ .step_seq_done (.refl _)

/-! ## Inversion lemmas for seq and block execution -/

/-- Invert a seq execution reaching terminal: the inner terminates,
    then the tail stmts run to terminal. -/
theorem seq_reaches_terminal
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.seq inner ss) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.terminal ρ') := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ss ρ', src = .seq inner ss → tgt = .terminal ρ' →
      ∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
        StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.terminal ρ') from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ss ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      have ⟨ρ₁, hterm, htail⟩ := ih _ _ _ rfl htgt
      exact ⟨ρ₁, .step _ _ _ h hterm, htail⟩
    | step_seq_done => subst htgt; exact ⟨_, .refl _, hrest⟩
    | step_seq_exit => subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Invert a seq execution reaching exiting: either the inner exited
    (propagated), or the inner terminated and the tail exited. -/
theorem seq_reaches_exiting
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {lbl : Option String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.seq inner ss) (.exiting lbl ρ')) :
    (StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ')) ∨
    (∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.exiting lbl ρ')) := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ss lbl ρ', src = .seq inner ss → tgt = .exiting lbl ρ' →
      (StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ')) ∨
      (∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
        StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.exiting lbl ρ')) from
    this _ _ hstar _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ss lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      match ih _ _ _ _ rfl htgt with
      | .inl hexit => exact .inl (.step _ _ _ h hexit)
      | .inr ⟨ρ₁, hterm, htail⟩ => exact .inr ⟨ρ₁, .step _ _ _ h hterm, htail⟩
    | step_seq_done => subst htgt; exact .inr ⟨_, .refl _, hrest⟩
    | step_seq_exit => exact .inl (htgt ▸ hrest)

/-- Invert a block execution reaching terminal: the inner either
    terminated or exited (caught by the block). -/
theorem block_reaches_terminal
    {inner : Config P CmdT} {l : Option String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l inner) (.terminal ρ')) :
    StepStmtStar P EvalCmd extendEval inner (.terminal ρ') ∨
    (∃ lbl, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ')) := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ρ', src = .block l inner → tgt = .terminal ρ' →
      StepStmtStar P EvalCmd extendEval inner (.terminal ρ') ∨
      (∃ lbl, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ')) from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl hterm => exact .inl (.step _ _ _ h hterm)
      | .inr ⟨lbl, hexit⟩ => exact .inr ⟨lbl, .step _ _ _ h hexit⟩
    | step_block_done => subst htgt; exact .inl hrest
    | step_block_exit_none =>
      subst htgt; cases hrest with
      | refl => exact .inr ⟨.none, .refl _⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with
      | refl => exact .inr ⟨.some _, .refl _⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Invert a block execution reaching exiting: the inner must have
    exited with a label that didn't match the block. -/
theorem block_reaches_exiting
    {inner : Config P CmdT} {l : Option String} {lbl : Option String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l inner) (.exiting lbl ρ')) :
    ∃ lbl_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl_inner ρ') := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner lbl ρ', src = .block l inner → tgt = .exiting lbl ρ' →
      ∃ lbl_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl_inner ρ') from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨lbl_inner, hexit⟩ := ih _ _ _ rfl htgt
      exact ⟨lbl_inner, .step _ _ _ h hexit⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_none =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, .refl _⟩
      | step _ _ _ h _ => cases h

/-! ## Trace construction helpers -/

/-- Entering a block: a single step from `.stmt (.block l body md) ρ`
    to `.block (.some l) (.stmts body ρ)`. -/
theorem step_block_enter (l : String) (body : List (Stmt P CmdT))
    (md : MetaData P) (ρ : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.stmt (.block l body md) ρ) (.block (.some l) (.stmts body ρ)) :=
  .step _ _ _ .step_block (.refl _)

/-- If a prefix of a statement list terminates, the full list steps
    to the suffix starting from the terminal environment. -/
theorem stmts_prefix_terminal_append
    (pfx sfx : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmts pfx ρ) (.terminal ρ')) :
    StepStmtStar P EvalCmd extendEval (.stmts (pfx ++ sfx) ρ) (.stmts sfx ρ') := by
  induction pfx generalizing ρ with
  | nil =>
    cases h with
    | step _ _ _ h_step h_rest => cases h_step with
      | step_stmts_nil => cases h_rest with
        | refl => exact .refl _
        | step _ _ _ h _ => exact nomatch h
  | cons s rest ih =>
    cases h with
    | step _ _ _ h_step h_rest => cases h_step with
      | step_stmts_cons =>
        have ⟨ρ₁, h_s, h_r⟩ := seq_reaches_terminal P EvalCmd extendEval h_rest
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P EvalCmd extendEval s (rest ++ sfx) ρ ρ₁ h_s) (ih ρ₁ h_r)

/-- Decompose a terminating execution of `ss₁ ++ ss₂` into a terminating
    execution of `ss₁` followed by a terminating execution of `ss₂`. -/
theorem stmts_append_terminates
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmts (ss₁ ++ ss₂) ρ) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmd extendEval (.stmts ss₁ ρ) (.terminal ρ₁) ∧
           StepStmtStar P EvalCmd extendEval (.stmts ss₂ ρ₁) (.terminal ρ') := by
  induction ss₁ generalizing ρ with
  | nil =>
    exact ⟨ρ, .step _ _ _ .step_stmts_nil (.refl _), h⟩
  | cons s rest ih =>
    cases h with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ_mid, h_s, h_rest_ss₂⟩ :=
          seq_reaches_terminal P EvalCmd extendEval hrest
        have ⟨ρ₁, h_rest, h_ss₂⟩ := ih ρ_mid h_rest_ss₂
        exact ⟨ρ₁, ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P EvalCmd extendEval
            s rest ρ ρ_mid h_s) h_rest, h_ss₂⟩

/-- Try every non-recursive `StepStmt` constructor, using `‹_›` (term-level
    assumption) to fill arguments so that no hypothesis names are needed. -/
local macro "apply_step" : tactic => `(tactic| first
  | exact .step_cmd ‹_›        | exact .step_ite_true ‹_› ‹_›
  | exact .step_ite_false ‹_› ‹_›
  | exact .step_loop_enter ‹_› ‹_› ‹_› ‹_›
  | exact .step_loop_exit ‹_› ‹_› ‹_› ‹_›
  | exact .step_block
  | exact .step_exit            | exact .step_funcDecl
  | exact .step_typeDecl        | exact .step_stmts_nil
  | exact .step_stmts_cons)

/-! ## Store/eval simulation and hasFailure irrelevance -/

/-- Two configs agree on store/eval (may differ on hasFailure). -/
private def ConfigSE : Config P CmdT → Config P CmdT → Prop
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
    (c₁ c₁' c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₁')
    (heq : ConfigSE P c₁ c₂) :
    ∃ c₂', StepStmt P EvalCmd extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' := by
  cases hstep with
  -- Non-recursive cases where c₁ is `.stmt` or `.stmts`: exactly one c₂
  -- constructor is valid, and the output ConfigSE follows by `simp_all`.
  | step_cmd _ | step_block | step_ite_true _ _ | step_ite_false _ _
  | step_loop_enter _ _ _ _ | step_loop_exit _ _ _ _
  | step_exit | step_funcDecl | step_typeDecl | step_stmts_nil | step_stmts_cons =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; subst hs; subst he
    exact ⟨_, by apply_step, by simp_all [ConfigSE]⟩
  | step_ite_nondet_true =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_ite_nondet_true, by simp [ConfigSE]⟩
  | step_ite_nondet_false =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_ite_nondet_false, by simp [ConfigSE]⟩
  | step_loop_nondet_enter _ _ =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_loop_nondet_enter ‹_› ‹_›, by simp_all [ConfigSE]⟩
  | step_loop_nondet_exit _ _ =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_loop_nondet_exit ‹_› ‹_›, by simp_all [ConfigSE]⟩
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
    (s : Stmt P CmdT) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')) :
    ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
    ∃ ρ₂', StepStmtStar P EvalCmd extendEval (.stmt s ρ₂) (.terminal ρ₂') ∧
      ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval := by
  intro ρ₂ hs he
  suffices ∀ (c₁ c₂ : Config P CmdT),
      ConfigSE P c₁ c₂ →
      ∀ c₁', StepStmtStar P EvalCmd extendEval c₁ c₁' →
      ∃ c₂', StepStmtStar P EvalCmd extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' by
    have heq_init : ConfigSE P (.stmt s ρ) (.stmt s ρ₂) := ⟨rfl, hs.symm, he.symm⟩
    have ⟨c₂', hstar₂, heq₂⟩ := this _ _ heq_init _ h
    match c₂', heq₂ with
    | .terminal ρ₂', heq_t => exact ⟨ρ₂', hstar₂, heq_t.1.symm, heq_t.2.symm⟩
  intro c₁ c₂ heq c₁' hstar
  induction hstar generalizing c₂ with
  | refl => exact ⟨c₂, .refl _, heq⟩
  | step _ mid _ hstep _ ih =>
    have ⟨mid₂, hstep₂, heq_mid⟩ := step_simulation P EvalCmd extendEval _ _ _ hstep heq
    have ⟨c₂', hstar₂, heq_final⟩ := ih _ heq_mid
    exact ⟨c₂', .step _ _ _ hstep₂ hstar₂, heq_final⟩

/-! ## Well-paired exits: preservation and no-escape -/

/-- A single step preserves `Config.exitsCoveredByBlocks`. -/
public theorem step_preserves_exitsCoveredByBlocks
    (labels : List (Option String))
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hwp : c₁.exitsCoveredByBlocks labels) :
    c₂.exitsCoveredByBlocks labels := by
  -- Prove a generalized version where labels is universally quantified,
  -- so the IH works at any nesting depth (needed for step_block_body).
  suffices ∀ c₁ c₂, StepStmt P EvalCmd extendEval c₁ c₂ →
      ∀ labels, c₁.exitsCoveredByBlocks labels → c₂.exitsCoveredByBlocks labels by
    exact this c₁ c₂ hstep labels hwp
  intro c₁ c₂ hstep
  induction hstep with
  | step_cmd => intro _ _; trivial
  | step_block => intro _ hwp; exact hwp
  | step_ite_true => intro _ hwp; exact hwp.1
  | step_ite_false => intro _ hwp; exact hwp.2
  | step_ite_nondet_true => intro _ hwp; exact hwp.1
  | step_ite_nondet_false => intro _ hwp; exact hwp.2
  | step_loop_enter _ _ =>
    intro labels hwp
    -- Goal: (.block .none (.stmts (body ++ [.loop ...]) ρ')) covers labels
    --  ↔ .stmts (body ++ [...]) covers (none :: labels).
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    have hbody := (exitsCoveredByBlocks_weaken (P := P) (CmdT := CmdT)
      labels (.none :: labels) (fun l hl => .tail _ hl)).2 _ hwp
    exact block_exitsCoveredByBlocks_append (P := P) (CmdT := CmdT) (.none :: labels) _ _
      hbody ⟨hbody, True.intro⟩
  | step_loop_exit => intro _ _; trivial
  | step_loop_nondet_enter =>
    intro labels hwp
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    have hbody := (exitsCoveredByBlocks_weaken (P := P) (CmdT := CmdT)
      labels (.none :: labels) (fun l hl => .tail _ hl)).2 _ hwp
    exact block_exitsCoveredByBlocks_append (P := P) (CmdT := CmdT) (.none :: labels) _ _
      hbody ⟨hbody, True.intro⟩
  | step_loop_nondet_exit => intro _ _; trivial
  | step_exit =>
    intro labels hwp
    -- hwp is about .stmt (.exit lbl md) but goal is about .exiting lbl
    -- Both pattern-match on the Option lbl; case split to reduce.
    revert hwp; cases ‹Option String› <;> exact id
  | step_funcDecl => intro _ _; trivial
  | step_typeDecl => intro _ _; trivial
  | step_stmts_nil => intro _ _; trivial
  | step_stmts_cons => intro _ hwp; exact ⟨hwp.1, hwp.2⟩
  | step_seq_inner _ ih => intro labels hwp; exact ⟨ih labels hwp.1, hwp.2⟩
  | step_seq_done => intro _ hwp; exact hwp.2
  | step_seq_exit => intro _ hwp; exact hwp.1
  | step_block_body _ ih => intro labels hwp; exact ih _ hwp
  | step_block_done => intro _ _; trivial
  | step_block_exit_none => intro _ _; trivial
  | step_block_exit_match => intro _ _; trivial
  | step_block_exit_mismatch hne =>
    intro labels hwp
    simp only [Config.exitsCoveredByBlocks, List.mem_cons] at hwp ⊢
    exact hwp.resolve_left (fun h => hne (h ▸ rfl))

/-- Well-paired statements cannot escape via `.exiting`:
    if all exits in `s` are caught by enclosing blocks
    (`s.exitsCoveredByBlocks []`), then `s` never reaches `.exiting`. -/
theorem exitsCoveredByBlocks_noEscape
    (s : Stmt P CmdT)
    (hwp : s.exitsCoveredByBlocks []) :
    ∀ (ρ : Env P) (lbl : Option String) (ρ' : Env P),
      ¬ StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.exiting lbl ρ') := by
  intro ρ lbl ρ' hstar
  -- Prove Config.exitsCoveredByBlocks [] is preserved, then show .exiting contradicts it.
  suffices ∀ c₁ c₂,
      c₁.exitsCoveredByBlocks ([] : List (Option String)) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List (Option String)) by
    have hwp' := this _ _ (show Config.exitsCoveredByBlocks [] (.stmt s ρ) from hwp) hstar
    -- Config.exitsCoveredByBlocks [] (.exiting lbl ρ') requires:
    --   lbl = none → [].length > 0 (False)
    --   lbl = some l → l ∈ [] (False)
    cases lbl with
    | none => exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
    | some l => exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ c₂ hwp_c hstar_c
  induction hstar_c with
  | refl => exact hwp_c
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_exitsCoveredByBlocks P EvalCmd extendEval [] _ _ hstep hwp_c)

/-- Well-paired statement lists cannot escape via `.exiting`:
    if all exits in `bss` are caught by enclosing blocks
    (`Block.exitsCoveredByBlocks [] bss`), then `.stmts bss ρ` never reaches `.exiting`. -/
theorem block_exitsCoveredByBlocks_noEscape
    (bss : List (Stmt P CmdT))
    (hwp : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks [] bss) :
    ∀ (ρ : Env P) (lbl : Option String) (ρ' : Env P),
      ¬ StepStmtStar P EvalCmd extendEval (.stmts bss ρ) (.exiting lbl ρ') := by
  intro ρ lbl ρ' hstar
  suffices ∀ c₁ c₂,
      c₁.exitsCoveredByBlocks ([] : List (Option String)) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List (Option String)) by
    have hwp' := this _ _ (show Config.exitsCoveredByBlocks [] (.stmts bss ρ) from hwp) hstar
    cases lbl with
    | none => exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
    | some l => exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ c₂ hwp_c hstar_c
  induction hstar_c with
  | refl => exact hwp_c
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_exitsCoveredByBlocks P EvalCmd extendEval [] _ _ hstep hwp_c)

/-- If `.block l inner →* cfg`, the inner config never reaches `.exiting`,
    and `cfg` is neither terminal nor exiting, then `cfg = .block l inner'`
    for some `inner'` with `inner →* inner'`. -/
theorem block_star_extract_inner
    {l : Option String} {inner cfg : Config P CmdT}
    (h_star : StepStmtStar P EvalCmd extendEval (.block l inner) cfg)
    (h_no_exit : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval
        inner (.exiting lbl ρ'))
    (h_not_terminal : ∀ ρ', cfg ≠ .terminal ρ')
    (h_not_exiting : ∀ lbl ρ', cfg ≠ .exiting lbl ρ') :
    ∃ inner', cfg = .block l inner' ∧
      StepStmtStar P EvalCmd extendEval inner inner' := by
  suffices ∀ c₁ c₂,
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      ∀ inner₀, c₁ = .block l inner₀ →
      (∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval inner₀ (.exiting lbl ρ')) →
      (∀ ρ', c₂ ≠ .terminal ρ') → (∀ lbl ρ', c₂ ≠ .exiting lbl ρ') →
      ∃ inner', c₂ = .block l inner' ∧
        StepStmtStar P EvalCmd extendEval inner₀ inner' from
    this _ _ h_star _ rfl h_no_exit h_not_terminal h_not_exiting
  intro c₁ c₂ h_star
  induction h_star with
  | refl => intro inner₀ heq _ _ _; subst heq; exact ⟨inner₀, rfl, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner₀ heq h_ne h_nt h_nx; subst heq
    cases hstep with
    | step_block_body h_inner_step =>
      have h_ne' : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval _ (.exiting lbl ρ') :=
        fun lbl ρ' h => h_ne lbl ρ' (.step _ _ _ h_inner_step h)
      obtain ⟨inner', rfl, h_inner_star⟩ := ih _ rfl h_ne' h_nt h_nx
      exact ⟨inner', rfl, .step _ _ _ h_inner_step h_inner_star⟩
    | step_block_done =>
      cases hrest with
      | refl => exact absurd rfl (h_nt _)
      | step _ _ _ h _ => exact nomatch h
    | step_block_exit_none => exact absurd (.refl _) (h_ne _ _)
    | step_block_exit_match => exact absurd (.refl _) (h_ne _ _)
    | step_block_exit_mismatch => exact absurd (.refl _) (h_ne _ _)

/-! ## noFuncDecl preserves eval (small-step) -/

/-- A single step preserves eval when noFuncDecl holds.
    The only step that changes eval is step_funcDecl, which is excluded. -/
private theorem step_preserves_eval_noFuncDecl
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hnofd : Config.noFuncDecl c₁) :
    c₂.getEnv.eval = c₁.getEnv.eval ∧ Config.noFuncDecl c₂ := by
  suffices ∀ c₁ c₂, StepStmt P EvalCmd extendEval c₁ c₂ →
      ∀ (_ : Config.noFuncDecl c₁),
      c₂.getEnv.eval = c₁.getEnv.eval ∧ Config.noFuncDecl c₂ by
    exact this c₁ c₂ hstep hnofd
  intro c₁ c₂ hstep
  induction hstep with
  | step_cmd => intro _; exact ⟨rfl, trivial⟩
  | step_block =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
    exact ⟨rfl, hnofd⟩
  | step_ite_true =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.1⟩
  | step_ite_false =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.2⟩
  | step_ite_nondet_true =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.1⟩
  | step_ite_nondet_false =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.2⟩
  | step_loop_enter =>
    intro hnofd
    refine ⟨rfl, ?_⟩
    simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
    -- Need: Block.noFuncDecl (body ++ [loop]) from Block.noFuncDecl body
    have h_append : ∀ (ss₁ ss₂ : List (Stmt P CmdT)),
        Block.noFuncDecl ss₁ = true → Block.noFuncDecl ss₂ = true →
        Block.noFuncDecl (ss₁ ++ ss₂) = true := by
      intro ss₁; induction ss₁ with
      | nil => intro _ _ h; exact h
      | cons s ss ih =>
        intro ss₂ h₁ h₂
        simp only [Block.noFuncDecl] at h₁ ⊢
        cases hs : Stmt.noFuncDecl s
        · simp [hs] at h₁
        · simp_all [Block.noFuncDecl]
    exact h_append _ _ hnofd (by simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd])
  | step_loop_exit => intro _; exact ⟨rfl, trivial⟩
  | step_loop_nondet_enter =>
    intro hnofd
    refine ⟨rfl, ?_⟩
    simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
    have h_append : ∀ (ss₁ ss₂ : List (Stmt P CmdT)),
        Block.noFuncDecl ss₁ = true → Block.noFuncDecl ss₂ = true →
        Block.noFuncDecl (ss₁ ++ ss₂) = true := by
      intro ss₁; induction ss₁ with
      | nil => intro _ _ h; exact h
      | cons s ss ih =>
        intro ss₂ h₁ h₂
        simp only [Block.noFuncDecl] at h₁ ⊢
        cases hs : Stmt.noFuncDecl s
        · simp [hs] at h₁
        · simp_all [Block.noFuncDecl]
    exact h_append _ _ hnofd (by simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd])
  | step_loop_nondet_exit => intro _; exact ⟨rfl, trivial⟩
  | step_exit => intro _; exact ⟨rfl, trivial⟩
  | step_funcDecl =>
    intro hnofd; simp [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd
  | step_typeDecl => intro _; exact ⟨rfl, trivial⟩
  | step_stmts_nil => intro _; exact ⟨rfl, trivial⟩
  | step_stmts_cons =>
    intro hnofd
    refine ⟨rfl, ?_⟩
    simp only [Config.noFuncDecl, Block.noFuncDecl, Bool.and_eq_true] at hnofd ⊢
    exact hnofd
  | step_seq_inner _ ih =>
    intro hnofd
    have ⟨heq, hnofd'⟩ := ih hnofd.1
    exact ⟨heq, hnofd', hnofd.2⟩
  | step_seq_done => intro hnofd; exact ⟨rfl, hnofd.2⟩
  | step_seq_exit => intro _; exact ⟨rfl, trivial⟩
  | step_block_body _ ih => intro hnofd; exact ih hnofd
  | step_block_done => intro _; exact ⟨rfl, trivial⟩
  | step_block_exit_none => intro _; exact ⟨rfl, trivial⟩
  | step_block_exit_match => intro _; exact ⟨rfl, trivial⟩
  | step_block_exit_mismatch => intro _; exact ⟨rfl, trivial⟩

/-- When a statement has no function declarations, small-step execution
    preserves the evaluator. -/
theorem smallStep_noFuncDecl_preserves_eval
    (s : Stmt P CmdT) (ρ ρ' : Env P)
    (hnofd : Stmt.noFuncDecl s = true)
    (hstar : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmt s ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-- When a block has no function declarations, small-step execution
    preserves the evaluator. -/
theorem smallStep_noFuncDecl_preserves_eval_block
    (bss : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (hnofd : Block.noFuncDecl bss = true)
    (hstar : StepStmtStar P EvalCmd extendEval (.stmts bss ρ) (.terminal ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmts bss ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-- Alias for `smallStep_noFuncDecl_preserves_eval_block`, matching the
    `Block.noFuncDecl` naming convention. -/
theorem block_noFuncDecl_preserves_eval
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (hnofd : Block.noFuncDecl ss = true)
    (hterm : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.terminal ρ')) :
    ρ'.eval = ρ.eval :=
  smallStep_noFuncDecl_preserves_eval_block P EvalCmd extendEval ss ρ ρ' hnofd hterm

end -- section

section

variable (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P]
variable (extendEval : ExtendEval P)

/-! ## Assertion Identity -/

/-- An assertion identifier: the label + expression attached to an
    `assert` command. -/
structure AssertId where
  label : String
  expr  : P.Expr

/-! ## Detecting an assert in a configuration -/

/-- `isAtAssert cfg aid` holds when the head of `cfg` is either an `assert`
    command whose label and expression match `aid`, or a loop statement
    whose invariant list contains an entry with matching label and
    expression.  Recurses into `block` and `seq` wrappers so that
    assertions inside compound statements are visible. -/
@[expose] def isAtAssert : Config P (Cmd P) → AssertId P → Prop
  | .stmt (.cmd (.assert label expr _)) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.assert label expr _)) :: _) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmt (.loop _ _ inv _ _) _, aid => (aid.label, aid.expr) ∈ inv
  | .stmts ((.loop _ _ inv _ _) :: _) _, aid => (aid.label, aid.expr) ∈ inv
  | .block _ inner, aid => isAtAssert inner aid
  | .seq inner _, aid => isAtAssert inner aid
  | _, _ => False

omit [HasFvar P] [HasBool P] [HasNot P] in
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
  | .stmt (.cmd (.assume ..)) _
  | .stmt (.cmd (.cover ..)) _
  | .stmt (.block ..) _ | .stmt (.ite ..) _
  | .stmt (.exit ..) _ | .stmt (.funcDecl ..) _ | .stmt (.typeDecl ..) _ =>
    simp [isAtAssert]
  | .stmt (.loop _ _ inv _ _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno
    intro hat
    exact hno.1 label expr hat rfl
  | .stmts [] _ => simp [isAtAssert]
  | .stmts ((.cmd (.assert l _ _)) :: _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert.Stmts.noMatchingAssert, Stmt.noMatchingAssert] at hno
    simp [isAtAssert]; exact fun h _ => hno.1 (h ▸ rfl)
  | .stmts ((.cmd (.init ..)) :: _) _ | .stmts ((.cmd (.set ..)) :: _) _
  | .stmts ((.cmd (.assume ..)) :: _) _
  | .stmts ((.cmd (.cover ..)) :: _) _
  | .stmts ((.block ..) :: _) _ | .stmts ((.ite ..) :: _) _
  | .stmts ((.exit ..) :: _) _
  | .stmts ((.funcDecl ..) :: _) _ | .stmts ((.typeDecl ..) :: _) _ =>
    simp [isAtAssert]
  | .stmts ((.loop _ _ inv _ _) :: _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert.Stmts.noMatchingAssert,
      Stmt.noMatchingAssert] at hno
    intro hat
    exact hno.1.1 label expr hat rfl
  | .terminal _ | .exiting _ _ => simp [isAtAssert]
  | .block _ inner => exact noMatchingAssert_not_isAtAssert inner label expr hno
  | .seq inner _ => exact noMatchingAssert_not_isAtAssert inner label expr hno.1

omit [HasFvar P] [HasBool P] [HasNot P] in
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
  | step_ite_nondet_true => exact hno.1
  | step_ite_nondet_false => exact hno.2
  | step_loop_enter =>
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    apply stmts_noMatchingAssert_append
    · exact hno.2
    · exact ⟨hno, True.intro⟩
  | step_loop_exit => trivial
  | step_loop_nondet_enter =>
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    apply stmts_noMatchingAssert_append
    · exact hno.2
    · exact ⟨hno, True.intro⟩
  | step_loop_nondet_exit => trivial
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

/-! ## isAtAssert inversion lemmas -/

/-- If execution inside a block reaches a config where isAtAssert holds,
    then the config must be `.block label inner` where `inner` is reachable
    from the block's body and satisfies `isAtAssert`. -/
theorem block_isAtAssert_inner
    (label : String) (inner₀ cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.block label inner₀) cfg)
    (hat : isAtAssert P cfg a) :
    ∃ inner, cfg = .block label inner ∧
      StepStmtStar P (EvalCmd P) extendEval inner₀ inner ∧
      isAtAssert P inner a := by
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
theorem seq_isAtAssert_cases
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

/-- For a single assert command, any config reachable from `.stmts [assert] ρ`
    that satisfies `isAtAssert` has getEval = ρ.eval and getStore = ρ.store. -/
theorem assert_tail_getEvalStore
    (ρ : Env P) (l : String) (e : P.Expr) (md : MetaData P)
    (cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [Stmt.cmd (Cmd.assert l e md)] ρ) cfg)
    (hat : isAtAssert P cfg a) :
    cfg.getEval = ρ.eval ∧ cfg.getStore = ρ.store := by
  cases hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ h1 hr1 => cases h1 with
    | step_stmts_cons => cases hr1 with
      | refl => exact ⟨rfl, rfl⟩
      | step _ _ _ h2 hr2 =>
        cases h2 with
        | step_seq_inner hi =>
          cases hi with
          | step_cmd =>
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

/-! ## hasFailure preservation

The lemmas below are abstract over the command type `CmdT`, the command
evaluator `EvalCmd`, and an `IsAtAssert` predicate.  Language extensions
(such as Core, whose commands are `CmdExt Expression`) supply their own
`IsAtAssert` predicate together with a few simple hypotheses relating it
to the loop / seq / block structure of configurations. -/

omit [HasFvar P] in
/-- Helper: when all asserts at a loop config pass (via `hv`), the
    loop-step's `hasInvFailure` boolean is forced to `false`. -/
theorem loop_step_hasInvFailure_false
    {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
    (IsAtAssert : Config P CmdT → AssertId P → Prop)
    (h_IsAtAssert_loop : ∀ {g m inv body md ρ lbl e},
      (lbl, e) ∈ inv →
      IsAtAssert (.stmt (.loop g m inv body md) ρ) ⟨lbl, e⟩)
    {c : Config P CmdT} {ρ : Env P}
    {inv : List (String × P.Expr)} {guard : ExprOrNondet P}
    {m : Option P.Expr} {body : List (Stmt P CmdT)} {md : MetaData P}
    {hasInvFailure : Bool}
    (hc_shape : c = .stmt (.loop guard m inv body md) ρ)
    (hv : ∀ a cfg, StepStmtStar P EvalCmd extendEval c cfg →
      IsAtAssert cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hff_iff : hasInvFailure = true ↔ ∃ le, le ∈ inv ∧
      ρ.eval ρ.store le.snd = some HasBool.ff) :
    hasInvFailure = false := by
  cases hb : hasInvFailure with
  | false => rfl
  | true =>
    exfalso
    rw [hb] at hff_iff
    have ⟨⟨lbl, e⟩, hmem, he_ff⟩ := hff_iff.mp rfl
    have hat : IsAtAssert c ⟨lbl, e⟩ := hc_shape ▸ h_IsAtAssert_loop hmem
    have htt := hv ⟨lbl, e⟩ c (.refl _) hat
    rw [hc_shape] at htt
    simp only [Config.getEval, Config.getStore, Config.getEnv] at htt
    rw [he_ff] at htt
    exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm

omit [HasFvar P] in
/-- Single-step: if hasFailure is false and all reachable asserts pass,
    then hasFailure stays false after one step.

    Parameterized over an abstract `IsAtAssert` predicate so the lemma
    applies to both the base Imperative dialect and language extensions
    (e.g., Core). -/
theorem step_preserves_noFailure
    {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
    (IsAtAssert : Config P CmdT → AssertId P → Prop)
    (h_failure_implies_assert_ff :
      ∀ {ρ : Env P} {c : CmdT} {σ'},
        EvalCmd ρ.eval ρ.store c σ' true →
        ∃ a : AssertId P, IsAtAssert (.stmt (.cmd c) ρ) a ∧
          ρ.eval ρ.store a.expr = some HasBool.ff)
    (h_IsAtAssert_loop : ∀ {g m inv body md ρ lbl e},
      (lbl, e) ∈ inv →
      IsAtAssert (.stmt (.loop g m inv body md) ρ) ⟨lbl, e⟩)
    (h_IsAtAssert_seq : ∀ {inner ss a},
      IsAtAssert inner a → IsAtAssert (.seq inner ss) a)
    (h_IsAtAssert_block : ∀ {label inner a},
      IsAtAssert inner a → IsAtAssert (.block label inner) a)
    (c₁ c₂ : Config P CmdT)
    (hv : ∀ a cfg, StepStmtStar P EvalCmd extendEval c₁ cfg →
      IsAtAssert cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hnf : c₁.getEnv.hasFailure = false)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂) :
    c₂.getEnv.hasFailure = false := by
  induction hstep with
  | step_cmd hcmd =>
    simp only [Config.getEnv] at hnf ⊢
    -- The per-command failure flag can be either true or false.
    match h : ‹Bool› with
    | false => simp [hnf, h]
    | true =>
      exfalso
      have ⟨a, hat, hff⟩ := h_failure_implies_assert_ff (h ▸ hcmd)
      have htt := hv a _ (.refl _) hat
      simp only [Config.getEval, Config.getStore, Config.getEnv] at htt
      rw [hff] at htt
      exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm
  | step_block | step_funcDecl => simp [Config.getEnv]; exact hnf
  | step_loop_enter _ _ hff_iff _ | step_loop_exit _ _ hff_iff _
  | step_loop_nondet_enter _ hff_iff | step_loop_nondet_exit _ hff_iff =>
    simp only [Config.getEnv]
    have hinv := loop_step_hasInvFailure_false (P := P) (extendEval := extendEval)
      IsAtAssert h_IsAtAssert_loop rfl hv hff_iff
    simp [Config.getEnv] at hnf
    rw [hnf, Bool.false_or]; exact hinv
  | step_seq_inner h ih =>
    exact ih
      (fun a cfg hr hat =>
        hv a (.seq cfg _) (seq_inner_star P EvalCmd extendEval _ _ _ hr) (h_IsAtAssert_seq hat)) hnf
  | step_block_body h ih =>
    exact ih
      (fun a cfg hr hat =>
        hv a (.block _ cfg) (block_inner_star P EvalCmd extendEval _ _ _ hr) (h_IsAtAssert_block hat)) hnf
  | _ => intros; exact hnf

theorem allAssertsValid_preserves_noFailure
    {ρ₀ ρ' : Env P}
    (st : Stmt P (Cmd P))
    (hvalid : ∀ (a : AssertId P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) cfg →
      isAtAssert P cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hf₀ : ρ₀.hasFailure = false)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    ρ'.hasFailure = false := by
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
    refine ih
      (fun a cfg h hat => hv a _ (.step _ _ _ hstep h) hat)
      (step_preserves_noFailure (P := P) (extendEval := extendEval)
        (isAtAssert P)
        (fun hcmd => by
          cases hcmd with
          | eval_assert_fail hff _ => exact ⟨⟨_, _⟩, ⟨rfl, rfl⟩, hff⟩)
        (fun hmem => hmem)
        (fun h => h)
        (fun h => h)
        _ _ hv hnf hstep)

end -- section

end -- public section
end Imperative

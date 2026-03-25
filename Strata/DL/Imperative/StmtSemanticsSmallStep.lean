/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Imperative

public section

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
      The string is the block label. -/
  | block : String → Config P CmdT → Config P CmdT
  /-- A sequence context: execute the first statement (as a sub-config), then
      continue with the remaining statements. -/
  | seq : Config P CmdT → List (Stmt P CmdT) → Config P CmdT

/-! ## Configuration accessors -/

variable {P : PureExpr} {CmdT : Type}

/-- Extract the store from a configuration. -/
@[expose] def Config.getStore : Config P CmdT → SemanticStore P
  | .stmt _ ρ => ρ.store
  | .stmts _ ρ => ρ.store
  | .terminal ρ => ρ.store
  | .exiting _ ρ => ρ.store
  | .block _ inner => inner.getStore
  | .seq inner _ => inner.getStore

/-- Extract the evaluator from a configuration. -/
@[expose] def Config.getEval : Config P CmdT → SemanticEval P
  | .stmt _ ρ => ρ.eval
  | .stmts _ ρ => ρ.eval
  | .terminal ρ => ρ.eval
  | .exiting _ ρ => ρ.eval
  | .block _ inner => inner.getEval
  | .seq inner _ => inner.getEval

/-- Extract the execution environment from a configuration. -/
@[expose] def Config.getEnv : Config P CmdT → Env P
  | .stmt _ ρ => ρ
  | .stmts _ ρ => ρ
  | .terminal ρ => ρ
  | .exiting _ ρ => ρ
  | .block _ inner => inner.getEnv
  | .seq inner _ => inner.getEnv

/-! ## noMatchingAssert

`noMatchingAssert` checks that a statement, list of statements, or
configuration does not syntactically contain an `assert` command with
a given label.  This is specific to `Cmd P`. -/

/-- `noMatchingAssert` for statements and statement lists.
    Returns `True` when `s` does not syntactically contain any `assert`
    command with the given label. -/
@[expose] def Stmt.noMatchingAssert : Stmt P (Cmd P) → String → Prop
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

/-! ## Well-paired exits

`exitsCoveredByBlocks labels s` holds when every `exit` statement in `s` is caught
by an enclosing `block` — either within `s` itself or with a label in
`labels` (representing blocks that enclose `s` externally).

When `s.exitsCoveredByBlocks []`, execution of `s` can never produce `.exiting`. -/

@[expose] def Stmt.exitsCoveredByBlocks : List String → Stmt P CmdT → Prop
  | _, .cmd _ => True
  | labels, .block l ss _ => Block.exitsCoveredByBlocks (l :: labels) ss
  | labels, .ite _ tss ess _ => Block.exitsCoveredByBlocks labels tss ∧ Block.exitsCoveredByBlocks labels ess
  | labels, .loop _ _ _ body _ => Block.exitsCoveredByBlocks labels body
  | labels, .exit none _ => labels.length > 0
  | labels, .exit (some l) _ => l ∈ labels
  | _, .funcDecl _ _ => True
  | _, .typeDecl _ _ => True
where
  Block.exitsCoveredByBlocks : List String → List (Stmt P CmdT) → Prop
    | _, [] => True
    | labels, s :: ss => Stmt.exitsCoveredByBlocks labels s ∧ Block.exitsCoveredByBlocks labels ss

/-- Extend `exitsCoveredByBlocks` to configurations. -/
@[expose] def Config.exitsCoveredByBlocks : List String → Config P CmdT → Prop
  | labels, .stmt s _ => s.exitsCoveredByBlocks labels
  | labels, .stmts ss _ => Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss
  | _, .terminal _ => True
  | labels, .exiting none _ => labels.length > 0
  | labels, .exiting (some l) _ => l ∈ labels
  | labels, .block l inner => Config.exitsCoveredByBlocks (l :: labels) inner
  | labels, .seq inner ss =>
    Config.exitsCoveredByBlocks labels inner ∧ Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss

/-! ## Single-step relation

`StepStmt` defines a single execution step from one configuration to another.
The expression evaluator is part of the `Env` and can be extended by
`funcDecl` statements.  The cumulative failure flag in `Env.hasFailure` is
OR-ed with the per-command failure flag at each `step_cmd`.
-/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P]

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

  /-- A labeled block steps to a block context that wraps its body as `.stmts`. -/
  | step_block :
    StepStmt EvalCmd extendEval
      (.stmt (.block label ss _) ρ)
      (.block label (.stmts ss ρ))

  /-- If the condition of an `ite` statement evaluates to true, step to the
      then branch. -/
  | step_ite_true :
    ρ.eval ρ.store c = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite c tss ess _) ρ)
      (.stmts tss ρ)

  /-- If the condition of an `ite` statement evaluates to false, step to the
      else branch. -/
  | step_ite_false :
    ρ.eval ρ.store c = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite c tss ess _) ρ)
      (.stmts ess ρ)

  /-- If a loop guard is true, execute the body (followed by the loop again). -/
  | step_loop_enter :
    ρ.eval ρ.store g = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop g m inv body md) ρ)
      (.stmts (body ++ [.loop g m inv body md]) ρ)

  /-- If a loop guard is false, terminate the loop. -/
  | step_loop_exit :
    ρ.eval ρ.store g = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop g m inv body _) ρ)
      (.terminal ρ)

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

  /-- When a block's inner body exits with no label, the block consumes the exit. -/
  | step_block_exit_none :
    StepStmt EvalCmd extendEval
      (.block label (.exiting .none ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with a matching label, the block consumes it. -/
  | step_block_exit_match :
    l = label →
    ----
    StepStmt EvalCmd extendEval
      (.block label (.exiting (.some l) ρ'))
      (.terminal ρ')

  /-- When a block's inner body exits with a non-matching label, the exit propagates. -/
  | step_block_exit_mismatch :
    l ≠ label →
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

abbrev StepStmtStar :
    Config P CmdT → Config P CmdT → Prop :=
  ReflTrans (StepStmt P EvalCmd extendEval)

/-- A statement evaluates successfully if it steps to a terminal configuration. -/
def EvalStmtSmall
    (ρ : Env P) (s : Stmt P CmdT)
    (ρ' : Env P) : Prop :=
  StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')

/-- A list of statements evaluates successfully if it steps to a terminal
    configuration. -/
def EvalStmtsSmall
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

/-- Transitivity of `ReflTrans`: if `r* x y` and `r* y z` then `r* x z`.
    This is a local helper that avoids the opaque `Transitive` wrapper
    from `Relations.lean` (which becomes opaque across module boundaries). -/
theorem reflTrans_trans {r : Relation A}
    {x y z : A} (h1 : ReflTrans r x y) (h2 : ReflTrans r y z) :
    ReflTrans r x z := by
  induction h1 with
  | refl => exact h2
  | step _ mid _ hstep _ ih => exact .step _ mid _ hstep (ih h2)

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
    (label : String)
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
    reflTrans_trans h2 h3
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
    {inner : Config P CmdT} {l : String} {ρ' : Env P}
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
    {inner : Config P CmdT} {l : String} {lbl : Option String} {ρ' : Env P}
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

private theorem block_exitsCoveredByBlocks_append
    (labels : List String) (ss₁ ss₂ : List (Stmt P CmdT))
    (h₁ : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss₁)
    (h₂ : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss₂) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels (ss₁ ++ ss₂) := by
  induction ss₁ with
  | nil => exact h₂
  | cons s ss ih => exact ⟨h₁.1, ih h₁.2⟩

/-- A single step preserves `Config.exitsCoveredByBlocks`. -/
private theorem step_preserves_exitsCoveredByBlocks
    (labels : List String)
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
  | step_loop_enter _ _ =>
    intro labels hwp
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact block_exitsCoveredByBlocks_append (P := P) (CmdT := CmdT) labels _ _ hwp ⟨hwp, True.intro⟩
  | step_loop_exit => intro _ _; trivial
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
      c₁.exitsCoveredByBlocks ([] : List String) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List String) by
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

end -- section

end -- public section
end Imperative

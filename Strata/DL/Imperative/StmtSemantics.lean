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

/-- `NoGenStore Q ρ` says the environment `ρ` leaves every `Q`-kind slot
undefined: for each string `s` satisfying the label-kind predicate `Q` (the
kind of label a pass mints), `ρ`'s store maps `HasIdent.ident s` to `none`.

This is the store-level analogue of the syntactic `NoGenSuffix` freshness
condition: it captures the "minted names start undefined" precondition shared
by the pipeline passes, parameterised by the kind each pass mints so a single
initial store can satisfy several passes' obligations at disjoint kinds. -/
@[expose] abbrev NoGenStore {P : PureExpr} [HasIdent P]
    (Q : String → Prop) (ρ : Env P) : Prop :=
  ∀ s : String, Q s → ρ.store (HasIdent.ident (P := P) s) = none

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
      The label identifies which block to exit to. -/
  | exiting : String → Env P → Config P CmdT
  /-- A block context: execute the inner config, then consume matching exits.
      The label is `Option String` — `none` denotes an unnamed block that only
      catches unlabeled exits.  The `SemanticStore P` is the parent store at
      block entry; on exit, the result is projected through it so that
      variables initialized inside the block are not visible outside. -/
  | block : Option String → SemanticStore P → Config P CmdT → Config P CmdT
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
  | .block _ _ inner => inner.getEnv
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
  | .block _ _ inner, label => inner.noMatchingAssert label
  | .seq inner ss, label =>
    inner.noMatchingAssert label ∧ Stmt.noMatchingAssert.Stmts.noMatchingAssert ss label

/-- Config-level noFuncDecl predicate. -/
def Config.noFuncDecl : Config P CmdT → Prop
  | .stmt s _ => Stmt.noFuncDecl s = true
  | .stmts ss _ => Block.noFuncDecl ss = true
  | .terminal _ => True
  | .exiting _ _ => True
  | .block _ _ inner => Config.noFuncDecl inner
  | .seq inner ss => Config.noFuncDecl inner ∧ Block.noFuncDecl ss = true

/-- Extend `exitsCoveredByBlocks` to configurations.

    The label list has type `List String` (matching `Stmt.exit`'s mandatory-label
    AST).  An anonymous (`.none`) `Config.block` (introduced by the loop/if's body
    wrapper) does NOT contribute a label — labeled exits cannot match `.none`,
    and unlabeled exits do not exist as user statements. -/
@[expose] def Config.exitsCoveredByBlocks : List String → Config P CmdT → Prop
  | labels, .stmt s _ => s.exitsCoveredByBlocks labels
  | labels, .stmts ss _ => Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss
  | _, .terminal _ => True
  | labels, .exiting l _ => l ∈ labels
  | labels, .block none _ inner => Config.exitsCoveredByBlocks labels inner
  | labels, .block (some l) _ inner => Config.exitsCoveredByBlocks (l :: labels) inner
  | labels, .seq inner ss =>
    Config.exitsCoveredByBlocks labels inner ∧ Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss

/-- Project an inner store through a parent store: keep the inner value only
    for variables that were already defined in the parent. Variables that were
    not defined in the parent (i.e., init'd inside the block) become `none`. -/
@[expose] def projectStore (σ_parent σ_inner : SemanticStore P) : SemanticStore P :=
  fun x => if (σ_parent x).isSome then σ_inner x else none

/-- The projected inner store agrees with the unprojected inner store on
`σ_parent`'s domain. Variables present in the parent are unchanged by
projection; variables absent from the parent become `none` in the projection,
but those don't satisfy `isDefined (projectStore _ _) [x]`, so
`StoreAgreement` doesn't constrain them. -/
theorem StoreAgreement.of_projectStore {P : PureExpr}
    (σ_parent σ_inner : SemanticStore P) :
    StoreAgreement (projectStore σ_parent σ_inner) σ_inner := by
  intro x h_def
  -- h_def : isDefined (projectStore σ_parent σ_inner) [x]
  -- Goal: projectStore σ_parent σ_inner x = σ_inner x
  have h := h_def x (List.mem_singleton.mpr rfl)
  unfold projectStore at h ⊢
  -- h : (if (σ_parent x).isSome then σ_inner x else none).isSome = true
  -- Goal : (if (σ_parent x).isSome then σ_inner x else none) = σ_inner x
  by_cases hp : (σ_parent x).isSome
  · simp [hp]
  · simp [hp] at h

/-- Bundle `StoreAgreement.of_projectStore` with `.trans` and a `ρ_blk` rewrite,
the four-line idiom that recurs after every `.block`-step in the simulation
proofs. Given a record-update equality showing the outer env's store is the
projection of the inner env's store, and an agreement between the inner store
and a CFG store, derive agreement between the outer store and the CFG store. -/
theorem StoreAgreement.through_projectStore {P : PureExpr}
    {σ_parent : SemanticStore P}
    {ρ_inner ρ_blk : Env P}
    {σ_cfg : SemanticStore P}
    (h_ρ_blk_eq : ρ_blk = { ρ_inner with store := projectStore σ_parent ρ_inner.store })
    (h_agree_body : StoreAgreement ρ_inner.store σ_cfg) :
    StoreAgreement ρ_blk.store σ_cfg := by
  rw [h_ρ_blk_eq]
  exact StoreAgreement.trans (StoreAgreement.of_projectStore _ _) h_agree_body

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
      `Config.block` wrapper (whose label is `Option String`).
      The parent store `ρ.store` is saved so that block-local variables
      can be popped on exit. -/
  | step_block :
    StepStmt EvalCmd extendEval
      (.stmt (.block label ss _) ρ)
      (.block (.some label) ρ.store (.stmts ss ρ))

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

      The body alone is wrapped in an unnamed `.block`, sequenced with the
      recursive loop.  This means each iteration runs the body in its own
      block scope: variables `init`'d inside body are projected away at the
      end of each iteration, allowing the next iteration's body to re-`init`
      the same names. -/
  | step_loop_enter {hasInvFailure : Bool} :
    ρ.eval ρ.store g = .some HasBool.tt →
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop (.det g) m inv body md) ρ)
      (.seq
        (.block .none ρ.store (.stmts body
          { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))
        [.loop (.det g) m inv body md])

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
      body alone is wrapped in an unnamed `.block` and sequenced with the
      recursive loop, giving each iteration its own block scope. -/
  | step_loop_nondet_enter {hasInvFailure : Bool} :
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    StepStmt EvalCmd extendEval
      (.stmt (.loop .nondet m inv body md) ρ)
      (.seq
        (.block .none ρ.store (.stmts body
          { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))
        [.loop .nondet m inv body md])

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
      (.block label σ_parent inner)
      (.block label σ_parent inner')

  /-- When a block's inner body reaches terminal, the block terminates.
      The resulting store is projected through the parent store: only variables
      that existed before the block keep their (possibly updated) values;
      variables initialized inside the block are discarded. -/
  | step_block_done :
    StepStmt EvalCmd extendEval
      (.block label σ_parent (.terminal ρ'))
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

  /-- When a block's inner body exits with a matching label, the block consumes it.
      Store is projected. -/
  | step_block_exit_match :
    label = .some l →
    ----
    StepStmt EvalCmd extendEval
      (.block label σ_parent (.exiting l ρ'))
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

  /-- When a block's inner body exits with a non-matching label, the exit propagates.
      Includes the case where the block's own label is `.none` (anonymous loop/ite
      wrapper, which never matches a labeled exit) as well as any other mismatched
      `.some` label.  Store is projected since we're leaving this block. -/
  | step_block_exit_mismatch :
    label ≠ .some l →
    ----
    StepStmt EvalCmd extendEval
      (.block label σ_parent (.exiting l ρ'))
      (.exiting l { ρ' with store := projectStore σ_parent ρ'.store })

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

/-- Configuration is terminal if no further steps are possible. -/
def IsTerminal
    (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd extendEval c c'

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
  | .block _ _ inner, aid => isAtAssert inner aid
  | .seq inner _, aid => isAtAssert inner aid
  | _, _ => False

end -- section

end -- public section
end Imperative

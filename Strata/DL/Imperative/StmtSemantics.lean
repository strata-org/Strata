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

/-- A well-formed evaluator extension preserves all `WellFormedSemanticEval*`
    predicates through funcDecl steps.  This is the only step that modifies the
    evaluator (`step_funcDecl`); all other small-step rules leave it unchanged.

    `preserves_eval_on_disjoint` says: extending the evaluator with `decl`
    leaves evaluation of any expression whose free variables do NOT mention
    `decl.name` unchanged.  This lets simulation proofs reason about
    expressions whose free variables are syntactically disjoint from
    freshly-introduced function names (e.g., loop invariants whose `getVars`
    are confined to pre-body scope, while a `funcDecl` inside the body
    introduces a fresh name not in that scope).

    Concrete instantiations of `extendEval` (e.g., lookup-table extensions in
    Core) should prove this once at the instantiation site. -/
structure WFEvalExtension (P : PureExpr) [HasBool P] [HasNot P] [HasFvar P] [HasVal P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P) : Prop where
  preserves_wfBool : ∀ δ σ decl, WellFormedSemanticEvalBool δ →
    WellFormedSemanticEvalBool (extendEval δ σ decl)
  preserves_wfVal : ∀ δ σ decl, WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVal (extendEval δ σ decl)
  preserves_wfVar : ∀ δ σ decl, WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalVar (extendEval δ σ decl)
  preserves_eval_on_disjoint : ∀ δ σ decl σ' e,
    decl.name ∉ HasVarsPure.getVars (P := P) e →
    (extendEval δ σ decl) σ' e = δ σ' e

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
      variables initialized inside the block are not visible outside.
      The `SemanticEval P` is the parent evaluator at block entry; on exit,
      the result evaluator is restored to it so that any function declarations
      introduced inside the block are not visible outside. -/
  | block : Option String → SemanticStore P → SemanticEval P → Config P CmdT → Config P CmdT
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
  | .block _ _ _ inner => inner.getEnv
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
  | .block _ _ _ inner, label => inner.noMatchingAssert label
  | .seq inner ss, label =>
    inner.noMatchingAssert label ∧ Stmt.noMatchingAssert.Stmts.noMatchingAssert ss label

/-- Config-level noFuncDecl predicate.

    For `.block` we additionally require that the snapshotted parent eval
    `e_parent` matches the inner config's current eval.  Together with
    no-funcDecl-inside, this ensures that on `step_block_done` the eval
    restoration is a no-op (it puts back the same eval that was already
    there), so eval is preserved throughout. -/
def Config.noFuncDecl : Config P CmdT → Prop
  | .stmt s _ => Stmt.noFuncDecl s = true
  | .stmts ss _ => Block.noFuncDecl ss = true
  | .terminal _ => True
  | .exiting _ _ => True
  | .block _ _ e_parent inner => Config.noFuncDecl inner ∧ e_parent = inner.getEnv.eval
  | .seq inner ss => Config.noFuncDecl inner ∧ Block.noFuncDecl ss = true

/-- Config-level `funcDeclNames`: collects all `decl.name`s from `funcDecl`
    AST nodes syntactically present anywhere in the config. -/
@[expose] def Config.funcDeclNames : Config P CmdT → List P.Ident
  | .stmt s _ => Stmt.funcDeclNames s
  | .stmts ss _ => Block.funcDeclNames ss
  | .terminal _ => []
  | .exiting _ _ => []
  | .block _ _ _ inner => Config.funcDeclNames inner
  | .seq inner ss => Config.funcDeclNames inner ++ Block.funcDeclNames ss

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
  | labels, .block none _ _ inner => Config.exitsCoveredByBlocks labels inner
  | labels, .block (some l) _ _ inner => Config.exitsCoveredByBlocks (l :: labels) inner
  | labels, .seq inner ss =>
    Config.exitsCoveredByBlocks labels inner ∧ Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss

/-- Project an inner store through a parent store: keep the inner value only
    for variables that were already defined in the parent. Variables that were
    not defined in the parent (i.e., init'd inside the block) become `none`. -/
@[expose] def projectStore (σ_parent σ_inner : SemanticStore P) : SemanticStore P :=
  fun x => if (σ_parent x).isSome then σ_inner x else none

/-- If every var that's defined in `σ'` is also defined in `σ`, then projection
    through `σ` is the identity on `σ'`. -/
theorem projectStore_id {P : PureExpr} {σ σ' : SemanticStore P}
    (h : ∀ x, σ' x ≠ none → σ x ≠ none) :
    projectStore σ σ' = σ' := by
  funext x
  simp [projectStore]
  intro hx
  cases heq : σ' x
  · rfl
  · exact absurd hx (h x (by simp [heq]))

/-- Projecting a store through itself is the identity. -/
theorem projectStore_self {P : PureExpr} (σ : SemanticStore P) :
    projectStore σ σ = σ := projectStore_id (fun _ h => h)

/-- Projecting a store through itself, lifted to envs. -/
theorem projectStore_self_env {P : PureExpr} (ρ : Env P) :
    ({ ρ with store := projectStore ρ.store ρ.store } : Env P) = ρ := by
  have h : projectStore ρ.store ρ.store = ρ.store := projectStore_self ρ.store
  simp [h]

/-- `projectStore` preserves `isSome` for any variable that is `isSome`
    in both the parent and the inner store. -/
theorem projectStore_isSome {P : PureExpr} {σ_parent σ_inner : SemanticStore P}
    {n : P.Ident}
    (hp : (σ_parent n).isSome) (hi : (σ_inner n).isSome) :
    (projectStore σ_parent σ_inner n).isSome := by
  simp [projectStore, hp, hi]

/-! ## Single-step relation -/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P] [HasIntOrder P]

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
      The parent store `ρ.store` and parent eval `ρ.eval` are saved so that
      block-local variables and function declarations can be popped on exit. -/
  | step_block :
    StepStmt EvalCmd extendEval
      (.stmt (.block label ss _) ρ)
      (.block (.some label) ρ.store ρ.eval (.stmts ss ρ))

  /-- If the condition of an `ite` statement evaluates to true, step to the
      then branch.  The branch is wrapped in a block so that variables
      `init`'d inside are projected away on exit (matching `definedVars`
      with `excludeScoped = true`). -/
  | step_ite_true :
    ρ.eval ρ.store c = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite (.det c) tss ess _) ρ)
      (.block .none ρ.store ρ.eval (.stmts tss ρ))

  /-- If the condition of an `ite` statement evaluates to false, step to the
      else branch (scoped via block wrapper). -/
  | step_ite_false :
    ρ.eval ρ.store c = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.ite (.det c) tss ess _) ρ)
      (.block .none ρ.store ρ.eval (.stmts ess ρ))

  /-- Non-deterministic ite: step to the then branch (scoped). -/
  | step_ite_nondet_true :
    StepStmt EvalCmd extendEval
      (.stmt (.ite .nondet tss ess _) ρ)
      (.block .none ρ.store ρ.eval (.stmts tss ρ))

  /-- Non-deterministic ite: step to the else branch (scoped). -/
  | step_ite_nondet_false :
    StepStmt EvalCmd extendEval
      (.stmt (.ite .nondet tss ess _) ρ)
      (.block .none ρ.store ρ.eval (.stmts ess ρ))

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
    (∀ me v, m = .some me →
      ρ.eval ρ.store me = .some v ∧
      ρ.eval ρ.store (HasIntOrder.lt v HasIntOrder.zero) = .some HasBool.ff) →
    ----
    StepStmt EvalCmd extendEval
      (.stmt (.loop (.det g) m inv body md) ρ)
      (.seq
        (.block .none ρ.store ρ.eval (.stmts body
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
        (.block .none ρ.store ρ.eval (.stmts body
          { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))
        [.loop .nondet m inv body md])

  /-- Non-deterministic loop: exit the loop.  Measure must be `.none`. -/
  | step_loop_nondet_exit {hasInvFailure : Bool} :
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    StepStmt EvalCmd extendEval
      (.stmt (.loop .nondet .none inv body _) ρ)
      (.terminal { ρ with hasFailure := ρ.hasFailure || hasInvFailure })

  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
    StepStmt EvalCmd extendEval
      (.stmt (.exit label _) ρ)
      (.exiting label ρ)

  /-- A function declaration extends the evaluator with the new function. -/
  | step_funcDecl [HasSubstFvar P] :
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
      (.block label σ_parent e_parent inner)
      (.block label σ_parent e_parent inner')

  /-- When a block's inner body reaches terminal, the block terminates.
      The resulting store is projected through the parent store: only variables
      that existed before the block keep their (possibly updated) values;
      variables initialized inside the block are discarded.  The evaluator is
      restored to the parent's: function declarations introduced inside the
      block are not visible outside. -/
  | step_block_done :
    StepStmt EvalCmd extendEval
      (.block label σ_parent e_parent (.terminal ρ'))
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store, eval := e_parent })

  /-- When a block's inner body exits with a matching label, the block consumes it.
      Store and eval are projected/restored. -/
  | step_block_exit_match :
    label = .some l →
    ----
    StepStmt EvalCmd extendEval
      (.block label σ_parent e_parent (.exiting l ρ'))
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store, eval := e_parent })

  /-- When a block's inner body exits with a non-matching label, the exit propagates.
      Includes the case where the block's own label is `.none` (anonymous loop/ite
      wrapper, which never matches a labeled exit) as well as any other mismatched
      `.some` label.  Store and eval are projected/restored since we're leaving
      this block. -/
  | step_block_exit_mismatch :
    label ≠ .some l →
    ----
    StepStmt EvalCmd extendEval
      (.block label σ_parent e_parent (.exiting l ρ'))
      (.exiting l { ρ' with store := projectStore σ_parent ρ'.store, eval := e_parent })

end

/-! ## Multi-step execution: reflexive transitive closure of single steps. -/

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [HasBool P] [HasNot P] [HasIntOrder P]
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
    (σ_parent : SemanticStore P)
    (e_parent : SemanticEval P)
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval
      (.block label σ_parent e_parent inner) (.block label σ_parent e_parent inner') := by
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
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {lbl : String} {ρ' : Env P}
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
    terminated or exited (caught by the block).  In both cases the inner
    reaches a config whose env projects to `ρ'` via the parent store. -/
theorem block_reaches_terminal
    {inner : Config P CmdT} {l : Option String}
    {σ_parent : SemanticStore P} {e_parent : SemanticEval P} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l σ_parent e_parent inner) (.terminal ρ')) :
    (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.terminal ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent }) ∨
    (∃ lbl ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent }) := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ρ', src = .block l σ_parent e_parent inner → tgt = .terminal ρ' →
      (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.terminal ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent }) ∨
      (∃ lbl ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent }) from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl ⟨ρ_inner, hterm, heq⟩ => exact .inl ⟨ρ_inner, .step _ _ _ h hterm, heq⟩
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ => exact .inr ⟨lbl, ρ_inner, .step _ _ _ h hexit, heq⟩
    | step_block_done =>
      subst htgt; cases hrest with
      | refl => exact .inl ⟨_, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with
      | refl => exact .inr ⟨_, _, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Invert a block execution reaching exiting: the inner must have
    exited with a label that didn't match the block.  The env is projected. -/
theorem block_reaches_exiting
    {inner : Config P CmdT} {l : Option String}
    {σ_parent : SemanticStore P} {e_parent : SemanticEval P} {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l σ_parent e_parent inner) (.exiting lbl ρ')) :
    ∃ lbl_inner ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl_inner ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner lbl ρ', src = .block l σ_parent e_parent inner → tgt = .exiting lbl ρ' →
      ∃ lbl_inner ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl_inner ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨lbl_inner, ρ_inner, hexit, heq⟩ := ih _ _ _ rfl htgt
      exact ⟨lbl_inner, ρ_inner, .step _ _ _ h hexit, heq⟩
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with
      | refl => exact ⟨_, _, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_done | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-! ## Trace construction helpers -/

/-- Entering a block: a single step from `.stmt (.block l body md) ρ`
    to `.block (.some l) (.stmts body ρ)`. -/
theorem step_block_enter (l : String) (body : List (Stmt P CmdT))
    (md : MetaData P) (ρ : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.stmt (.block l body md) ρ) (.block (.some l) ρ.store ρ.eval (.stmts body ρ)) :=
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
  | exact .step_loop_enter ‹_› ‹_› ‹_› ‹_› ‹_›
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
  | .block l₁ σ₁ e₁ i₁, .block l₂ σ₂ e₂ i₂ => l₁ = l₂ ∧ σ₁ = σ₂ ∧ e₁ = e₂ ∧ ConfigSE i₁ i₂
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
  | step_loop_enter _ _ _ _ _ | step_loop_exit _ _ _ _
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
    | block _ _ _ i₂ =>
      have hrs := heq.1; subst hrs
      have hσ := heq.2.1; subst hσ
      have he := heq.2.2.1; subst he
      have ⟨c₂', h₂, heq₂⟩ := step_simulation _ _ _ h heq.2.2.2
      exact ⟨_, .step_block_body h₂, ⟨rfl, rfl, rfl, heq₂⟩⟩
    | _ => exact nomatch heq
  | step_block_done =>
    cases c₂ with
    | block _ _ _ i₂ =>
      have hrs := heq.1; subst hrs
      have hσ := heq.2.1; subst hσ
      have he := heq.2.2.1; subst he
      cases i₂ with
      | terminal ρ₂ =>
        have hse := heq.2.2.2
        exact ⟨_, .step_block_done, ⟨congrArg (projectStore _) hse.1, rfl⟩⟩
      | _ => exact nomatch heq.2.2.2
    | _ => exact nomatch heq
  | step_block_exit_match hl =>
    cases c₂ with
    | block _ _ _ i₂ =>
      have hlb := heq.1; subst hlb
      have hσ := heq.2.1; subst hσ
      have he := heq.2.2.1; subst he
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl₂ := heq.2.2.2.1; subst hl₂
        have hse := heq.2.2.2.2
        exact ⟨_, .step_block_exit_match hl, ⟨congrArg (projectStore _) hse.1, rfl⟩⟩
      | _ => exact nomatch heq.2.2.2
    | _ => exact nomatch heq
  | step_block_exit_mismatch hl =>
    cases c₂ with
    | block _ _ _ i₂ =>
      have hlb := heq.1; subst hlb
      have hσ := heq.2.1; subst hσ
      have he := heq.2.2.1; subst he
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl₂ := heq.2.2.2.1; subst hl₂
        have hse := heq.2.2.2.2
        exact ⟨_, .step_block_exit_mismatch hl, ⟨rfl, congrArg (projectStore _) hse.1, rfl⟩⟩
      | _ => exact nomatch heq.2.2.2
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

/-- Helper: when the inner of a block reaches `.exiting l` and the
    block's label (if some) doesn't match `l`, then `l` must be in the outer
    labels list.  The conclusion is `l ∈ labels`, which is exactly the
    `Config.exitsCoveredByBlocks` of `.exiting l ρ''` for any ρ''. -/
private theorem block_exit_mismatch_unfold {labels : List String}
    {label : Option String} {σ_parent : SemanticStore P} {e_parent : SemanticEval P}
    {l : String} {ρ' ρ'' : Env P}
    (h : Config.exitsCoveredByBlocks labels
          (.block label σ_parent e_parent (.exiting l ρ' : Config P CmdT)))
    (hne : label ≠ .some l) :
    Config.exitsCoveredByBlocks labels (.exiting l ρ'' : Config P CmdT) := by
  show l ∈ labels
  cases label with
  | none => exact h
  | some lb =>
    have h' : l ∈ lb :: labels := h
    rw [List.mem_cons] at h'
    rcases h' with hh | hh
    · exact absurd (by rw [hh]) hne
    · exact hh

/-- A single step preserves `Config.exitsCoveredByBlocks`. -/
theorem step_preserves_exitsCoveredByBlocks
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
  | step_ite_nondet_true => intro _ hwp; exact hwp.1
  | step_ite_nondet_false => intro _ hwp; exact hwp.2
  | step_loop_enter _ _ =>
    intro labels hwp
    -- Goal: .seq (.block .none ρ.store (.stmts body ρ')) [.loop ...] covers labels.
    -- The .block .none label doesn't extend the labels list (Config.exitsCoveredByBlocks's
    -- .block none case just descends).
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_exit => intro _ _; trivial
  | step_loop_nondet_enter =>
    intro labels hwp
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_nondet_exit => intro _ _; trivial
  | step_exit =>
    intro labels hwp
    -- hwp : l ∈ labels (from .stmt (.exit l)), goal: .exiting (.some l) covers labels = l ∈ labels
    exact hwp
  | step_funcDecl => intro _ _; trivial
  | step_typeDecl => intro _ _; trivial
  | step_stmts_nil => intro _ _; trivial
  | step_stmts_cons => intro _ hwp; exact ⟨hwp.1, hwp.2⟩
  | step_seq_inner _ ih => intro labels hwp; exact ⟨ih labels hwp.1, hwp.2⟩
  | step_seq_done => intro _ hwp; exact hwp.2
  | step_seq_exit => intro _ hwp; exact hwp.1
  | step_block_body _ ih =>
    intro labels hwp
    rename_i inner inner' label σ_parent e_parent _
    cases label with
    | none => exact ih labels hwp
    | some l => exact ih (l :: labels) hwp
  | step_block_done => intro _ _; trivial
  | step_block_exit_match => intro _ _; trivial
  | step_block_exit_mismatch hne =>
    intro labels hwp
    exact block_exit_mismatch_unfold (P := P) (CmdT := CmdT) hwp hne

/-- Well-paired statements cannot escape via `.exiting`:
    if all exits in `s` are caught by enclosing blocks
    (`s.exitsCoveredByBlocks []`), then `s` never reaches `.exiting`. -/
theorem exitsCoveredByBlocks_noEscape
    (s : Stmt P CmdT)
    (hwp : s.exitsCoveredByBlocks []) :
    ∀ (ρ : Env P) (lbl : String) (ρ' : Env P),
      ¬ StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.exiting lbl ρ') := by
  intro ρ lbl ρ' hstar
  -- Prove Config.exitsCoveredByBlocks [] is preserved, then show .exiting contradicts it.
  suffices ∀ c₁ c₂,
      c₁.exitsCoveredByBlocks ([] : List String) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List String) by
    have hwp' := this _ _ (show Config.exitsCoveredByBlocks [] (.stmt s ρ) from hwp) hstar
    -- Config.exitsCoveredByBlocks [] (.exiting lbl ρ') requires lbl ∈ [] (False).
    exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
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
    ∀ (ρ : Env P) (lbl : String) (ρ' : Env P),
      ¬ StepStmtStar P EvalCmd extendEval (.stmts bss ρ) (.exiting lbl ρ') := by
  intro ρ lbl ρ' hstar
  suffices ∀ c₁ c₂,
      c₁.exitsCoveredByBlocks ([] : List String) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List String) by
    have hwp' := this _ _ (show Config.exitsCoveredByBlocks [] (.stmts bss ρ) from hwp) hstar
    exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ c₂ hwp_c hstar_c
  induction hstar_c with
  | refl => exact hwp_c
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_exitsCoveredByBlocks P EvalCmd extendEval [] _ _ hstep hwp_c)

/-- If `.block l inner →* cfg`, the inner config never reaches `.exiting`,
    and `cfg` is neither terminal nor exiting, then `cfg = .block l inner'`
    for some `inner'` with `inner →* inner'`. -/
theorem block_star_extract_inner
    {l : Option String} {σ_parent : SemanticStore P} {e_parent : SemanticEval P}
    {inner cfg : Config P CmdT}
    (h_star : StepStmtStar P EvalCmd extendEval (.block l σ_parent e_parent inner) cfg)
    (h_no_exit : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval
        inner (.exiting lbl ρ'))
    (h_not_terminal : ∀ ρ', cfg ≠ .terminal ρ')
    (h_not_exiting : ∀ lbl ρ', cfg ≠ .exiting lbl ρ') :
    ∃ inner', cfg = .block l σ_parent e_parent inner' ∧
      StepStmtStar P EvalCmd extendEval inner inner' := by
  suffices ∀ c₁ c₂,
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      ∀ inner₀, c₁ = .block l σ_parent e_parent inner₀ →
      (∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval inner₀ (.exiting lbl ρ')) →
      (∀ ρ', c₂ ≠ .terminal ρ') → (∀ lbl ρ', c₂ ≠ .exiting lbl ρ') →
      ∃ inner', c₂ = .block l σ_parent e_parent inner' ∧
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
    exact ⟨rfl, hnofd, rfl⟩
  | step_ite_true =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.1, rfl⟩
  | step_ite_false =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.2, rfl⟩
  | step_ite_nondet_true =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.1, rfl⟩
  | step_ite_nondet_false =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.2, rfl⟩
  | step_loop_enter =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd
    refine ⟨rfl, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · -- Goal: Block.noFuncDecl body = true
      exact hnofd
    · -- Goal: ρ.eval = (.stmts body ρ').getEnv.eval where ρ' is hasFailure-modified ρ
      rfl
    · -- Goal: rest = [loop ...] has Block.noFuncDecl
      simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd]
  | step_loop_exit => intro _; exact ⟨rfl, trivial⟩
  | step_loop_nondet_enter =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd
    refine ⟨rfl, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact hnofd
    · rfl
    · simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd]
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
  | step_block_body _ ih =>
    intro hnofd
    -- hnofd : inner.noFuncDecl ∧ e_parent = inner.getEnv.eval
    have ⟨heq_inner, hnofd_inner⟩ := ih hnofd.1
    -- heq_inner : inner'.getEnv.eval = inner.getEnv.eval
    refine ⟨heq_inner, hnofd_inner, ?_⟩
    -- Goal: e_parent = inner'.getEnv.eval
    rw [heq_inner]; exact hnofd.2
  | step_block_done =>
    intro hnofd
    refine ⟨?_, trivial⟩
    simp only [Config.getEnv]
    exact hnofd.2
  | step_block_exit_match =>
    intro hnofd
    refine ⟨?_, trivial⟩
    simp only [Config.getEnv]
    exact hnofd.2
  | step_block_exit_mismatch =>
    intro hnofd
    refine ⟨?_, trivial⟩
    simp only [Config.getEnv]
    exact hnofd.2

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

/-- `.exiting` variant: When a block has no function declarations, an exiting
    execution preserves the evaluator. -/
theorem block_noFuncDecl_preserves_eval_exiting
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    (hnofd : Block.noFuncDecl ss = true)
    (hexit : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.exiting lbl ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmts ss ρ) from hnofd) hexit
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-! ## WF preservation under WFEvalExtension (no `noFuncDecl` requirement) -/

variable [HasFvar P] [HasVal P] [HasVarsPure P P.Expr]

/-- Config-level `WellFormedSemanticEvalBool` invariant.  Requires WF on
    the current eval AND on every captured `e_parent` snapshot stored
    inside enclosing blocks (recursively).  This is necessary because
    `step_block_done` restores eval to `e_parent`, so we need to know
    `e_parent` itself was WF. -/
def Config.wfBool : Config P CmdT → Prop
  | .stmt _ ρ => WellFormedSemanticEvalBool ρ.eval
  | .stmts _ ρ => WellFormedSemanticEvalBool ρ.eval
  | .terminal ρ => WellFormedSemanticEvalBool ρ.eval
  | .exiting _ ρ => WellFormedSemanticEvalBool ρ.eval
  | .block _ _ e_parent inner =>
    WellFormedSemanticEvalBool e_parent ∧ Config.wfBool inner
  | .seq inner _ => Config.wfBool inner

def Config.wfVal : Config P CmdT → Prop
  | .stmt _ ρ => WellFormedSemanticEvalVal ρ.eval
  | .stmts _ ρ => WellFormedSemanticEvalVal ρ.eval
  | .terminal ρ => WellFormedSemanticEvalVal ρ.eval
  | .exiting _ ρ => WellFormedSemanticEvalVal ρ.eval
  | .block _ _ e_parent inner =>
    WellFormedSemanticEvalVal e_parent ∧ Config.wfVal inner
  | .seq inner _ => Config.wfVal inner

def Config.wfVar : Config P CmdT → Prop
  | .stmt _ ρ => WellFormedSemanticEvalVar ρ.eval
  | .stmts _ ρ => WellFormedSemanticEvalVar ρ.eval
  | .terminal ρ => WellFormedSemanticEvalVar ρ.eval
  | .exiting _ ρ => WellFormedSemanticEvalVar ρ.eval
  | .block _ _ e_parent inner =>
    WellFormedSemanticEvalVar e_parent ∧ Config.wfVar inner
  | .seq inner _ => Config.wfVar inner

/-- Single step preserves `Config.wfBool` when the evaluator extension is
    well-formed (no `noFuncDecl` requirement). -/
private theorem step_preserves_wfBool_wfExtend
    (hwf_ext : WFEvalExtension P extendEval)
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hwfb : c₁.wfBool) :
    c₂.wfBool := by
  induction hstep with
  | step_cmd => exact hwfb
  | step_block =>
    -- c₁ = .stmt (.block ...), c₂ = .block (.some _) ρ.store ρ.eval (.stmts ss ρ)
    exact ⟨hwfb, hwfb⟩
  | step_ite_true | step_ite_false | step_ite_nondet_true | step_ite_nondet_false =>
    exact ⟨hwfb, hwfb⟩
  | step_loop_enter =>
    -- c₂ = .seq (.block .none ρ.store ρ.eval (.stmts body {ρ with hasFailure := ...})) [...]
    -- ρ.eval = wfBool, hasFailure-modified ρ has same eval, so still wfBool.
    exact ⟨hwfb, hwfb⟩
  | step_loop_exit => exact hwfb
  | step_loop_nondet_enter =>
    exact ⟨hwfb, hwfb⟩
  | step_loop_nondet_exit => exact hwfb
  | step_exit => exact hwfb
  | step_funcDecl =>
    -- c₂ = .terminal { ρ with eval := extendEval ρ.eval ρ.store decl }
    exact hwf_ext.preserves_wfBool _ _ _ hwfb
  | step_typeDecl => exact hwfb
  | step_stmts_nil => exact hwfb
  | step_stmts_cons => exact hwfb
  | step_seq_inner _ ih => exact ih hwfb
  | step_seq_done => exact hwfb
  | step_seq_exit => exact hwfb
  | step_block_body _ ih =>
    -- hwfb : ⟨wfBool e_parent, c₁_inner.wfBool⟩
    exact ⟨hwfb.1, ih hwfb.2⟩
  | step_block_done =>
    -- c₁ = .block label σ_parent e_parent (.terminal ρ'); c₂ = .terminal {... eval := e_parent}
    exact hwfb.1
  | step_block_exit_match => exact hwfb.1
  | step_block_exit_mismatch => exact hwfb.1

/-- Single step preserves `Config.wfVal`. -/
private theorem step_preserves_wfVal_wfExtend
    (hwf_ext : WFEvalExtension P extendEval)
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hwfv : c₁.wfVal) :
    c₂.wfVal := by
  induction hstep with
  | step_cmd => exact hwfv
  | step_block => exact ⟨hwfv, hwfv⟩
  | step_ite_true | step_ite_false | step_ite_nondet_true | step_ite_nondet_false =>
    exact ⟨hwfv, hwfv⟩
  | step_loop_enter => exact ⟨hwfv, hwfv⟩
  | step_loop_exit => exact hwfv
  | step_loop_nondet_enter => exact ⟨hwfv, hwfv⟩
  | step_loop_nondet_exit => exact hwfv
  | step_exit => exact hwfv
  | step_funcDecl => exact hwf_ext.preserves_wfVal _ _ _ hwfv
  | step_typeDecl => exact hwfv
  | step_stmts_nil => exact hwfv
  | step_stmts_cons => exact hwfv
  | step_seq_inner _ ih => exact ih hwfv
  | step_seq_done => exact hwfv
  | step_seq_exit => exact hwfv
  | step_block_body _ ih => exact ⟨hwfv.1, ih hwfv.2⟩
  | step_block_done => exact hwfv.1
  | step_block_exit_match => exact hwfv.1
  | step_block_exit_mismatch => exact hwfv.1

/-- Single step preserves `Config.wfVar`. -/
private theorem step_preserves_wfVar_wfExtend
    (hwf_ext : WFEvalExtension P extendEval)
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hwfvar : c₁.wfVar) :
    c₂.wfVar := by
  induction hstep with
  | step_cmd => exact hwfvar
  | step_block => exact ⟨hwfvar, hwfvar⟩
  | step_ite_true | step_ite_false | step_ite_nondet_true | step_ite_nondet_false =>
    exact ⟨hwfvar, hwfvar⟩
  | step_loop_enter => exact ⟨hwfvar, hwfvar⟩
  | step_loop_exit => exact hwfvar
  | step_loop_nondet_enter => exact ⟨hwfvar, hwfvar⟩
  | step_loop_nondet_exit => exact hwfvar
  | step_exit => exact hwfvar
  | step_funcDecl => exact hwf_ext.preserves_wfVar _ _ _ hwfvar
  | step_typeDecl => exact hwfvar
  | step_stmts_nil => exact hwfvar
  | step_stmts_cons => exact hwfvar
  | step_seq_inner _ ih => exact ih hwfvar
  | step_seq_done => exact hwfvar
  | step_seq_exit => exact hwfvar
  | step_block_body _ ih => exact ⟨hwfvar.1, ih hwfvar.2⟩
  | step_block_done => exact hwfvar.1
  | step_block_exit_match => exact hwfvar.1
  | step_block_exit_mismatch => exact hwfvar.1

/-- `Config.wfBool` is preserved under `StepStmtStar`. -/
theorem star_preserves_cfg_wfBool
    (hwf_ext : WFEvalExtension P extendEval)
    {c₁ c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval c₁ c₂)
    (hwfb : c₁.wfBool) :
    c₂.wfBool := by
  induction hstar with
  | refl => exact hwfb
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_wfBool_wfExtend P EvalCmd extendEval hwf_ext _ _ hstep hwfb)

theorem star_preserves_cfg_wfVal
    (hwf_ext : WFEvalExtension P extendEval)
    {c₁ c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval c₁ c₂)
    (hwfv : c₁.wfVal) :
    c₂.wfVal := by
  induction hstar with
  | refl => exact hwfv
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_wfVal_wfExtend P EvalCmd extendEval hwf_ext _ _ hstep hwfv)

theorem star_preserves_cfg_wfVar
    (hwf_ext : WFEvalExtension P extendEval)
    {c₁ c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval c₁ c₂)
    (hwfvar : c₁.wfVar) :
    c₂.wfVar := by
  induction hstar with
  | refl => exact hwfvar
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_wfVar_wfExtend P EvalCmd extendEval hwf_ext _ _ hstep hwfvar)

set_option linter.unusedSectionVars false in
/-- `Config.wfBool` implies `WellFormedSemanticEvalBool` on the current
    config's eval (the inner eval after walking through any blocks). -/
theorem Config.wfBool_implies_wfEval (cfg : Config P CmdT) :
    cfg.wfBool → WellFormedSemanticEvalBool cfg.getEnv.eval := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

set_option linter.unusedSectionVars false in
theorem Config.wfVal_implies_wfEval (cfg : Config P CmdT) :
    cfg.wfVal → WellFormedSemanticEvalVal cfg.getEnv.eval := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

set_option linter.unusedSectionVars false in
theorem Config.wfVar_implies_wfEval (cfg : Config P CmdT) :
    cfg.wfVar → WellFormedSemanticEvalVar cfg.getEnv.eval := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

/-- `WellFormedSemanticEvalBool` is preserved under `StepStmtStar` when the
    starting config is a top-level `.stmt`/`.stmts`/`.terminal`/`.exiting`
    (i.e., not inside a `.block`).  Generalises
    `smallStep_noFuncDecl_preserves_eval` to programs with funcDecl.

    For starts at `.block` configurations, use `star_preserves_cfg_wfBool`
    with the appropriate `Config.wfBool` precondition. -/
theorem star_preserves_wfBool
    (hwf_ext : WFEvalExtension P extendEval)
    {s : Stmt P CmdT} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.stmt s ρ) c₂)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    WellFormedSemanticEvalBool c₂.getEnv.eval := by
  have h := star_preserves_cfg_wfBool P EvalCmd extendEval hwf_ext hstar
    (show Config.wfBool (P := P) (CmdT := CmdT) (Config.stmt s ρ) from hwfb)
  exact Config.wfBool_implies_wfEval P c₂ h

theorem star_preserves_wfVal
    (hwf_ext : WFEvalExtension P extendEval)
    {s : Stmt P CmdT} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.stmt s ρ) c₂)
    (hwfv : WellFormedSemanticEvalVal ρ.eval) :
    WellFormedSemanticEvalVal c₂.getEnv.eval := by
  have h := star_preserves_cfg_wfVal P EvalCmd extendEval hwf_ext hstar
    (show Config.wfVal (P := P) (CmdT := CmdT) (Config.stmt s ρ) from hwfv)
  exact Config.wfVal_implies_wfEval P c₂ h

theorem star_preserves_wfVar
    (hwf_ext : WFEvalExtension P extendEval)
    {s : Stmt P CmdT} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.stmt s ρ) c₂)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval) :
    WellFormedSemanticEvalVar c₂.getEnv.eval := by
  have h := star_preserves_cfg_wfVar P EvalCmd extendEval hwf_ext hstar
    (show Config.wfVar (P := P) (CmdT := CmdT) (Config.stmt s ρ) from hwfvar)
  exact Config.wfVar_implies_wfEval P c₂ h

/-- Block-list variants for `Config.wfBool/Val/Var`: starting at
    `.stmts ss ρ`. -/
theorem star_preserves_wfBool_block
    (hwf_ext : WFEvalExtension P extendEval)
    {ss : List (Stmt P CmdT)} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) c₂)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    WellFormedSemanticEvalBool c₂.getEnv.eval := by
  have h := star_preserves_cfg_wfBool P EvalCmd extendEval hwf_ext hstar
    (show Config.wfBool (P := P) (CmdT := CmdT) (Config.stmts ss ρ) from hwfb)
  exact Config.wfBool_implies_wfEval P c₂ h

theorem star_preserves_wfVal_block
    (hwf_ext : WFEvalExtension P extendEval)
    {ss : List (Stmt P CmdT)} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) c₂)
    (hwfv : WellFormedSemanticEvalVal ρ.eval) :
    WellFormedSemanticEvalVal c₂.getEnv.eval := by
  have h := star_preserves_cfg_wfVal P EvalCmd extendEval hwf_ext hstar
    (show Config.wfVal (P := P) (CmdT := CmdT) (Config.stmts ss ρ) from hwfv)
  exact Config.wfVal_implies_wfEval P c₂ h

theorem star_preserves_wfVar_block
    (hwf_ext : WFEvalExtension P extendEval)
    {ss : List (Stmt P CmdT)} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) c₂)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval) :
    WellFormedSemanticEvalVar c₂.getEnv.eval := by
  have h := star_preserves_cfg_wfVar P EvalCmd extendEval hwf_ext hstar
    (show Config.wfVar (P := P) (CmdT := CmdT) (Config.stmts ss ρ) from hwfvar)
  exact Config.wfVar_implies_wfEval P c₂ h

/-! ## Eval preservation on disjoint expressions (no `noFuncDecl` requirement)

Generalizes `smallStep_noFuncDecl_preserves_eval` to programs that may contain
`funcDecl`: rather than requiring the program have no `funcDecl`s at all, we
allow them as long as the names they introduce are syntactically disjoint
from the variables referenced by a target expression `e`.

The key invariant `Config.evalSnapAgrees` states that every `e_parent` snapshot
inside the config agrees with the inner config's current eval on `(σ', e)`.
This is preserved by every step (given disjointness): on `step_funcDecl`,
inner eval extends but stays equal on `e` (disjoint); on `step_block_done`,
the snapshot is restored, and the snapshot already agreed with the inner eval.

The invariant trivially holds at top-level (`.stmt`/`.stmts`/`.terminal`/
`.exiting`), since there are no snapshots there. -/

/-- All captured `e_parent` snapshots in the config agree with the inner
    config's current eval on `(σ', e)`. -/
def Config.evalSnapAgrees (σ' : SemanticStore P) (e : P.Expr) :
    Config P CmdT → Prop
  | .stmt _ _ => True
  | .stmts _ _ => True
  | .terminal _ => True
  | .exiting _ _ => True
  | .block _ _ e_p inner =>
    e_p σ' e = inner.getEnv.eval σ' e ∧ Config.evalSnapAgrees σ' e inner
  | .seq inner _ => Config.evalSnapAgrees σ' e inner

/-- Single-step preservation of `eval` on expressions disjoint from
    `Config.funcDeclNames`.  Maintains the snapshot-agreement invariant. -/
private theorem step_preserves_eval_on_disjoint
    (hwf_ext : WFEvalExtension P extendEval)
    {c₁ c₂ : Config P CmdT}
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (σ' : SemanticStore P) (e : P.Expr)
    (hdisj : ∀ n ∈ Config.funcDeclNames c₁, n ∉ HasVarsPure.getVars (P := P) e)
    (hsnap : Config.evalSnapAgrees (P := P) σ' e c₁) :
    c₂.getEnv.eval σ' e = c₁.getEnv.eval σ' e ∧
      (∀ n ∈ Config.funcDeclNames c₂, n ∉ HasVarsPure.getVars (P := P) e) ∧
      Config.evalSnapAgrees (P := P) σ' e c₂ := by
  induction hstep with
  | step_cmd =>
    refine ⟨rfl, hdisj, ?_⟩
    simp [Config.evalSnapAgrees] at hsnap ⊢
  | step_block =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simpa [Config.funcDeclNames, Stmt.funcDeclNames] using hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_ite_true =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Stmt.funcDeclNames] at hn ⊢
      exact .inl hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_ite_false =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Stmt.funcDeclNames] at hn ⊢
      exact .inr hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_ite_nondet_true =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Stmt.funcDeclNames] at hn ⊢
      exact .inl hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_ite_nondet_false =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Stmt.funcDeclNames] at hn ⊢
      exact .inr hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_loop_enter =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Stmt.funcDeclNames, Block.funcDeclNames] at hn ⊢
      exact hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_loop_exit =>
    exact ⟨rfl, by intro n hn; simp [Config.funcDeclNames] at hn,
           by simp [Config.evalSnapAgrees]⟩
  | step_loop_nondet_enter =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Stmt.funcDeclNames, Block.funcDeclNames] at hn ⊢
      exact hn
    · simp [Config.evalSnapAgrees, Config.getEnv]
  | step_loop_nondet_exit =>
    exact ⟨rfl, by intro n hn; simp [Config.funcDeclNames] at hn,
           by simp [Config.evalSnapAgrees]⟩
  | step_exit =>
    exact ⟨rfl, by intro n hn; simp [Config.funcDeclNames] at hn,
           by simp [Config.evalSnapAgrees]⟩
  | step_funcDecl =>
    rename_i decl _ ρ_inst _
    have hname : decl.name ∉ HasVarsPure.getVars (P := P) e := by
      apply hdisj decl.name
      simp [Config.funcDeclNames, Stmt.funcDeclNames]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Config.getEnv]
      exact hwf_ext.preserves_eval_on_disjoint ρ_inst.eval ρ_inst.store decl σ' e hname
    · intro n hn; simp [Config.funcDeclNames] at hn
    · simp [Config.evalSnapAgrees]
  | step_typeDecl =>
    exact ⟨rfl, by intro n hn; simp [Config.funcDeclNames] at hn,
           by simp [Config.evalSnapAgrees]⟩
  | step_stmts_nil =>
    exact ⟨rfl, by intro n hn; simp [Config.funcDeclNames] at hn,
           by simp [Config.evalSnapAgrees]⟩
  | step_stmts_cons =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames, Block.funcDeclNames] at hn ⊢
      exact hn
    · simp [Config.evalSnapAgrees]
  | step_seq_inner hstep_inner ih =>
    rename_i inner inner' ss
    have hdisj_inner : ∀ n ∈ Config.funcDeclNames inner, n ∉ HasVarsPure.getVars (P := P) e := by
      intro n hn
      apply hdisj n
      simp [Config.funcDeclNames]; exact .inl hn
    have hsnap_inner : Config.evalSnapAgrees (P := P) σ' e inner := by
      simpa [Config.evalSnapAgrees] using hsnap
    have ⟨heq, hdisj', hsnap'⟩ := ih hdisj_inner hsnap_inner
    refine ⟨heq, ?_, ?_⟩
    · intro n hn
      simp only [Config.funcDeclNames, List.mem_append] at hn
      rcases hn with hn | hn
      · exact hdisj' n hn
      · apply hdisj n; simp [Config.funcDeclNames]; exact .inr hn
    · simp [Config.evalSnapAgrees] at hsnap ⊢
      exact hsnap'
  | step_seq_done =>
    refine ⟨rfl, ?_, ?_⟩
    · intro n hn
      apply hdisj n
      simp [Config.funcDeclNames] at hn ⊢
      exact hn
    · simp [Config.evalSnapAgrees]
  | step_seq_exit =>
    exact ⟨rfl, by intro n hn; simp [Config.funcDeclNames] at hn,
           by simp [Config.evalSnapAgrees]⟩
  | step_block_body hstep_inner ih =>
    rename_i inner inner' label σ_p e_p
    have hdisj_inner : ∀ n ∈ Config.funcDeclNames inner, n ∉ HasVarsPure.getVars (P := P) e := by
      intro n hn; apply hdisj n; simp [Config.funcDeclNames]; exact hn
    have hsnap_inner : Config.evalSnapAgrees (P := P) σ' e inner := hsnap.2
    have ⟨heq, hdisj', hsnap'⟩ := ih hdisj_inner hsnap_inner
    refine ⟨heq, ?_, ?_⟩
    · intro n hn; simp only [Config.funcDeclNames] at hn; exact hdisj' n hn
    · refine ⟨?_, hsnap'⟩
      -- Goal: e_p σ' e = inner'.getEnv.eval σ' e
      -- hsnap.1: e_p σ' e = inner.getEnv.eval σ' e
      -- heq: inner'.getEnv.eval σ' e = inner.getEnv.eval σ' e
      rw [heq]; exact hsnap.1
  | step_block_done =>
    -- c₁ = .block label σ_p e_p (.terminal ρ')
    -- c₂ = .terminal { ρ' with store := proj, eval := e_p }
    -- hsnap : e_p σ' e = ρ'.eval σ' e ∧ True
    -- Goal: c₂.eval σ' e = c₁.getEnv.eval σ' e
    -- c₂.eval = e_p; c₁.getEnv.eval = ρ'.eval
    refine ⟨?_, ?_, ?_⟩
    · simp only [Config.getEnv]
      exact hsnap.1
    · intro n hn; simp [Config.funcDeclNames] at hn
    · simp [Config.evalSnapAgrees]
  | step_block_exit_match =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [Config.getEnv]
      exact hsnap.1
    · intro n hn; simp [Config.funcDeclNames] at hn
    · simp [Config.evalSnapAgrees]
  | step_block_exit_mismatch =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [Config.getEnv]
      exact hsnap.1
    · intro n hn; simp [Config.funcDeclNames] at hn
    · simp [Config.evalSnapAgrees]

/-- Star-step preservation of `eval` on expressions disjoint from
    `Config.funcDeclNames`.  Generalizes `smallStep_noFuncDecl_preserves_eval`. -/
theorem star_preserves_eval_on_disjoint
    (hwf_ext : WFEvalExtension P extendEval)
    {c₁ c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval c₁ c₂)
    (σ' : SemanticStore P) (e : P.Expr)
    (hdisj : ∀ n ∈ Config.funcDeclNames c₁, n ∉ HasVarsPure.getVars (P := P) e)
    (hsnap : Config.evalSnapAgrees (P := P) σ' e c₁) :
    c₂.getEnv.eval σ' e = c₁.getEnv.eval σ' e := by
  suffices ∀ c₁ c₂,
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      (∀ n ∈ Config.funcDeclNames c₁, n ∉ HasVarsPure.getVars (P := P) e) →
      Config.evalSnapAgrees (P := P) σ' e c₁ →
      c₂.getEnv.eval σ' e = c₁.getEnv.eval σ' e by
    exact this c₁ c₂ hstar hdisj hsnap
  intro c₁ c₂ hstar
  induction hstar with
  | refl => intros; rfl
  | step _ mid _ hstep _ ih =>
    intro hdisj_c hsnap_c
    have ⟨heq_step, hdisj_mid, hsnap_mid⟩ :=
      step_preserves_eval_on_disjoint P EvalCmd extendEval hwf_ext hstep σ' e hdisj_c hsnap_c
    rw [ih hdisj_mid hsnap_mid, heq_step]

/-- Specialization of `star_preserves_eval_on_disjoint` to a top-level
    `.stmts ss ρ → .terminal ρ'` trace, where the snapshot-agreement
    invariant trivially holds. -/
theorem block_preserves_eval_on_disjoint
    (hwf_ext : WFEvalExtension P extendEval)
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (σ' : SemanticStore P) (e : P.Expr)
    (hdisj : ∀ n ∈ Block.funcDeclNames ss, n ∉ HasVarsPure.getVars (P := P) e)
    (hterm : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.terminal ρ')) :
    ρ'.eval σ' e = ρ.eval σ' e := by
  have h := star_preserves_eval_on_disjoint P EvalCmd extendEval hwf_ext hterm σ' e
    (by intro n hn; exact hdisj n (by simpa [Config.funcDeclNames] using hn))
    (by simp [Config.evalSnapAgrees])
  simpa [Config.getEnv] using h

/-- Exiting variant of `block_preserves_eval_on_disjoint`. -/
theorem block_preserves_eval_on_disjoint_exiting
    (hwf_ext : WFEvalExtension P extendEval)
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    (σ' : SemanticStore P) (e : P.Expr)
    (hdisj : ∀ n ∈ Block.funcDeclNames ss, n ∉ HasVarsPure.getVars (P := P) e)
    (hexit : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.exiting lbl ρ')) :
    ρ'.eval σ' e = ρ.eval σ' e := by
  have h := star_preserves_eval_on_disjoint P EvalCmd extendEval hwf_ext hexit σ' e
    (by intro n hn; exact hdisj n (by simpa [Config.funcDeclNames] using hn))
    (by simp [Config.evalSnapAgrees])
  simpa [Config.getEnv] using h

/-- Bundles `block_preserves_eval_on_disjoint` with `funcDeclNames_disjoint_of_defUseOk`:
    when the block's `defUseWellFormed` holds against `defined`, every expression `e`
    whose free variables are all in `defined` evaluates the same way before and after.

    This is the form most useful at simulation call sites, where the surrounding
    `defUseOk` invariant from `BlockInitEnvWF` automatically discharges the
    funcDecl-disjointness via the strengthened `defUseWellFormed.funcDecl` case. -/
theorem block_preserves_eval_via_defUseOk
    [DecidableEq P.Ident] [HasVarsImp P CmdT] [HasVarsPure P CmdT]
    (hwf_ext : WFEvalExtension P extendEval)
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (defined : P.Ident → Bool)
    (hdef : Block.defUseWellFormed defined ss = true)
    (σ' : SemanticStore P) (e : P.Expr)
    (he : ∀ n ∈ HasVarsPure.getVars (P := P) e, defined n)
    (hterm : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.terminal ρ')) :
    ρ'.eval σ' e = ρ.eval σ' e := by
  apply block_preserves_eval_on_disjoint P EvalCmd extendEval hwf_ext ss ρ ρ' σ' e _ hterm
  intro n hn hgv
  have h_undef := Block.funcDeclNames_disjoint_of_defUseOk defined ss hdef n hn
  have h_def := he n hgv
  rw [h_def] at h_undef
  cases h_undef

theorem block_preserves_eval_via_defUseOk_exiting
    [DecidableEq P.Ident] [HasVarsImp P CmdT] [HasVarsPure P CmdT]
    (hwf_ext : WFEvalExtension P extendEval)
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String) (defined : P.Ident → Bool)
    (hdef : Block.defUseWellFormed defined ss = true)
    (σ' : SemanticStore P) (e : P.Expr)
    (he : ∀ n ∈ HasVarsPure.getVars (P := P) e, defined n)
    (hexit : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.exiting lbl ρ')) :
    ρ'.eval σ' e = ρ.eval σ' e := by
  apply block_preserves_eval_on_disjoint_exiting P EvalCmd extendEval hwf_ext ss ρ ρ' lbl
    σ' e _ hexit
  intro n hn hgv
  have h_undef := Block.funcDeclNames_disjoint_of_defUseOk defined ss hdef n hn
  have h_def := he n hgv
  rw [h_def] at h_undef
  cases h_undef

/-- Statement-level analog of `block_preserves_eval_via_defUseOk` (terminal). -/
theorem stmt_preserves_eval_via_defUseOk
    [DecidableEq P.Ident] [HasVarsImp P CmdT] [HasVarsPure P CmdT]
    (hwf_ext : WFEvalExtension P extendEval)
    (s : Stmt P CmdT) (ρ ρ' : Env P) (defined : P.Ident → Bool)
    (hdef : Stmt.defUseWellFormed defined s = true)
    (σ' : SemanticStore P) (e : P.Expr)
    (he : ∀ n ∈ HasVarsPure.getVars (P := P) e, defined n)
    (hterm : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')) :
    ρ'.eval σ' e = ρ.eval σ' e := by
  have h := star_preserves_eval_on_disjoint P EvalCmd extendEval hwf_ext hterm σ' e
    (by
      intro n hn hgv
      have h_undef := Stmt.funcDeclNames_disjoint_of_defUseOk defined s hdef n
        (by simpa [Config.funcDeclNames] using hn)
      have h_def := he n hgv
      rw [h_def] at h_undef
      cases h_undef)
    (by simp [Config.evalSnapAgrees])
  simpa [Config.getEnv] using h

/-- Statement-level analog of `block_preserves_eval_via_defUseOk_exiting`. -/
theorem stmt_preserves_eval_via_defUseOk_exiting
    [DecidableEq P.Ident] [HasVarsImp P CmdT] [HasVarsPure P CmdT]
    (hwf_ext : WFEvalExtension P extendEval)
    (s : Stmt P CmdT) (ρ ρ' : Env P) (lbl : String) (defined : P.Ident → Bool)
    (hdef : Stmt.defUseWellFormed defined s = true)
    (σ' : SemanticStore P) (e : P.Expr)
    (he : ∀ n ∈ HasVarsPure.getVars (P := P) e, defined n)
    (hexit : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.exiting lbl ρ')) :
    ρ'.eval σ' e = ρ.eval σ' e := by
  have h := star_preserves_eval_on_disjoint P EvalCmd extendEval hwf_ext hexit σ' e
    (by
      intro n hn hgv
      have h_undef := Stmt.funcDeclNames_disjoint_of_defUseOk defined s hdef n
        (by simpa [Config.funcDeclNames] using hn)
      have h_def := he n hgv
      rw [h_def] at h_undef
      cases h_undef)
    (by simp [Config.evalSnapAgrees])
  simpa [Config.getEnv] using h

end -- section

section

variable (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P]
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
  | .block _ _ _ inner, aid => isAtAssert inner aid
  | .seq inner _, aid => isAtAssert inner aid
  | _, _ => False

omit [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] in
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
  | .block _ _ _ inner => exact noMatchingAssert_not_isAtAssert inner label expr hno
  | .seq inner _ => exact noMatchingAssert_not_isAtAssert inner label expr hno.1

omit [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] in
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
    -- New shape: .seq (.block .none ρ.store (.stmts body ρ')) [loop]
    -- noMatchingAssert: inner covers, AND [loop] covers.
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    exact ⟨hno.2, hno, True.intro⟩
  | step_loop_exit => trivial
  | step_loop_nondet_enter =>
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    exact ⟨hno.2, hno, True.intro⟩
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
    exact ih (@step_preserves_noMatchingAssert P _ _ _ _ extendEval _ _ _ hstep hno_c)

/-! ## isAtAssert inversion lemmas -/

/-- If execution inside a block reaches a config where isAtAssert holds,
    then the config must be `.block label inner` where `inner` is reachable
    from the block's body and satisfies `isAtAssert`. -/
theorem block_isAtAssert_inner
    (label : Option String) (σ_parent : SemanticStore P) (e_parent : SemanticEval P)
    (inner₀ cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.block label σ_parent e_parent inner₀) cfg)
    (hat : isAtAssert P cfg a) :
    ∃ inner, cfg = .block label σ_parent e_parent inner ∧
      StepStmtStar P (EvalCmd P) extendEval inner₀ inner ∧
      isAtAssert P inner a := by
  generalize hsrc : Config.block label σ_parent e_parent inner₀ = src at hstar
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
    (h_IsAtAssert_block : ∀ {label σ_parent e_parent inner a},
      IsAtAssert inner a → IsAtAssert (.block label σ_parent e_parent inner) a)
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
        hv a (.block _ _ _ cfg) (block_inner_star P EvalCmd extendEval _ _ _ _ _ hr) (h_IsAtAssert_block hat)) hnf
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

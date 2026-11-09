/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StoreRelations
public import Strata.DL.Imperative.Stmt
public import Strata.Util.RelationsProps

---------------------------------------------------------------------

namespace Imperative

public section

universe u

/-! ## Execution Environment

An `Env` bundles the store and the expression factory into a single record.
Assertion outcomes are not part of the environment: the statement semantics
`StepStmtE` records each assertion as a trace event instead.
-/

/-- Execution environment: store and expression factory. -/
structure Env (P : PureExpr) where
  /-- The current variable store. -/
  store : SemanticStore P
  /-- The read-only expression factory used to evaluate expressions. Commands,
      guards, and events read it from the active configuration as `ρ.factory`;
      every statement step preserves it, and leaving a block projects only the
      store. -/
  factory : P.Factory

/-- Lift a predicate on generated strings to the identifiers representing those
strings. -/
@[expose] def IdentOfStringKind {P : PureExpr} [HasIdent P]
    (Q : String → Prop) (ident : P.Ident) : Prop :=
  ∃ name, Q name ∧ ident = HasIdent.ident (P := P) name

/-- `Env.varsUndefined Q ρ` says the environment `ρ` leaves every `Q`-kind slot
undefined: for each string `s` satisfying the label-kind predicate `Q` (the
kind of label a pass generates), `ρ`'s store maps `HasIdent.ident s` to `none`.

It captures the "generated names start undefined" precondition shared by the
pipeline passes, parameterised by the kind each pass generates so a single
initial store can satisfy several passes' obligations at disjoint kinds. -/
abbrev Env.varsUndefined {P : PureExpr} [HasIdent P]
    (Q : String → Prop) (ρ : Env P) : Prop :=
  ρ.store.varsUndefined (IdentOfStringKind Q)

/-- A target environment extends a source environment with classified register
bindings while preserving the factory. -/
@[expose] def Env.ExtendsWith {P : PureExpr} (Extra : P.Ident → Prop)
    (source target : Env P) : Prop :=
  source.factory = target.factory ∧
  StoreExtendsWith Extra source.store target.store

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
- An execution environment (`Env`) bundling store and evaluator
-/
inductive Config (P : PureExpr.{u}) (CmdT : Type) : Type u where
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
      - The block label is `Option String` — `none` denotes an unnamed block, and is only
        used for scoping of variables; no explicit exit statement can reach this block.
      - The `SemanticStore P` is the parent store at
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

/-- Events emitted by the active base command in the next statement step.
Administrative configurations and non-command statements are silent. -/
@[expose] def Config.emittedEvents : Config P (Cmd P) → Trace P
  | .stmt (.cmd command) ρ => Cmd.emittedEvents P command ρ.factory ρ.store
  | .block _ _ inner => inner.emittedEvents
  | .seq inner _ => inner.emittedEvents
  | _ => []

/-- The terminal-or-exiting configuration selected by an `Option String`:
`none` denotes the terminal outcome `.terminal ρ`, `some lbl` the exiting outcome
`.exiting lbl ρ`.  Lets a lemma conclude over *either* outcome uniformly. -/
@[expose] def Env.outcomeConfig (oc : Option String) (ρ : Env P) :
    Config P (Cmd P) :=
  match oc with
  | none => .terminal ρ
  | some lbl => .exiting lbl ρ

/-- Extend `exitsCoveredByBlocks` to configurations.

    The label list has type `List String` (matching `Stmt.exit`'s mandatory-label
    AST).  An anonymous (`.none`) `Config.block` (introduced by the loop/if's body
    wrapper) does not contribute a label — labeled exits cannot match `.none`,
    and unlabeled exits do not exist as user statements. -/
@[expose] def Config.exitsCoveredByBlocks : List String → Config P CmdT → Prop
  | labels, .stmt s _ => s.exitsCoveredByBlocks labels
  | labels, .stmts ss _ => Block.exitsCoveredByBlocks labels ss
  | _, .terminal _ => True
  | labels, .exiting l _ => l ∈ labels
  | labels, .block none _ inner => Config.exitsCoveredByBlocks labels inner
  | labels, .block (some l) _ inner => Config.exitsCoveredByBlocks (l :: labels) inner
  | labels, .seq inner ss =>
    Config.exitsCoveredByBlocks labels inner ∧ Block.exitsCoveredByBlocks labels ss

/-! ## Config-level definedness / undefinedness invariants

Two dual `Config`-recursive predicates, keyed on a set `Q` of identifiers,
threaded through a run to track store contents across the execution stack:

* `Config.varsDefined Q c` — every `Q`-var is defined in `c`'s operative store
  and in every enclosing block-parent store.  Monotone (no step undefines a
  slot), so it makes no claim about the pending statements.
* `Config.varsUndefined excludeScoped Q c` — every `Q`-var is undefined in `c`'s
  operative store and in every enclosing block-parent store, AND no pending
  statement defines a `Q`-var.  The pending-statement clause is what makes
  undefinedness stable across a step (an `init`/`set` of a `Q`-var would break
  it), the dual of the monotone `varsDefined` which needs no such clause.

  `excludeScoped` selects which `Stmt.definedVars` flag that clause uses, and with
  it how a block is treated.  At `false` a `Q`-var must stay undefined
  *everywhere*, so the invariant is required of a block's body too.  At `true`
  only top-level definitions count, so a block-local `init` of a `Q`-var is
  allowed: leaving the block projects the inner store through the saved parent
  store, which still has the var undefined. -/

@[expose] def Config.varsDefined {P : PureExpr} {CmdT : Type} (Q : P.Ident → Prop) :
    Config P CmdT → Prop
  | .stmt _ ρ => ρ.store.varsDefined Q
  | .stmts _ ρ => ρ.store.varsDefined Q
  | .terminal ρ => ρ.store.varsDefined Q
  | .exiting _ ρ => ρ.store.varsDefined Q
  | .block _ σ_parent inner => σ_parent.varsDefined Q ∧ Config.varsDefined Q inner
  | .seq inner _ => Config.varsDefined Q inner

/-- Single-identifier specialisation of `Config.varsDefined`. -/
abbrev Config.varDefined {P : PureExpr} {CmdT : Type} (y : P.Ident) :
    Config P CmdT → Prop :=
  Config.varsDefined (· = y)

@[expose] def Config.varsUndefined {P : PureExpr} [HasFvars P]
    {CmdT : Type} [HasVarsImp P CmdT] (excludeScoped : Bool) (Q : P.Ident → Prop) :
    Config P CmdT → Prop
  | .stmt s ρ => ∀ y, Q y → ρ.store y = none ∧
      y ∉ Stmt.definedVars (P := P) (C := CmdT) s excludeScoped
  | .stmts ss ρ => ∀ y, Q y → ρ.store y = none ∧
      ∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := CmdT) s excludeScoped
  | .terminal ρ => ρ.store.varsUndefined Q
  | .exiting _ ρ => ρ.store.varsUndefined Q
  | .block _ σ_parent inner =>
      match excludeScoped with
      | true => σ_parent.varsUndefined Q
      | false => σ_parent.varsUndefined Q ∧ Config.varsUndefined false Q inner
  | .seq inner ss => Config.varsUndefined excludeScoped Q inner ∧
      ∀ y, Q y → ∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := CmdT) s excludeScoped

/-- Every store reachable from `c` — its operative store and the saved parent store
    of every enclosing block — holds only values. -/
@[expose] def Config.storeWellDefined {P : PureExpr} [HasVal P] {CmdT : Type} :
    Config P CmdT → Prop
  | .stmt _ ρ => WellFormedStore ρ.store ρ.factory
  | .stmts _ ρ => WellFormedStore ρ.store ρ.factory
  | .terminal ρ => WellFormedStore ρ.store ρ.factory
  | .exiting _ ρ => WellFormedStore ρ.store ρ.factory
  | .block _ σ_parent inner =>
      WellFormedStore σ_parent inner.getEnv.factory ∧ Config.storeWellDefined inner
  | .seq inner _ => Config.storeWellDefined inner

/-! ## Single-step relation -/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasBoolOps P]

/-- Event-labeled single statement step.  The expression evaluator is `P.eval`
(part of the `PureExpr` bundle); command steps use the command relation
`EvalCmd : EvalCmdParamE`.

A `StepStmtE` derivation describes one operational step and carries one event
list; it never concatenates traces.  A command step exposes exactly the events
its command semantics produces.  Every other rule is administrative and emits
no events; the sequence and block context rules propagate the inner step's
events unchanged.  Intended choices, such as nondeterministic conditionals and
loops, remain nondeterministic. -/
inductive StepStmtE
    {EventT : Type _}
    (EvalCmd : EvalCmdParamE P CmdT EventT) :
    Config P CmdT → List EventT → Config P CmdT → Prop where
  /-- Execute one command and expose exactly the event list produced by its
  command semantics. -/
  | step_cmd :
      EvalCmd ρ.factory ρ.store cmd σ' emitted →
      StepStmtE EvalCmd
        (.stmt (.cmd cmd) ρ) emitted
        (.terminal { ρ with store := σ' })

  /-- A labeled block steps to a block context that wraps its body as `.stmts`.
      The AST label `label : String` is lifted into `.some label` for the
      `Config.block` wrapper (whose label is `Option String`).
      The parent store `ρ.store` is saved so that block-local variables can be
      popped on exit. -/
  | step_block :
      StepStmtE EvalCmd
        (.stmt (.block label ss _) ρ) []
        (.block (.some label) ρ.store (.stmts ss ρ))

  /-- If the condition of an `ite` statement evaluates to true, step to the
      then branch.  The branch is wrapped in a block so that variables
      `init`'d inside are projected away on exit (matching `definedVars`
      with `excludeScoped = true`). -/
  | step_ite_true :
      P.eval ρ.factory ρ.store c = .some (HasBool.ttVal ρ.factory) →
      ----
      StepStmtE EvalCmd
        (.stmt (.ite (.det c) tss ess _) ρ) []
        (.block .none ρ.store (.stmts tss ρ))

  /-- If the condition of an `ite` statement evaluates to false, step to the
      else branch (scoped via block wrapper). -/
  | step_ite_false :
      P.eval ρ.factory ρ.store c = .some (HasBool.ffVal ρ.factory) →
      ----
      StepStmtE EvalCmd
        (.stmt (.ite (.det c) tss ess _) ρ) []
        (.block .none ρ.store (.stmts ess ρ))

  /-- Non-deterministic ite: step to the then branch (scoped). -/
  | step_ite_nondet_true :
      StepStmtE EvalCmd
        (.stmt (.ite .nondet tss ess _) ρ) []
        (.block .none ρ.store (.stmts tss ρ))

  /-- Non-deterministic ite: step to the else branch (scoped). -/
  | step_ite_nondet_false :
      StepStmtE EvalCmd
        (.stmt (.ite .nondet tss ess _) ρ) []
        (.block .none ρ.store (.stmts ess ρ))

  /-- If a loop guard is true, execute the body (followed by the loop again).
      Loop invariants are not evaluated during execution: they are treated
      purely as verification-condition annotations elsewhere, not as runtime
      assertions.  The invariants are labeled pairs `(String × P.Expr)`.

      The body alone is wrapped in an unnamed `.block`, sequenced with the
      recursive loop.  This means each iteration runs the body in its own
      block scope: variables `init`'d inside body are projected away at the
      end of each iteration, allowing the next iteration's body to re-`init`
      the same names. -/
  | step_loop_enter :
      P.eval ρ.factory ρ.store g = .some (HasBool.ttVal ρ.factory) →
      ----
      StepStmtE EvalCmd
        (.stmt (.loop (.det g) m inv body md) ρ) []
        (.seq
          (.block .none ρ.store (.stmts body ρ))
          [.loop (.det g) m inv body md])

  /-- If a loop guard is false, terminate the loop.  As with `step_loop_enter`,
      loop invariants are not evaluated during execution. -/
  | step_loop_exit :
      P.eval ρ.factory ρ.store g = .some (HasBool.ffVal ρ.factory) →
      ----
      StepStmtE EvalCmd
        (.stmt (.loop (.det g) m inv body _) ρ) []
        (.terminal ρ)

  /-- Non-deterministic loop: enter the body.  As with the det variant,
      loop invariants are not evaluated during execution; the body alone is
      wrapped in an unnamed `.block` and sequenced with the recursive loop,
      giving each iteration its own block scope. -/
  | step_loop_nondet_enter :
      StepStmtE EvalCmd
        (.stmt (.loop .nondet m inv body md) ρ) []
        (.seq
          (.block .none ρ.store (.stmts body ρ))
          [.loop .nondet m inv body md])

  /-- Non-deterministic loop: exit the loop. -/
  | step_loop_nondet_exit :
      StepStmtE EvalCmd
        (.stmt (.loop .nondet m inv body _) ρ) []
        (.terminal ρ)

  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
      StepStmtE EvalCmd
        (.stmt (.exit label _) ρ) []
        (.exiting label ρ)

  /-- A type declaration is a no-op at runtime. -/
  | step_typeDecl :
      StepStmtE EvalCmd
        (.stmt (.typeDecl _tc _md) ρ) []
        (.terminal ρ)

  /-- An empty list of statements steps to `.terminal` with no state changes. -/
  | step_stmts_nil :
      StepStmtE EvalCmd
        (.stmts [] ρ) []
        (.terminal ρ)

  /-- To evaluate a non-empty sequence, enter a seq context that processes
      the first statement while remembering the remaining statements. -/
  | step_stmts_cons :
      StepStmtE EvalCmd
        (.stmts (s :: ss) ρ) []
        (.seq (.stmt s ρ) ss)

  /-- A seq context steps its inner config forward, propagating its events. -/
  | step_seq_inner :
      StepStmtE EvalCmd inner emitted inner' →
      ----
      StepStmtE EvalCmd
        (.seq inner ss) emitted
        (.seq inner' ss)

  /-- When the inner config of a seq reaches terminal, continue with the
      remaining statements. -/
  | step_seq_done :
      StepStmtE EvalCmd
        (.seq (.terminal ρ') ss) []
        (.stmts ss ρ')

  /-- When the inner config of a seq exits, propagate the exit
      (skip remaining statements). -/
  | step_seq_exit :
      StepStmtE EvalCmd
        (.seq (.exiting label ρ') ss) []
        (.exiting label ρ')

  /-- A block context steps its inner body one step forward, propagating its
      events.  The inner body can be any config (stmts, seq, etc.). -/
  | step_block_body :
      StepStmtE EvalCmd inner emitted inner' →
      ----
      StepStmtE EvalCmd
        (.block label σ_parent inner) emitted
        (.block label σ_parent inner')

  /-- When a block's inner body reaches terminal, the block terminates.
      The resulting store is projected through the parent store: only variables
      that existed before the block keep their (possibly updated) values;
      variables initialized inside the block are discarded.  The factory is
      preserved. -/
  | step_block_done :
      StepStmtE EvalCmd
        (.block label σ_parent (.terminal ρ')) []
        (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

  /-- When a block's inner body exits with a matching label, the block consumes it.
      The store is projected; the factory is preserved. -/
  | step_block_exit_match :
      label = .some l →
      ----
      StepStmtE EvalCmd
        (.block label σ_parent (.exiting l ρ')) []
        (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

  /-- When a block's inner body exits with a non-matching label, the exit propagates.
      Includes the case where the block's own label is `.none` (anonymous loop/ite
      wrapper, which never matches a labeled exit) as well as any other mismatched
      `.some` label.  The store is projected since we're leaving this block. -/
  | step_block_exit_mismatch :
      label ≠ .some l →
      ----
      StepStmtE EvalCmd
        (.block label σ_parent (.exiting l ρ')) []
        (.exiting l { ρ' with store := projectStore σ_parent ρ'.store })

/-- Structured multi-step execution with a chronological event trace.
`ReflTransTrace` concatenates the event list from each successive step as
`emitted ++ rest`; this closure, not `StepStmtE`, performs trace
concatenation. -/
abbrev StepStmtStarE
    {EventT : Type _}
    (EvalCmd : EvalCmdParamE P CmdT EventT) :
    Config P CmdT → List EventT → Config P CmdT → Prop :=
  ReflTransTrace (StepStmtE P EvalCmd)

end

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [HasBool P] [HasBoolOps P] [HasFvars P] [HasOps P]

/-! ## Config-level WF predicates -/

variable [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

/-- Config-level `WellFormedSemanticEval` invariant on the active environment's
    factory. -/
def Config.wfEval (c : Config P CmdT) : Prop :=
  WellFormedSemanticEval (P := P) c.getEnv.factory

end -- section

end -- public section
end Imperative

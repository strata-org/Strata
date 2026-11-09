/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.Logic.TraceInterp

/-! # Big-step event semantics of call-free programs

A big-step presentation of the reference event semantics (`StepStmtStarE` over
`EvalCmdE`, no calls), with one factory:

* `BRun F ss σ evs o` — the statement list runs from store `σ` to outcome `o` (normal
  end or `exit l`, with the store), emitting `evs`;
* `BReach F ss σ evs` — a run of the list from `σ` emits `evs` and stops right after a
  command emitting events (a prefix of an execution, such as the prefix ending at a failing
  assertion), so `evs` ends with the events of that command.

Blocks, `ite` branches and loop iterations project the store on exit (`projectStore`), as
the small-step semantics does.  A loop enters its body when its guard admits it
(`guardEnters`) and stops when its guard admits stopping (`guardExits`); a nondeterministic
guard admits both.

Key definitions: `PStmts`, `guardEnters`, `guardExits`, `BRun`, `BReach`, `evalInterp`,
`FailsAt`, `Claim`, `Fails`. -/

namespace Imperative
namespace BigStep

public section

/-- A statement of a program over commands and calls. -/
abbrev PStmt (P : PureExpr) := Stmt P (CmdExt P)
/-- A list of statements of a program over commands and calls. -/
abbrev PStmts (P : PureExpr) := List (PStmt P)

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasBool P] [HasFvar P]

/-- Commands under the event semantics; calls have no step. -/
@[expose] def EvalE : EvalCmdParamE P (CmdExt P) (Event P)
  | f, σ, .cmd c, σ', evs => EvalCmdE P f σ c σ' evs
  | _, _, .call _ _ _, _, _ => False

/-- How a statement list ends. -/
inductive Outcome (P : PureExpr) where
  | normal (σ : SemanticStore P)
  | exit (l : String) (σ : SemanticStore P)

/-- The outcome with its store projected on a parent store (leaving a scope). -/
@[expose] def Outcome.proj (σp : SemanticStore P) : (Outcome P) → (Outcome P)
  | .normal σ => .normal (projectStore σp σ)
  | .exit l σ => .exit l (projectStore σp σ)

/-- The store an outcome ends with. -/
@[expose] def Outcome.store : Outcome P → SemanticStore P
  | .normal σ => σ
  | .exit _ σ => σ

/-- The outcome of a block labelled `l` whose body ended with `o`. -/
@[expose] def Outcome.block (l : String) (σp : SemanticStore P) : (Outcome P) → (Outcome P)
  | .normal σ => .normal (projectStore σp σ)
  | .exit l' σ => if l' = l then .normal (projectStore σp σ) else .exit l' (projectStore σp σ)

/-- The loop guard `g` lets the loop enter its body from the store `σ`: a deterministic guard
    evaluates to `true`; a nondeterministic guard always does. -/
@[expose] def guardEnters (F : P.Factory) (σ : SemanticStore P) : ExprOrNondet P → Prop
  | .det g => P.eval F σ g = some (HasBool.ttVal F)
  | .nondet => True

/-- The loop guard `g` lets the loop stop at the store `σ`: a deterministic guard evaluates to
    `false`; a nondeterministic guard always does. -/
@[expose] def guardExits (F : P.Factory) (σ : SemanticStore P) : ExprOrNondet P → Prop
  | .det g => P.eval F σ g = some (HasBool.ffVal F)
  | .nondet => True

mutual
/-- Big-step run of a statement list. -/
inductive BRun (F : P.Factory) : (PStmts P) → SemanticStore P →
    List (Event P) → (Outcome P) → Prop where
  | nil : BRun F [] σ [] (.normal σ)
  | cons_normal : BRunS F s σ evs1 (.normal σ1) → BRun F rest σ1 evs2 o →
      BRun F (s :: rest) σ (evs1 ++ evs2) o
  | cons_exit : BRunS F s σ evs (.exit l σ1) → BRun F (s :: rest) σ evs (.exit l σ1)

/-- Big-step run of one statement. -/
inductive BRunS (F : P.Factory) : (PStmt P) → SemanticStore P →
    List (Event P) → (Outcome P) → Prop where
  | cmd : EvalE F σ c σ' evs → BRunS F (.cmd c) σ evs (.normal σ')
  | ite_true : P.eval F σ c = some (HasBool.ttVal F) → BRun F tss σ evs o →
      BRunS F (.ite (.det c) tss ess md) σ evs (o.proj σ)
  | ite_false : P.eval F σ c = some (HasBool.ffVal F) → BRun F ess σ evs o →
      BRunS F (.ite (.det c) tss ess md) σ evs (o.proj σ)
  | ite_nondet_true : BRun F tss σ evs o → BRunS F (.ite .nondet tss ess md) σ evs (o.proj σ)
  | ite_nondet_false : BRun F ess σ evs o → BRunS F (.ite .nondet tss ess md) σ evs (o.proj σ)
  | block : BRun F ss σ evs o → BRunS F (.block l ss md) σ evs (o.block l σ)
  | exit : BRunS F (.exit l md) σ [] (.exit l σ)
  | typeDecl : BRunS F (.typeDecl tc md) σ [] (.normal σ)
  /-- The guard lets the loop stop: it ends normally, unchanged. -/
  | loop_exit : guardExits F σ g → BRunS F (.loop g m inv body md) σ [] (.normal σ)
  /-- The guard lets the loop enter its body, which ends normally; the loop runs again from
      the store of the iteration projected on its entry store. -/
  | loop_iter : guardEnters F σ g → BRun F body σ evs1 (.normal σ1) →
      BRunS F (.loop g m inv body md) (projectStore σ σ1) evs2 o →
      BRunS F (.loop g m inv body md) σ (evs1 ++ evs2) o
  /-- The guard lets the loop enter its body, which exits: so does the loop. -/
  | loop_break : guardEnters F σ g → BRun F body σ evs (.exit l σ1) →
      BRunS F (.loop g m inv body md) σ evs (.exit l (projectStore σ σ1))
end

mutual
/-- A run of a statement list emits `evs` and stops right after a command emitting events. -/
inductive BReach (F : P.Factory) : (PStmts P) → SemanticStore P →
    List (Event P) → Prop where
  | here : BReachS F s σ evs → BReach F (s :: rest) σ evs
  | later : BRunS F s σ evs1 (.normal σ1) → BReach F rest σ1 evs2 →
      BReach F (s :: rest) σ (evs1 ++ evs2)

/-- A run of one statement emits `evs` and stops right after a command emitting events. -/
inductive BReachS (F : P.Factory) : (PStmt P) → SemanticStore P →
    List (Event P) → Prop where
  | cmd : EvalE F σ c σ' evs → evs ≠ [] → BReachS F (.cmd c) σ evs
  | ite_true : P.eval F σ c = some (HasBool.ttVal F) → BReach F tss σ evs →
      BReachS F (.ite (.det c) tss ess md) σ evs
  | ite_false : P.eval F σ c = some (HasBool.ffVal F) → BReach F ess σ evs →
      BReachS F (.ite (.det c) tss ess md) σ evs
  | ite_nondet_true : BReach F tss σ evs → BReachS F (.ite .nondet tss ess md) σ evs
  | ite_nondet_false : BReach F ess σ evs → BReachS F (.ite .nondet tss ess md) σ evs
  | block : BReach F ss σ evs → BReachS F (.block l ss md) σ evs
  /-- The guard lets the loop enter its body, which stops. -/
  | loop_here : guardEnters F σ g → BReach F body σ evs →
      BReachS F (.loop g m inv body md) σ evs
  /-- The guard lets the loop enter its body, which ends normally; the next iterations stop. -/
  | loop_later : guardEnters F σ g → BRun F body σ evs1 (.normal σ1) →
      BReachS F (.loop g m inv body md) (projectStore σ σ1) evs2 →
      BReachS F (.loop g m inv body md) σ (evs1 ++ evs2)
end

/-- The interpretation of a condition as its evaluation to `true` under the event's factory
    and store, in a single world. -/
@[expose] def evalInterp : ConditionInterp P :=
  ⟨Unit, fun _ c => P.eval c.factory c.store c.expr = some (HasBool.ttVal c.factory)⟩

/-- The event is a failing occurrence of the target `t` with the condition `e`: an assertion
    with the label and metadata of `t` and the condition `e`, evaluating to false, or a cover
    with the label and metadata of `t` and the condition `e`, evaluating to true. -/
@[expose] def FailsAt (t : AssertId P) (e : P.Expr) : Event P → Prop
  | .assert arg => arg.label = t.label ∧ arg.metadata = t.md ∧ arg.expr = e ∧
      P.eval arg.factory arg.store arg.expr = some (HasBool.ffVal arg.factory)
  | .cover arg => arg.label = t.label ∧ arg.metadata = t.md ∧ arg.expr = e ∧
      P.eval arg.factory arg.store arg.expr = some (HasBool.ttVal arg.factory)
  | .assume _ => False

/-- The events `tr` claim a failure of the target `t` with the condition `e`: they end with a
    failing occurrence of `t` with the condition `e`, every assumption before it evaluating to
    `true`. A list fails `t` with the condition `e` exactly when a reach of it emits events that
    claim that failure (`fails_iff_claim`). -/
@[expose] def Claim (t : AssertId P) (e : P.Expr) (tr : List (Event P)) : Prop :=
  ∃ evs ev, tr = evs ++ [ev] ∧ Trace.AssumptionsHold P evalInterp () evs ∧ FailsAt t e ev

/-- A statement list fails target `t` with the condition `e` from store `σ`: a run reaches a
    failing occurrence of `t` with the condition `e`, every assumption before it evaluating to
    `true` (`Trace.AssumptionsHold` under `evalInterp`). -/
@[expose] def Fails (F : P.Factory) (ss : (PStmts P)) (σ : SemanticStore P)
    (t : AssertId P) (e : P.Expr) : Prop :=
  ∃ evs ev, BReach F ss σ (evs ++ [ev]) ∧ Trace.AssumptionsHold P evalInterp () evs ∧
    FailsAt t e ev

end -- public section

end BigStep
end Imperative

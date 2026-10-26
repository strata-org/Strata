/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.Logic.TraceInterp

/-! # Big-step event semantics of loop-free and obligation programs

A big-step presentation of the reference event semantics (`StepStmtStarE` over
`EvalCmdE`, no calls) restricted to the constructs of loop-free and obligation programs,
with one factory:

* `BRun F ss σ evs o` — the statement list runs from store `σ` to outcome `o` (normal
  end or `exit l`, with the store), emitting `evs`;
* `BReach F ss σ evs` — a run of the list from `σ` emits `evs` and stops right after a
  command (a prefix of an execution, such as the prefix ending at a failing assertion).

Blocks and `ite` branches project the store on exit (`projectStore`), as the small-step
semantics does.

Key definitions: `PStmts`, `BRun`, `BReach`, `evalInterp`, `FailsAt`, `Fails`. -/

namespace Imperative
namespace BigStep

public section

/-- A statement of a loop-free or obligation program. -/
abbrev PStmt (P : PureExpr) := Stmt P (CmdExt P)
/-- A list of statements of a loop-free or obligation program. -/
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

/-- The outcome of a block labelled `l` whose body ended with `o`. -/
@[expose] def Outcome.block (l : String) (σp : SemanticStore P) : (Outcome P) → (Outcome P)
  | .normal σ => .normal (projectStore σp σ)
  | .exit l' σ => if l' = l then .normal (projectStore σp σ) else .exit l' (projectStore σp σ)

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
  | ite_true : P.eval F σ c = some HasBool.tt → BRun F tss σ evs o →
      BRunS F (.ite (.det c) tss ess md) σ evs (o.proj σ)
  | ite_false : P.eval F σ c = some HasBool.ff → BRun F ess σ evs o →
      BRunS F (.ite (.det c) tss ess md) σ evs (o.proj σ)
  | ite_nondet_true : BRun F tss σ evs o → BRunS F (.ite .nondet tss ess md) σ evs (o.proj σ)
  | ite_nondet_false : BRun F ess σ evs o → BRunS F (.ite .nondet tss ess md) σ evs (o.proj σ)
  | block : BRun F ss σ evs o → BRunS F (.block l ss md) σ evs (o.block l σ)
  | exit : BRunS F (.exit l md) σ [] (.exit l σ)
  | typeDecl : BRunS F (.typeDecl tc md) σ [] (.normal σ)
end

mutual
/-- A run of a statement list emits `evs` and stops right after a command. -/
inductive BReach (F : P.Factory) : (PStmts P) → SemanticStore P →
    List (Event P) → Prop where
  | here : BReachS F s σ evs → BReach F (s :: rest) σ evs
  | later : BRunS F s σ evs1 (.normal σ1) → BReach F rest σ1 evs2 →
      BReach F (s :: rest) σ (evs1 ++ evs2)

/-- A run of one statement emits `evs` and stops right after a command. -/
inductive BReachS (F : P.Factory) : (PStmt P) → SemanticStore P →
    List (Event P) → Prop where
  | cmd : EvalE F σ c σ' evs → BReachS F (.cmd c) σ evs
  | ite_true : P.eval F σ c = some HasBool.tt → BReach F tss σ evs →
      BReachS F (.ite (.det c) tss ess md) σ evs
  | ite_false : P.eval F σ c = some HasBool.ff → BReach F ess σ evs →
      BReachS F (.ite (.det c) tss ess md) σ evs
  | ite_nondet_true : BReach F tss σ evs → BReachS F (.ite .nondet tss ess md) σ evs
  | ite_nondet_false : BReach F ess σ evs → BReachS F (.ite .nondet tss ess md) σ evs
  | block : BReach F ss σ evs → BReachS F (.block l ss md) σ evs
end

/-- The interpretation of a condition as its evaluation to `true` under the event's factory
    and store, in a single world. -/
@[expose] def evalInterp : ConditionInterp P :=
  ⟨Unit, fun _ c => P.eval c.factory c.store c.expr = some HasBool.tt⟩

/-- The event is a failing occurrence of the target: an assertion with the target id whose
    condition evaluates to false, or a cover with the target id whose condition evaluates
    to true. -/
@[expose] def FailsAt (t : AssertId P) : Event P → Prop
  | .assert arg => arg.label = t.label ∧ arg.expr = t.expr ∧
      P.eval arg.factory arg.store arg.expr = some HasBool.ff
  | .cover arg => arg.label = t.label ∧ arg.expr = t.expr ∧
      P.eval arg.factory arg.store arg.expr = some HasBool.tt
  | .assume _ => False

/-- A statement list fails target `t` from store `σ`: a run reaches a failing occurrence
    of `t`, every assumption before it evaluating to `true` (`Trace.AssumptionsHold` under
    `evalInterp`). -/
@[expose] def Fails (F : P.Factory) (ss : (PStmts P)) (σ : SemanticStore P)
    (t : AssertId P) : Prop :=
  ∃ evs e, BReach F ss σ (evs ++ [e]) ∧ Trace.AssumptionsHold P evalInterp () evs ∧
    FailsAt t e

end -- public section

end BigStep
end Imperative

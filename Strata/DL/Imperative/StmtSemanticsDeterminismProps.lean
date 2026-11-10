/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsDeterminism
import all Strata.DL.Imperative.StmtSemanticsDeterminism
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.Util.Relations

/-! # Properties of syntactic determinism and of the choice-free reference relation

Lemmas about the definitions of `StmtSemanticsDeterminism.lean`. Key theorems:
`StepStmtE.preserves_deterministic` and `StepStmtStarE.preserves_deterministic` (the reference
semantics preserves syntactic determinism), `StepStmtE.toStepDetE` and
`StepStmtStarE.toStepDetStarE` (from a deterministic configuration every step is a `StepDetE`
step), `StepDetE.toStepStmtE` and `StepDetStarE.toStepStmtStarE` (every `StepDetE` step or run
is a reference one), and `StepDetStarE.iff_stepStmtStarE` (the two relations agree there); the
`@[simp]` lemmas `Config.deterministic_ite_nondet`, `Config.deterministic_loop_nondet`,
`CmdDeterministic_init_nondet` and `CmdDeterministic_set_nondet` (nondeterministic constructs are
not deterministic), and `CmdDeterministic.det_rhs_of_init` / `CmdDeterministic.det_rhs_of_set`
(a deterministic `.init`/`.set` has a `.det` right-hand side). -/

namespace Imperative
public section
variable {P : PureExpr}

/-- A step of the event-trace reference semantics (`StepStmtE`) out of a configuration with no
    `.nondet` left to run (`Config.deterministic`) reaches another such configuration. -/
theorem StepStmtE.preserves_deterministic [HasBool P] [HasBoolOps P]
    {EventT : Type _} {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (hstep : StepStmtE P EvalCmd c ev c') :
    c.deterministic = true → c'.deterministic = true := by
  induction hstep <;> simp_all!

/-- A whole traced run out of a configuration with no `.nondet` left to run
(`Config.deterministic`) ends in such a configuration. -/
theorem StepStmtStarE.preserves_deterministic [HasBool P] [HasBoolOps P]
    {EventT : Type _} {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (hrun : StepStmtStarE P EvalCmd c ev c') :
    c.deterministic = true → c'.deterministic = true := by
  induction hrun <;> grind [StepStmtE.preserves_deterministic]

/-- A nondeterministic `ite` configuration is not deterministic. -/
@[simp] theorem Config.deterministic_ite_nondet
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P} :
    Config.deterministic (.stmt (.ite .nondet tss ess md) ρ) = false := rfl

/-- A nondeterministic `loop` configuration is not deterministic. -/
@[simp] theorem Config.deterministic_loop_nondet
    {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P} :
    Config.deterministic (.stmt (.loop .nondet m inv body md) ρ) = false := rfl

/-- A nondeterministic `.init` (the command `EvalCmdE.eval_init_unconstrained` evaluates) is not
    deterministic. -/
@[simp] theorem CmdDeterministic_init_nondet
    {x : P.Ident} {ty : P.Ty} {md : MetaData P} :
    CmdDeterministic (P := P) (.init x ty .nondet md) = false := rfl

/-- A nondeterministic `.set` (the command `EvalCmdE.eval_set_nondet` evaluates) is not
    deterministic. -/
@[simp] theorem CmdDeterministic_set_nondet
    {x : P.Ident} {md : MetaData P} :
    CmdDeterministic (P := P) (.set x .nondet md) = false := rfl

/-- On a deterministic base command an `.init` right-hand side is a `.det`
expression, so `EvalCmdE.eval_init_unconstrained` does not apply. -/
theorem CmdDeterministic.det_rhs_of_init
    {x : P.Ident} {ty : P.Ty} {rhs : ExprOrNondet P} {md : MetaData P}
    (h : CmdDeterministic (.init x ty rhs md) = true) :
    ∃ e, rhs = .det e := by cases rhs <;> simp_all

/-- On a deterministic base command a `.set` right-hand side is a `.det`
expression, so `EvalCmdE.eval_set_nondet` does not apply. -/
theorem CmdDeterministic.det_rhs_of_set
    {x : P.Ident} {rhs : ExprOrNondet P} {md : MetaData P}
    (h : CmdDeterministic (.set x rhs md) = true) :
    ∃ e, rhs = .det e := by cases rhs <;> simp_all

end
end Imperative

namespace Imperative
public section
variable {P : PureExpr}
section
variable (P : PureExpr) [HasBool P] [HasBoolOps P]
variable {P}

omit [HasBoolOps P] in
/-- Soundness: every step of the choice-free rules (`StepDetE`) is a step of the reference
    event-trace semantics (`StepStmtE`) with the same events. -/
theorem StepDetE.toStepStmtE {EventT : Type _}
    {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (h : StepDetE P EvalCmd c ev c') :
    StepStmtE P EvalCmd c ev c' := by induction h <;> grind [StepStmtE]

omit [HasBoolOps P] in
/-- **Completeness on deterministic configurations.**  Every step of the reference
event-trace semantics (`StepStmtE`) out of a configuration with no `.nondet` left to
run is a step of the choice-free rules (`StepDetE`): no nondeterministic rule fires,
and the base command it executes is deterministic. -/
theorem StepStmtE.toStepDetE {EventT : Type _}
    {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (h : StepStmtE P EvalCmd c ev c') :
    c.deterministic = true → StepDetE P EvalCmd c ev c' := by
  induction h <;>
    (try simp_all! only [Config.deterministic, StmtDeterministic, StmtsDeterministic,
      ExprOrNondet.isDet, Bool.false_and, Bool.true_and, Bool.false_eq_true, Bool.and_eq_true,
      false_implies, forall_const, and_imp, ne_eq]) <;>
    grind [StepDetE]

omit [HasBoolOps P] in
/-- Soundness of the closure: a run of the choice-free rules (`StepDetStarE`) is a
run of the reference event-trace semantics (`StepStmtStarE`) with the same trace. -/
theorem StepDetStarE.toStepStmtStarE {EventT : Type _}
    {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (h : StepDetStarE P EvalCmd c ev c') :
    StepStmtStarE P EvalCmd c ev c' := h.imp fun _ _ _ => (·.toStepStmtE)

/-- **Reference runs of deterministic configurations are choice-free.** A traced run of the
    reference event-trace semantics out of a configuration with no `.nondet` left to run uses only
    the choice-free rules (`StepDetStarE`), at every step and at every nesting depth, with the same
    trace. -/
theorem StepStmtStarE.toStepDetStarE {EventT : Type _}
    {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (h : StepStmtStarE P EvalCmd c ev c') :
    c.deterministic = true → StepDetStarE P EvalCmd c ev c' := by
  induction h <;> grind [ReflTransTrace, StepStmtE.toStepDetE, StepStmtE.preserves_deterministic]

/-- From a configuration with no `.nondet` left to run, the traced runs of the reference
    event-trace semantics (`StepStmtStarE`) are exactly those of the choice-free rules
    (`StepDetStarE`). -/
theorem StepDetStarE.iff_stepStmtStarE {EventT : Type _}
    {EvalCmd : EvalCmdParamE P (Cmd P) EventT}
    {c c' : Config P (Cmd P)} {ev : List EventT}
    (hd : c.deterministic = true) :
    StepDetStarE P EvalCmd c ev c' ↔
      StepStmtStarE P EvalCmd c ev c' := ⟨(·.toStepStmtStarE), (·.toStepDetStarE hd)⟩

end
end
end Imperative

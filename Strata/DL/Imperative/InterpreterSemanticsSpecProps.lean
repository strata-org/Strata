/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.StmtSemanticsDeterminism
public import Strata.DL.Imperative.StmtSemanticsDeterminismProps
public import Strata.DL.Imperative.InterpreterProps
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps

/-! # Properties of the monadic-interpreter↔semantics contract

Lemmas about the definitions of `InterpreterSemanticsSpec.lean`: the engine-realizable relations
against the reference semantics, the engine-check side condition, and the observation laws of
`InterpObs` applied to the engine.

Key theorems:
* `EngineChecksAgree.toFrom`: the global engine-check obligation implies the
  derivation-relative one;
* `engineChecksAgreeFrom_of_storeFree`: the derivation-relative obligation holds outright on
  configurations with no `.init` and no `.set`;
* `EvalCmdEngE.toEvalCmdE`, `StepEngE.toStepStmtE`, `StepEngStarE.toStepStmtStarE`: the
  engine-realizable relations are sub-relations of the reference semantics;
  `StepDetE.toStepEngE`: a choice-free reference step is engine-realizable, under the
  engine-check obligation; `StepEngParamE.not_done`: no engine-realizable step leaves a
  `.terminal` or `.exiting` configuration; `Calls.stepEngParamE_imp`: the engine-realizable step
  is monotone in its command relation;
* `StepStmtStarE.toStepEngStarEFrom`, `StepStmtStarE.toStepEngStarE`: a reference run from a
  deterministic configuration is engine-realizable, under the engine-check obligation;
* `StepStmtStarE.toStepEngParamStarE`: a reference run along which the engine agrees
  (`EngineAgreesFrom`) is engine-realizable; `engineAgreesFrom_of_deterministic` discharges the
  agreement on deterministic programs;
* `obs_run_zero`, `obs_run_succ`, `obs_runInterp_ok_final`, `obs_forM_emit`: `obs.run` of the
  driver at zero and successor fuel, the shape of a returned configuration, and the trace of
  emitting a list of events; `obs_run_throw_bind`: a throw before a bind leaves the state
  untouched;
* `obs_stepInterp_cmd_fwd`, `obs_ite_det_true_fwd`, `obs_ite_det_false_fwd`,
  `obs_loop_det_enter_fwd`, `obs_loop_det_exit_fwd`, `obs_seq_fwd`, `obs_block_fwd`: `obs.run` of
  one `stepInterp` step, forward, on a base command, a deterministic `ite` or `loop`, and an inner
  sequence or block step. -/

namespace Imperative
public section

/-! ## Engine-check agreement and the store-free fragment -/

section ChoiceSide
variable {P : PureExpr} [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- If every deterministic reference base-command evaluation passes the engine's value checks
    (`EngineChecksAgree R`), then so does the one in active position of any configuration `c`
    (`EngineChecksAgreeAt R c`). -/
private theorem EngineChecksAgree.toAt {R : ChoiceRecord P} (h : EngineChecksAgree (P := P) R)
    (c : Config P (Cmd P)) : EngineChecksAgreeAt (P := P) R c := fun _ _ _ _ _ => h _ _ _ _ _

omit [DecidableEq P.Expr] [HasBoolOps P] in
/-- If every deterministic reference base-command evaluation passes the engine's value checks
    (`EngineChecksAgree R`), then from any configuration `c` every configuration reachable by
    choice-free reference steps passes them at its active base command
    (`EngineChecksAgreeFrom R c`): the derivation-relative form never demands more
    than the global one. -/
theorem EngineChecksAgree.toFrom {R : ChoiceRecord P} (h : EngineChecksAgree (P := P) R)
    (c : Config P (Cmd P)) :
    EngineChecksAgreeFrom (P := P) R c := fun _ _ _ => h.toAt _

omit [DecidableEq P.Expr] [HasBoolOps P] in
/-- If the engine's value checks pass at every configuration reachable from `c` by choice-free
    reference steps, they pass at `c` itself (the empty derivation). -/
private theorem EngineChecksAgreeFrom.here {R : ChoiceRecord P}
    {c : Config P (Cmd P)} (h : EngineChecksAgreeFrom (P := P) R c) :
    EngineChecksAgreeAt (P := P) R c := h _ _ (.refl _)

omit [DecidableEq P.Expr] [HasBoolOps P] in
/-- If the engine's value checks pass at every configuration reachable from `c` by choice-free
    reference steps, the same holds from any `c'` one choice-free step after `c`, since what is
    reachable from `c'` is reachable from `c`. -/
private theorem EngineChecksAgreeFrom.step {R : ChoiceRecord P}
    {c c' : Config P (Cmd P)} {em : List (Event P)}
    (h : EngineChecksAgreeFrom (P := P) R c)
    (hs : StepDetE P (@EvalCmdE P _ _) c em c') :
    EngineChecksAgreeFrom (P := P) R c' := fun _ _ r => h _ _ (.step _ _ _ _ _ hs r)

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasBoolOps P] in
/-- The choice-free semantics preserves `Config.storeFree`. -/
private theorem StepDetE.preserves_storeFree
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (hstep : StepDetE P (@EvalCmdE P _ _) c evs c') :
    c.storeFree = true → c'.storeFree = true := by
  induction hstep <;> grind [Config.storeFree, StmtStoreFree, StmtsStoreFree]

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasBoolOps P] in
/-- A whole choice-free run out of a store-free configuration stays store-free. -/
private theorem StepDetStarE.preserves_storeFree
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (hrun : StepDetStarE P (@EvalCmdE P _ _) c evs c') :
    c.storeFree = true → c'.storeFree = true := by
  induction hrun <;> grind [StepDetE.preserves_storeFree]

omit [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] in
/-- The command in active position of a store-free configuration is store-free. -/
private theorem CmdFocus.storeFree_cmd {c : Config P (Cmd P)} {ρ : Env P} {cmd : Cmd P}
    (hfoc : CmdFocus (P := P) c ρ cmd) (h : c.storeFree = true) :
    CmdStoreFree (P := P) cmd = true := by
  induction hfoc <;> grind [Config.storeFree, StmtStoreFree]

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- At a configuration `c` with no `.init` and no `.set` left to execute, every deterministic
    reference evaluation of its active base command passes the engine's value checks
    (`EngineChecksAgreeAt R c`), for every choice record `R`. -/
private theorem engineChecksAgreeAt_of_storeFree (R : ChoiceRecord P) {c : Config P (Cmd P)}
    (h : c.storeFree = true) : EngineChecksAgreeAt (P := P) R c := fun _ _ _ _ hfoc hev => by
  have hsf := hfoc.storeFree_cmd h
  cases hev <;> intro _ <;> first
    | exact .eval_assert | exact .eval_assume | exact .eval_cover
    | (exact absurd hsf (by simp [CmdStoreFree]))

omit [DecidableEq P.Expr] [HasBoolOps P] in
/-- **The derivation-relative engine-check agreement on the store-free fragment.** From a
    configuration whose remaining program text contains no `.init` and no `.set`, every
    configuration reachable by choice-free reference steps passes the engine's value checks at its
    active base command (`EngineChecksAgreeFrom R`), for every choice record `R`. -/
theorem engineChecksAgreeFrom_of_storeFree (R : ChoiceRecord P)
    {c : Config P (Cmd P)} (h : c.storeFree = true) :
    EngineChecksAgreeFrom (P := P) R c :=
  fun _ _ r => engineChecksAgreeAt_of_storeFree R (r.preserves_storeFree h)

end ChoiceSide
end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
public section

/-! ## Soundness of the engine-realizable relations -/

section EngRel
variable (P : PureExpr) [HasBool P] [HasFvar P] [DecidableEq P.Ident] [InterpLang P]
variable {P}

/-- The refinement is sound: an `EvalCmdEngE` evaluation is a reference
`EvalCmdE` evaluation with the same store and the same events. -/
theorem EvalCmdEngE.toEvalCmdE {R : ChoiceRecord P}
    {f : P.Factory} {σ σ' : SemanticStore P} {cmd : Cmd P} {evs : Trace P}
    (h : EvalCmdEngE P R f σ cmd σ' evs) : EvalCmdE (P := P) f σ cmd σ' evs := by
  cases h <;> constructor <;> apply_rules [InitState.of_update, UpdateState.of_update]

/-- The engine-realizable command relation is monotone in its choice record. -/
theorem EvalCmdEngE.mono {R R' : ChoiceRecord P} (hR : ∀ f σ ty v, R f σ ty v → R' f σ ty v)
    {f : P.Factory} {σ σ' : SemanticStore P} {cmd : Cmd P} {evs : Trace P}
    (h : EvalCmdEngE P R f σ cmd σ' evs) : EvalCmdEngE P R' f σ cmd σ' evs := by
  cases h <;> constructor <;> first | assumption | exact hR _ _ _ _ ‹_›

end EngRel
end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
public section
section StepEng
variable (P : PureExpr) [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]
variable {P}

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- Soundness of the refinement at statement level: an engine-realizable step is a
reference `StepStmtE` step with the same events and the same successor. -/
theorem StepEngParamE.toStepStmtE {CmdT : Type} {R : ChoiceRecord P}
    {EvalCmdEng EvalCmd : EvalCmdParamE P CmdT (Event P)}
    (hcmd : ∀ f σ σ' cmd evs, EvalCmdEng f σ cmd σ' evs → EvalCmd f σ cmd σ' evs)
    {c c' : Config P CmdT} {evs : List (Event P)}
    (h : StepEngParamE P R EvalCmdEng c evs c') :
    StepStmtE P EvalCmd c evs c' := by
  induction h with
  | step_cmd h => exact .step_cmd (hcmd _ _ _ _ _ h)
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_block_body _ ih => exact .step_block_body ih
  | step_ite_nondet => split <;> constructor
  | step_loop_nondet => split <;> constructor
  | _ => constructor <;> assumption

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- Every engine-realizable step over base commands (`StepEngE`) is a reference `StepStmtE` step
    over `EvalCmdE` with the same events and the same successor. -/
theorem StepEngE.toStepStmtE {R : ChoiceRecord P}
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepEngE P R c evs c') :
    StepStmtE P (@EvalCmdE P _ _) c evs c' :=
  StepEngParamE.toStepStmtE (fun _ _ _ _ _ h => EvalCmdEngE.toEvalCmdE h) h

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- Every engine-realizable run over base commands (`StepEngStarE`) is a reference `StepStmtStarE`
    run over `EvalCmdE` with the same events and the same final configuration. -/
theorem StepEngStarE.toStepStmtStarE {R : ChoiceRecord P}
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepEngStarE P R c evs c') :
    StepStmtStarE P (@EvalCmdE P _ _) c evs c' :=
  h.imp fun _ _ _ => StepEngE.toStepStmtE

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- No engine-realizable step leaves a `.terminal` or `.exiting` configuration, so
the driver's stopping test is exactly the absence of a next step. -/
theorem StepEngParamE.not_done {CmdT : Type} {R : ChoiceRecord P}
    {EvalCmd : EvalCmdParamE P CmdT (Event P)}
    {c c' : Config P CmdT} {evs : List (Event P)}
    (h : StepEngParamE P R EvalCmd c evs c') :
    (∀ e, c ≠ .terminal e) ∧ (∀ l e, c ≠ .exiting l e) := by cases h <;> simp

end StepEng

namespace Calls
variable {P : PureExpr} [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- The engine-realizable statement step is monotone in its command relation. -/
theorem stepEngParamE_imp {CmdT : Type} {R : ChoiceRecord P}
    {E E' : EvalCmdParamE P CmdT (Event P)}
    (h : ∀ f σ c σ' evs, E f σ c σ' evs → E' f σ c σ' evs) :
    ∀ {c evs c'}, StepEngParamE P R E c evs c' → StepEngParamE P R E' c evs c' :=
  fun h => by induction h <;> constructor <;> grind

end Calls
end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
public section

/-! ## Choice-free reference runs are engine-realizable -/

section Bridge
variable {P : PureExpr} [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]

omit [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- A bounded evaluator that reaches every reference value at some fuel (`BoundedEvalComplete`)
    reaches the reference value of every expression on every store (`EngEvalReach`). -/
theorem BoundedEvalComplete.reach (h : BoundedEvalComplete P) {f : P.Factory}
    {σ : SemanticStore P} {e : P.Expr} : EngEvalReach P f σ e :=
  fun σr v hσ he => h f σr σ e v hσ he

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- A choice-free reference step is engine-realizable, given engine-check agreement at its
    configuration, a bounded evaluator that reaches every reference value, and guard agreement. -/
private theorem StepDetE.toStepEngEAt {R : ChoiceRecord P} (hEvalComplete : BoundedEvalComplete P)
    (hg : EngineGuardsAgree P)
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepDetE P (@EvalCmdE P _ _) c evs c') :
    EngineChecksAgreeAt (P := P) R c → StepEngE P R c evs c' := by
  induction h <;> intro hc
  case step_seq_inner ih => exact .step_seq_inner (ih fun _ _ _ _ hf => hc _ _ _ _ (.seq hf))
  case step_block_body ih => exact .step_block_body (ih fun _ _ _ _ hf => hc _ _ _ _ (.block hf))
  case step_cmd hd he => exact .step_cmd (hc _ _ _ _ .here he hd)
  all_goals first
    | (constructor; done)
    | (constructor <;> first
        | assumption
        | exact ⟨hEvalComplete.reach, (hg _ _ _).1 ‹_›⟩
        | exact ⟨hEvalComplete.reach, (hg _ _ _).2 ‹_›⟩)

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- A choice-free reference run is engine-realizable, given engine-check agreement along
    derivations from its start, a bounded evaluator that reaches every reference value, and guard
    agreement. -/
private theorem StepDetStarE.toStepEngStarEFrom {R : ChoiceRecord P}
    (hEvalComplete : BoundedEvalComplete P) (hg : EngineGuardsAgree P)
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepDetStarE P (@EvalCmdE P _ _) c evs c') :
    EngineChecksAgreeFrom (P := P) R c →
      StepEngStarE P R c evs c' :=
  h.rec (fun _ _ => .refl _) fun _ _ _ _ _ s _ ih hc =>
    .step _ _ _ _ _ (s.toStepEngEAt hEvalComplete hg hc.here) (ih (hc.step s))

omit [DecidableEq P.Expr] in
/-- A reference run from a deterministic configuration is an engine-realizable run with the same
    events, provided every configuration reachable from its start by choice-free reference steps
    passes the engine's value checks at its active base command (`EngineChecksAgreeFrom`), the
    bounded evaluator reaches every reference value (`BoundedEvalComplete`) and runtime guard
    values agree with the reference ones (`EngineGuardsAgree`). -/
theorem StepStmtStarE.toStepEngStarEFrom {R : ChoiceRecord P}
    (hEvalComplete : BoundedEvalComplete P) (hg : EngineGuardsAgree P)
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepStmtStarE P (@EvalCmdE P _ _) c evs c')
    (hdet : c.deterministic = true)
    (hchk : EngineChecksAgreeFrom (P := P) R c) :
    StepEngStarE P R c evs c' := (h.toStepDetStarE hdet).toStepEngStarEFrom hEvalComplete hg hchk

omit [HasBoolOps P] [DecidableEq P.Expr] in
/-- A choice-free reference step is an engine-realizable step, provided every deterministic
    reference base-command evaluation passes the engine's value checks (`EngineChecksAgree`), the
    bounded evaluator reaches every reference value (`BoundedEvalComplete`) and runtime guard
    values agree with the reference ones (`EngineGuardsAgree`). -/
theorem StepDetE.toStepEngE {R : ChoiceRecord P}
    (hEvalComplete : BoundedEvalComplete P) (hg : EngineGuardsAgree P)
    (hchk : EngineChecksAgree (P := P) R)
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepDetE P (@EvalCmdE P _ _) c evs c') :
    StepEngE P R c evs c' := h.toStepEngEAt hEvalComplete hg (hchk.toAt _)

omit [DecidableEq P.Expr] in
/-- **Reference run on a deterministic program ⇒ engine-realizable run**: a reference run from a
    deterministic configuration is an engine-realizable run with the same events, provided every
    deterministic reference base-command evaluation passes the engine's value checks
    (`EngineChecksAgree`), the bounded evaluator reaches every reference value
    (`BoundedEvalComplete`) and runtime guard values agree with the reference ones
    (`EngineGuardsAgree`). -/
theorem StepStmtStarE.toStepEngStarE {R : ChoiceRecord P}
    (hEvalComplete : BoundedEvalComplete P) (hg : EngineGuardsAgree P)
    (hchk : EngineChecksAgree (P := P) R)
    {c c' : Config P (Cmd P)} {evs : List (Event P)}
    (h : StepStmtStarE P (@EvalCmdE P _ _) c evs c')
    (hdet : c.deterministic = true) :
    StepEngStarE P R c evs c' := h.toStepEngStarEFrom hEvalComplete hg hdet (hchk.toFrom _)

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- If every reference step out of a configuration reachable from `c` is also an
    engine-realizable step (`EngineAgreesFrom`), then every reference run from `c` is an
    engine-realizable run with the same events. -/
theorem StepStmtStarE.toStepEngParamStarE {CmdT : Type} {R : ChoiceRecord P}
    {EvalCmd EvalCmdEng : EvalCmdParamE P CmdT (Event P)}
    {c c' : Config P CmdT} {evs : List (Event P)} (h : StepStmtStarE P EvalCmd c evs c')
    (hag : EngineAgreesFrom (P := P) R EvalCmd EvalCmdEng c) :
    StepEngParamStarE P R EvalCmdEng c evs c' := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hs _ ih =>
    exact .step _ _ _ _ _ (hag _ _ _ _ (.refl _) hs)
      (ih fun _ _ _ _ r => hag _ _ _ _ (.step _ _ _ _ _ hs r))

omit [DecidableEq P.Expr] in
/-- On a deterministic program `c`, if every configuration reachable by choice-free reference
    steps passes the engine's value checks at its active base command (`EngineChecksAgreeFrom`),
    then every reference step out of a configuration reachable from `c` is an engine-realizable
    step (`EngineAgreesFrom`), for every choice record, when the bounded evaluator reaches every
    reference value (`BoundedEvalComplete`) and runtime guard values agree with the reference ones
    (`EngineGuardsAgree`). -/
theorem engineAgreesFrom_of_deterministic {R : ChoiceRecord P}
    (hEvalComplete : BoundedEvalComplete P) (hg : EngineGuardsAgree P)
    {c : Config P (Cmd P)} (hdet : c.deterministic = true)
    (hchk : EngineChecksAgreeFrom (P := P) R c) :
    EngineAgreesFrom (P := P) R (@EvalCmdE P _ _) (EvalCmdEngE P R) c :=
  fun _ _ _ _ hr hs => (hs.toStepDetE (hr.preserves_deterministic hdet)).toStepEngEAt
    hEvalComplete hg (hchk _ _ (hr.toStepDetStarE hdet))

end Bridge
end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
public section

/-! ## One engine step, forward

Each statement form's `stepInterp` step computed under `obs.run`, from the reference step's
premises. -/

section Complete
variable {P : PureExpr} {m : Type → Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- If `stepBaseCmdStore` runs a base command `cmd` from `ρ`'s store to `σ'`, then
    `stepInterp baseStepCmd` on `.stmt (.cmd cmd) ρ` runs to `.terminal { ρ with store := σ' }`,
    with the same final state. -/
theorem obs_stepInterp_cmd_fwd (obs : InterpObs P m) (fuel : Nat) (ρ : IEnv P) (cmd : Cmd P)
    (σ' : IStore P) (cfgr : obs.Cfg) (st st' : obs.St)
    (h : obs.run (stepBaseCmdStore (m := m) fuel ρ.factory ρ.store cmd) cfgr st = (.ok σ', st')) :
    obs.run (stepInterp (baseStepCmd (m := m)) fuel (.stmt (.cmd cmd) ρ)) cfgr st
      = (.ok (.terminal { ρ with store := σ' }), st') := by simp [baseStepCmd, h]

end Complete
end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
public section
section Complete
variable {P : PureExpr} {m : Type → Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]
section FwdControl
variable {CmdT : Type} [CmdDefs P CmdT]

omit [HasBoolOps P] [HasFvar P] in
/-- On a deterministic `ite` whose guard the bounded evaluator reduces to `tt`, `stepInterp` returns
    the then-branch block, leaving the state unchanged. -/
theorem obs_ite_det_true_fwd (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (c : P.Expr) (tss ess : List (Stmt P CmdT)) (md : MetaData P) (env : IEnv P)
    (cfgr : obs.Cfg) (st : obs.St)
    {v : P.Expr} (hb : InterpLang.boundedEval (P := P) fuel env.factory env.store.get c = some v)
    (hv : InterpLang.boolLit? v = some true) :
    obs.run (stepInterp stepCmd fuel (.stmt (.ite (.det c) tss ess md) env)) cfgr st
      = (.ok (.block .none (.opened env.store) (.stmts tss env)), st) := by
  simp [*, stepInterp, resolveGuard]

omit [HasBoolOps P] [HasFvar P] in
/-- On a deterministic `ite` whose guard the bounded evaluator reduces to `ff`, `stepInterp` returns
    the else-branch block, leaving the state unchanged. -/
theorem obs_ite_det_false_fwd (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (c : P.Expr) (tss ess : List (Stmt P CmdT)) (md : MetaData P) (env : IEnv P)
    (cfgr : obs.Cfg) (st : obs.St)
    {v : P.Expr} (hb : InterpLang.boundedEval (P := P) fuel env.factory env.store.get c = some v)
    (hv : InterpLang.boolLit? v = some false) :
    obs.run (stepInterp stepCmd fuel (.stmt (.ite (.det c) tss ess md) env)) cfgr st
      = (.ok (.block .none (.opened env.store) (.stmts ess env)), st) := by
  simp [stepInterp, *, resolveGuard]

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- On a deterministic `loop` whose guard the bounded evaluator reduces to `tt`, `stepInterp`
    returns the body block followed by the loop again, leaving the state unchanged. -/
theorem obs_loop_det_enter_fwd (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (g : P.Expr) (measure : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P CmdT)) (md : MetaData P) (env : IEnv P)
    (cfgr : obs.Cfg) (st : obs.St)
    {v : P.Expr} (hb : InterpLang.boundedEval (P := P) fuel env.factory env.store.get g = some v)
    (hv : InterpLang.boolLit? v = some true) :
    obs.run (stepInterp stepCmd fuel (.stmt (.loop (.det g) measure inv body md) env)) cfgr st
      = (.ok (.seq (.block .none (.opened env.store) (.stmts body env))
          [.loop (.det g) measure inv body md]), st) := by simp [*, stepInterp, resolveGuard]

omit [LawfulMonad m] [HasBoolOps P] [HasFvar P] in
/-- On a deterministic `loop` whose guard the bounded evaluator reduces to `ff`, `stepInterp`
    terminates with the current environment, leaving the state unchanged. -/
theorem obs_loop_det_exit_fwd (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (g : P.Expr) (measure : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P CmdT)) (md : MetaData P) (env : IEnv P)
    (cfgr : obs.Cfg) (st : obs.St)
    {v : P.Expr} (hb : InterpLang.boundedEval (P := P) fuel env.factory env.store.get g = some v)
    (hv : InterpLang.boolLit? v = some false) :
    obs.run (stepInterp stepCmd fuel (.stmt (.loop (.det g) measure inv body md) env)) cfgr st
      = (.ok (.terminal env), st) := by simp [stepInterp, *, resolveGuard]

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- If `stepInterp` steps a non-terminal, non-exiting configuration `inner` to `inner'`, it steps
    `.seq inner ss` to `.seq inner' ss`, with the same final state. -/
theorem obs_seq_fwd (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (inner inner' : IConfig P CmdT) (ss : List (Stmt P CmdT)) (cfgr : obs.Cfg) (st st' : obs.St)
    (hnt : ∀ e, inner ≠ IConfig.terminal e) (hex : ∀ l e, inner ≠ IConfig.exiting l e)
    (h : obs.run (stepInterp stepCmd fuel inner) cfgr st = (.ok inner', st')) :
    obs.run (stepInterp stepCmd fuel (.seq inner ss)) cfgr st = (.ok (.seq inner' ss), st') := by
  simp [stepInterp_seq_unfold_gen _ _ _ _ hnt hex, h]

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- If `stepInterp` steps a non-terminal, non-exiting configuration `inner` to `inner'`, it steps
    `.block label frame inner` to `.block label (frame.record inner.levelCmd?) inner'`, with the
    same final state. -/
theorem obs_block_fwd (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (label : Option String) (frame : ScopeFrame P)
    (inner inner' : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St)
    (hnt : ∀ e, inner ≠ IConfig.terminal e) (hex : ∀ l e, inner ≠ IConfig.exiting l e)
    (h : obs.run (stepInterp stepCmd fuel inner) cfgr st = (.ok inner', st')) :
    obs.run (stepInterp stepCmd fuel (.block label frame inner)) cfgr st
      = (.ok (.block label (frame.record inner.levelCmd?) inner'), st') := by
  simp [stepInterp_block_unfold_gen, *]

end FwdControl
end Complete
end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
open Imperative
public section
variable {P : PureExpr} {CmdT : Type}
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-! ## The driver under `obs.run` -/

/-- At fuel `0`, `runInterp` on a non-terminal, non-exiting configuration runs to the
    fuel-exhaustion error with the state unchanged. -/
theorem obs_run_zero (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m)
    (cfg : IConfig P CmdT) (cfgr : obs.Cfg) (st : obs.St)
    (hnt : ∀ e, cfg ≠ .terminal e) (hex : ∀ l e, cfg ≠ .exiting l e) :
    obs.run (runInterp stepCmd 0 cfg) cfgr st = (.error .replayFuelExhausted, st) := by
  cases cfg <;> simp_all!

/-- At successor fuel, `runInterp` on a non-terminal, non-exiting configuration runs one
    `stepInterp` step, then continues from the resulting configuration and state, stopping at
    the first error. -/
theorem obs_run_succ (obs : InterpObs P m) (stepCmd : StepCmdM P CmdT m)
    (fuel : Nat) (cfg : IConfig P CmdT) (cfgr : obs.Cfg) (st : obs.St)
    (hnt : ∀ e, cfg ≠ .terminal e) (hex : ∀ l e, cfg ≠ .exiting l e) :
    obs.run (runInterp stepCmd (fuel + 1) cfg) cfgr st
      = (match obs.run (stepInterp stepCmd (fuel + 1) cfg) cfgr st with
         | (.ok next, s) => obs.run (runInterp stepCmd fuel next) cfgr s
         | (.error e, s) => (.error e, s)) := by grind [runInterp_succ_nonterminal]

end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
open Imperative
public section
variable {P : PureExpr} {CmdT : Type}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident]

omit [HasBoolOps P] [HasFvar P] in
/-- A run that returned `.ok` stopped at a terminal or an exiting configuration:
    those are the only two shapes `runInterp` hands back without throwing. -/
theorem obs_runInterp_ok_final (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) :
    ∀ (fuel : Nat) (cfg cfg' : IConfig P CmdT) (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (runInterp stepCmd fuel cfg) cfgr st = (.ok cfg', st') →
      (∃ e, cfg' = .terminal e) ∨ (∃ l e, cfg' = .exiting l e) := by
  intro F c _ _ s _ h
  fun_induction runInterp stepCmd F c generalizing s <;> grind

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] in
/-- Emitting a list of events prepends exactly that list to the trace. -/
theorem obs_forM_emit (obs : InterpObs P m) (cfgr : obs.Cfg) :
    ∀ (evs : List (IEvent P)) (st st' : obs.St) (u : Unit),
      obs.run (evs.forM (InterpEffects.emit (P := P))) cfgr st = (.ok u, st') →
      obs.trace st' = evs.reverse ++ obs.trace st := fun evs => by
  induction evs with
  | nil => simp_all
  | cons =>
    simp_all only [List.forM_eq_forM, List.forM_cons, InterpObs.run_bind, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append]
    grind

end
end Imperative

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp
open Imperative
public section
variable {P : PureExpr} {CmdT : Type}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident]
section StepGeneric
variable {P : PureExpr} {m : Type → Type} {CmdT : Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident] [LawfulMonad m] in
/-- A computation that throws before a bind runs to the error with the state untouched. -/
theorem obs_run_throw_bind {α β : Type} (obs : InterpObs P m) (r : StopReason)
    (f : α → m β) (cfgr : obs.Cfg) (st : obs.St) :
    obs.run (throw r >>= f) cfgr st = (.error r, st) := by rw [obs.run_bind, obs.run_throw]

end StepGeneric
end
end Imperative

namespace Imperative
public section

/-- `BoundedEvalSound` is `BoundedEvalSoundAt` at every factory. -/
theorem boundedEvalSound_iff_at {P : PureExpr} [InterpLang P] :
    BoundedEvalSound P ↔ ∀ f, BoundedEvalSoundAt P f :=
  ⟨fun h f n σr σ e r => h n f σr σ e r, fun h n f σr σ e r => h f n σr σ e r⟩

end
end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreSpecification
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.RelationsProps
import all Strata.Languages.Core.Procedure
import all Strata.Util.ListMap

/-! # Core specification properties

Supporting results for `CoreSpecification`: projections of the typed
procedure-entry environment, and the embedding of failure-flag runs into event
runs.

Every failure-flag run of a Core statement embeds into an event run through the
same configurations. The two semantics differ in how they record an assertion:
the failure-flag run evaluates it and raises `hasFailure` when it is false, while
the event run emits it and leaves the flag alone. So the event run reaches each
configuration with its failure flag reset to a fixed value, and its trace records
that every assumption evaluated to true, since a false one blocks a failure-flag
run.

## Key results

- `mem_procVerifyInitIdents_of_input`, `mem_procVerifyInitIdents_of_output`, and
  `mem_procVerifyInitIdents_of_oldInout` identify required procedure-entry slots.
- `ProcEnvWF.storeDefined`, `ProcEnvWF.inputTyped`, `ProcEnvWF.outputTyped`, and
  `ProcEnvWF.oldInoutTyped` project definedness and typed values from `ProcEnvWF`.
- `ProcEnvWF.of_sameSignature` — an entry environment carries over to a
  procedure with the same header and specification.
- `coreStepStar_toEvent` — the embedding of failure-flag runs, together with
  `evalCommand_toEvent` for single commands, including calls.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ### Convenient projections of `ProcEnvWF.storeDefinedAndWellTyped` -/

/-- An input parameter (with its declared type) is one of the variables that
    must be initialized before the body runs. -/
theorem mem_procVerifyInitIdents_of_input {proc : Procedure}
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (h : (id, ty) ∈ proc.header.inputs.toList) :
    (id, ty) ∈ procVerifyInitIdents proc := by
  unfold procVerifyInitIdents
  exact List.mem_append_left _ (List.mem_append_left _ h)

/-- An output parameter (with its declared type) is one of the variables that
    must be initialized before the body runs. -/
theorem mem_procVerifyInitIdents_of_output {proc : Procedure}
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (h : (id, ty) ∈ proc.header.outputs.toList) :
    (id, ty) ∈ procVerifyInitIdents proc := by
  unfold procVerifyInitIdents
  exact List.mem_append_left _ (List.mem_append_right _ h)

/-- The old snapshot of an in-out parameter (with the parameter's original
    type) is one of the variables that must be initialized before the body
    runs. -/
theorem mem_procVerifyInitIdents_of_oldInout {proc : Procedure}
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (h : (id, ty) ∈ proc.header.getInoutParams.toList) :
    (CoreIdent.mkOld id.name, ty) ∈ procVerifyInitIdents proc := by
  unfold procVerifyInitIdents
  exact List.mem_append_right _ (List.mem_map_of_mem h)

/-- Definedness projection: every variable that must be initialized holds
    *some* value. -/
theorem ProcEnvWF.storeDefined {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ procVerifyInitIdents proc) :
    (ρ.store id).isSome := by
  obtain ⟨v, hv, _⟩ := h.storeDefinedAndWellTyped id ty hm
  rw [hv]; rfl

/-- Typed-value projection for input parameters. -/
theorem ProcEnvWF.inputTyped {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ proc.header.inputs.toList) :
    ∃ v, ρ.store id = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty) :=
  h.storeDefinedAndWellTyped id ty (mem_procVerifyInitIdents_of_input hm)

/-- Typed-value projection for output parameters. -/
theorem ProcEnvWF.outputTyped {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ proc.header.outputs.toList) :
    ∃ v, ρ.store id = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty) :=
  h.storeDefinedAndWellTyped id ty (mem_procVerifyInitIdents_of_output hm)

/-- Typed-value projection for the old snapshots of in-out parameters. -/
theorem ProcEnvWF.oldInoutTyped {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ proc.header.getInoutParams.toList) :
    ∃ v, ρ.store (CoreIdent.mkOld id.name) = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty) :=
  h.storeDefinedAndWellTyped (CoreIdent.mkOld id.name) ty
    (mem_procVerifyInitIdents_of_oldInout hm)


/-- `ProcEnvWF` reads only a procedure's header, its specification and the
    well-formedness of its body. So an entry environment of `proc` is one of any
    `proc'` with the same header and specification whose body is well formed
    from it. -/
theorem ProcEnvWF.of_sameSignature {params : InitEnvWFParams} {proc proc' : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    (h_header : proc'.header = proc.header) (h_spec : proc'.spec = proc.spec)
    (h_structured : ∀ ss, proc'.body = .structured ss →
      BlockInitEnvWF params [Stmt.block "" ss #[]] ρ)
    (h_cfg : ∀ cfg, proc'.body = .cfg cfg → CFGInitEnvWF params cfg ρ) :
    ProcEnvWF params proc' ρ where
  toWellFormedSemanticEval := h.toWellFormedSemanticEval
  storeValues := h.storeValues
  storeDefinedAndWellTyped id ty hm := by
    rw [procVerifyInitIdents, h_header] at hm
    exact h.storeDefinedAndWellTyped id ty hm
  oldInoutMatchesInout := by rw [h_header]; exact h.oldInoutMatchesInout
  preconditionsHold := by rw [h_spec]; exact h.preconditionsHold
  noFailure := h.noFailure
  structuredBodyWF := h_structured
  cfgBodyWF := h_cfg

/-! ## What an event trace records about a failure-flag run -/

/-- The trace `tr` of an event run is faithful to a failure-flag run: every
    assumption in `tr` evaluates to true, as it must for the failure-flag run to
    have passed it. -/
structure FaithfulTrace (tr : Trace Expression) : Prop where
  assumes : ∀ e, Event.assume e ∈ tr →
    Expression.eval e.factory e.store e.expr = some HasBool.tt

namespace FaithfulTrace

/-- An empty trace is faithful. -/
private theorem nil : FaithfulTrace [] := ⟨by simp⟩

/-- Faithful traces compose. -/
private theorem append {tr₁ tr₂ : Trace Expression}
    (h₁ : FaithfulTrace tr₁) (h₂ : FaithfulTrace tr₂) : FaithfulTrace (tr₁ ++ tr₂) where
  assumes e he := by
    rcases List.mem_append.mp he with he | he
    · exact h₁.assumes e he
    · exact h₂.assumes e he

end FaithfulTrace

/-! ## Commands and contract checks -/

/-- A base command's emitted events are faithful to its failure-flag
    execution. -/
private theorem evalCmd_faithful {f : Expression.Factory} {σ σ' : CoreStore}
    {c : Imperative.Cmd Expression} {failed : Bool}
    (h : Imperative.EvalCmd Expression f σ c σ' failed) :
    FaithfulTrace (Cmd.emittedEvents Expression c f σ) := by
  cases h with
  | eval_init => exact FaithfulTrace.nil
  | eval_init_unconstrained => exact FaithfulTrace.nil
  | eval_set => exact FaithfulTrace.nil
  | eval_set_nondet => exact FaithfulTrace.nil
  | eval_assert_pass => exact ⟨by simp [Cmd.emittedEvents]⟩
  | eval_assert_fail => exact ⟨by simp [Cmd.emittedEvents]⟩
  | eval_assume htt => exact ⟨by simpa [Cmd.emittedEvents] using htt⟩
  | eval_cover => exact ⟨by simp [Cmd.emittedEvents]⟩

/-- The assertion events a call emits for its non-free contract clauses are
    faithful to the failure-flag check of the same clauses. -/
private theorem evalChecks_faithful {fac : Expression.Factory} {σ : CoreStore}
    (cs : ListMap CoreLabel Procedure.Check) {failed : Bool}
    (h : EvalChecks fac σ (Procedure.Spec.getDefaultCheckExprs cs) failed) :
    FaithfulTrace (defaultAssertEvents fac σ cs) := by
  induction cs generalizing failed with
  | nil =>
    have hnil : Procedure.Spec.getDefaultCheckExprs
        ([] : ListMap CoreLabel Procedure.Check) = [] := rfl
    rw [hnil] at h
    cases h
    exact FaithfulTrace.nil
  | cons hd rest ih =>
    obtain ⟨label, check⟩ := hd
    by_cases hattr : check.attr = .Default
    · have hevents : defaultAssertEvents fac σ ((label, check) :: rest) =
          Event.assert ⟨fac, σ, label, check.expr, check.md⟩ ::
            defaultAssertEvents fac σ rest := by
        simp [defaultAssertEvents, Imperative.Calls.defaultAssertEvents, ListMap.toList, hattr]
      have hexprs : Procedure.Spec.getDefaultCheckExprs ((label, check) :: rest) =
          check.expr :: Procedure.Spec.getDefaultCheckExprs rest := by
        simp [Procedure.Spec.getDefaultCheckExprs, ListMap.values, hattr]
      rw [hexprs] at h
      rw [hevents]
      have hrest : ∃ failed', EvalChecks fac σ (Procedure.Spec.getDefaultCheckExprs rest) failed' := by
        cases h with
        | eval_pass _ _ hrest => exact ⟨_, hrest⟩
        | eval_fail _ _ hrest => exact ⟨_, hrest⟩
      obtain ⟨_, hrest⟩ := hrest
      exact ⟨fun e he => by
        simp only [List.mem_cons, reduceCtorEq, false_or] at he
        exact (ih hrest).assumes e he⟩
    · have hevents : defaultAssertEvents fac σ ((label, check) :: rest) =
          defaultAssertEvents fac σ rest := by
        simp [defaultAssertEvents, Imperative.Calls.defaultAssertEvents, ListMap.toList, hattr]
      have hexprs : Procedure.Spec.getDefaultCheckExprs ((label, check) :: rest) =
          Procedure.Spec.getDefaultCheckExprs rest := by
        simp [Procedure.Spec.getDefaultCheckExprs, ListMap.values, hattr]
      rw [hexprs] at h
      rw [hevents]
      exact ih h

/-! ## Administrative steps -/

/-- Administrative steps do not inspect the failure flag. -/
private theorem adminStep_withFailure
    {c c' : CoreConfig} (b : Bool)
    (h : StepStmt Expression (noCommandEvalE Expression Command) c c') :
    StepStmt Expression (noCommandEvalE Expression Command)
      (c.withFailure b) (c'.withFailure b) := by
  induction h with
  | step_cmd hcmd => exact hcmd.elim
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_block_body _ ih => exact .step_block_body ih
  | step_ite_true heval => exact .step_ite_true heval
  | step_ite_false heval => exact .step_ite_false heval
  | step_loop_enter heval => exact .step_loop_enter heval
  | step_loop_exit heval => exact .step_loop_exit heval
  | step_block_exit_match hlabel => exact .step_block_exit_match hlabel
  | step_block_exit_mismatch hlabel => exact .step_block_exit_mismatch hlabel
  | _ => constructor

/-- An administrative step is an event step with an empty, faithful trace. -/
private theorem adminStep_toEvent {π : String → Option Procedure}
    {c c' : CoreConfig} (b : Bool)
    (h : StepStmt Expression (noCommandEvalE Expression Command) c c') :
    ∃ tr, CoreStepE π (c.withFailure b) tr (c'.withFailure b) ∧ FaithfulTrace tr :=
  ⟨[], .step_admin (adminStep_withFailure b h), FaithfulTrace.nil⟩

/-! ## Embedding failure-flag runs into event runs -/

variable {π : String → Option Procedure}

mutual

/-- A failure-flag run is an event run through the same configurations, with
    the failure flag held at `b`, and its trace is faithful to the run. -/
theorem coreStepStar_toEvent {c c' : CoreConfig} (h : CoreStepStar π c c') (b : Bool) :
    ∃ tr, CoreStepStarE π (c.withFailure b) tr (c'.withFailure b) ∧ FaithfulTrace tr :=
  match h with
  | .refl => ⟨[], .refl _, FaithfulTrace.nil⟩
  | .step hstep hrest =>
    match stepStmt_toEvent hstep b, coreStepStar_toEvent hrest b with
    | ⟨tr₁, h₁, f₁⟩, ⟨tr₂, h₂, f₂⟩ => ⟨tr₁ ++ tr₂, .step _ _ _ _ _ h₁ h₂, f₁.append f₂⟩

/-- One failure-flag statement step as one event step. -/
private theorem stepStmt_toEvent {c c' : CoreConfig}
    (h : StepStmt Expression (EvalCommand π) c c') (b : Bool) :
    ∃ tr, CoreStepE π (c.withFailure b) tr (c'.withFailure b) ∧ FaithfulTrace tr :=
  match h with
  | .step_cmd hcmd =>
    match evalCommand_toEvent hcmd with
    | ⟨tr, hE, hf⟩ => ⟨tr, .step_cmd hE, hf⟩
  | .step_seq_inner hinner =>
    match stepStmt_toEvent hinner b with
    | ⟨tr, hE, hf⟩ => ⟨tr, .step_seq_inner hE, hf⟩
  | .step_block_body hinner =>
    match stepStmt_toEvent hinner b with
    | ⟨tr, hE, hf⟩ => ⟨tr, .step_block_body hE, hf⟩
  | .step_block => adminStep_toEvent b .step_block
  | .step_ite_true heval => adminStep_toEvent b (.step_ite_true heval)
  | .step_ite_false heval => adminStep_toEvent b (.step_ite_false heval)
  | .step_ite_nondet_true => adminStep_toEvent b .step_ite_nondet_true
  | .step_ite_nondet_false => adminStep_toEvent b .step_ite_nondet_false
  | .step_loop_enter heval => adminStep_toEvent b (.step_loop_enter heval)
  | .step_loop_exit heval => adminStep_toEvent b (.step_loop_exit heval)
  | .step_loop_nondet_enter => adminStep_toEvent b .step_loop_nondet_enter
  | .step_loop_nondet_exit => adminStep_toEvent b .step_loop_nondet_exit
  | .step_exit => adminStep_toEvent b .step_exit
  | .step_typeDecl => adminStep_toEvent b .step_typeDecl
  | .step_stmts_nil => adminStep_toEvent b .step_stmts_nil
  | .step_stmts_cons => adminStep_toEvent b .step_stmts_cons
  | .step_seq_done => adminStep_toEvent b .step_seq_done
  | .step_seq_exit => adminStep_toEvent b .step_seq_exit
  | .step_block_done => adminStep_toEvent b .step_block_done
  | .step_block_exit_match hlabel => adminStep_toEvent b (.step_block_exit_match hlabel)
  | .step_block_exit_mismatch hlabel =>
    adminStep_toEvent b (.step_block_exit_mismatch hlabel)

/-- A failure-flag command execution, including a call, as an event command
    execution with a faithful trace. -/
theorem evalCommand_toEvent {fac : Expression.Factory} {σ σ' : CoreStore} {c : Command}
    {failed : Bool} (h : EvalCommand π fac σ c σ' failed) :
    ∃ tr, EvalCommandE π fac σ c σ' tr ∧ FaithfulTrace tr :=
  match h with
  | .cmd_sem hcmd => ⟨_, .cmd_sem hcmd.toEvalCmdE, evalCmd_faithful hcmd⟩
  | .call_sem hπ hentry hpre hbody hpost hexit =>
    match coreBodyExec_toEvent hbody with
    | ⟨_, hE, hf⟩ =>
      ⟨_, .call_sem hπ hentry hE hexit,
        ((evalChecks_faithful _ hpre).append hf).append (evalChecks_faithful _ hpost)⟩

/-- A failure-flag procedure-body execution as an event body execution. -/
private theorem coreBodyExec_toEvent {body : Procedure.Body} {ρ : Imperative.Env Expression}
    {σ' : CoreStore} {failed : Bool}
    (h : CoreBodyExec π body ρ σ' failed) :
    ∃ tr, CoreBodyExecE π body ρ σ' tr ∧ FaithfulTrace tr :=
  match h with
  | .structured (ρ := ρ) (ρ' := ρ') hstar =>
    match coreStepStar_toEvent hstar ρ.hasFailure with
    | ⟨tr, hE, hf⟩ =>
      ⟨tr, BigStepE.structured (ρ' := { ρ' with hasFailure := ρ.hasFailure })
        (by simpa [Config.withFailure] using hE), hf⟩

end

end Core.Specification

end -- public section

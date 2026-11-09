/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtCFGCallSemantics

/-! # Properties of the call-aware command semantics

`EvalCmdExtE` is mutually inductive with `BigStepE`, which nests through traced
closures of `StepStmtE` and `StepCFGE`. Its generated recursor therefore has six
motives and ordinary `induction` cannot use it directly.

`EvalCmdExtE.induct` exposes a single command motive. In its call case, the
induction hypothesis re-states the callee run over the command relation
"`EvalCmdExtE` and the motive holds", for either a structured or CFG body.
`evalCmdExtE_cmd_iff` characterizes evaluation of an embedded base command as
exactly `EvalCmdE`, with no call event behavior. `Calls.mem_checksAtCall`: a clause checked
at a call site (`Calls.checksAtCall`) is a clause of the callee's specification with the same
label, expression and attribute. `Calls.defaultAssertEvents_label_metadata`: the assertion
events emitted for a list of clauses carry the labels and metadata of its non-free clauses,
whatever the factory and store. -/

namespace Imperative

public section

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

/-- Induction on `EvalCmdExtE` with a single motive. In the `call_sem` case the
induction hypothesis covers every command step of a structured or CFG callee run,
including commands inside nested calls. -/
theorem EvalCmdExtE.induct
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {motive : ∀ fac σ c σ' evs, EvalCmdExtE π fac σ c σ' evs → Prop}
    {fac : P.Factory} {σ : SemanticStore P} {c : CmdExt P} {σ' : SemanticStore P}
    {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs)
    (cmd_sem : ∀ {fac σ c σ' emitted} (h : EvalCmdE (P := P) fac σ c σ' emitted),
      motive fac σ (.cmd c) σ' emitted (.cmd_sem h))
    (call_sem : ∀ {σ n p callArgs σ' σFinal bodyEvents md fac σAO}
      (hπ : π n = .some p)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : BigStepE π p.body ⟨σAO, fac⟩ σFinal bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σFinal σ'),
      ((∃ ss ρ', p.body = .structured ss ∧ ρ'.store = σFinal ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.stmt (Stmt.block "" ss #[]) ⟨σAO, fac⟩) bodyEvents (.terminal ρ')) ∨
       (∃ g ρ', p.body = .cfg g ∧ projectStore σAO ρ'.store = σFinal ∧
        StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.atBlock g g.entry ⟨σAO, fac⟩) bodyEvents (.terminal ρ'))) →
      motive fac σ (.call n callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σFinal p.spec.postconditions)
        (.call_sem hπ hentry hbody hexit)) :
    motive fac σ c σ' evs h :=
  EvalCmdExtE.rec (motive_2 := motive)
    (motive_1 := fun b ρ σFinal evs _ =>
      (∃ ss ρ', b = .structured ss ∧ ρ'.store = σFinal ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.stmt (Stmt.block "" ss #[]) ρ) evs (.terminal ρ')) ∨
      (∃ g ρ', b = .cfg g ∧ projectStore ρ.store ρ'.store = σFinal ∧
        StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.atBlock g g.entry ρ) evs (.terminal ρ')))
    (motive_3 := fun c evs c' _ =>
      StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_4 := fun c evs c' _ =>
      StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_5 := fun c evs c' _ =>
      StepStmtE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_6 := fun c evs c' _ =>
      StepCFGE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (fun _ ih => .inl ⟨_, _, rfl, rfl, ih⟩)
    (fun _ ih => .inr ⟨_, _, rfl, rfl, ih⟩)
    cmd_sem call_sem
    (fun _ => .refl _)
    (fun _ _ _ _ _ _ _ ihStep ihRest => .step _ _ _ _ _ ihStep ihRest)
    (fun _ => .refl _)
    (fun _ _ _ _ _ _ _ ihStep ihRest => .step _ _ _ _ _ ihStep ihRest)
    (fun h ih => .step_cmd ⟨h, ih⟩)
    .step_block
    (fun h => .step_ite_true h)
    (fun h => .step_ite_false h)
    .step_ite_nondet_true
    .step_ite_nondet_false
    (fun h => .step_loop_enter h)
    (fun h => .step_loop_exit h)
    .step_loop_nondet_enter
    .step_loop_nondet_exit
    .step_exit
    .step_typeDecl
    .step_stmts_nil
    .step_stmts_cons
    (fun _ ih => .step_seq_inner ih)
    .step_seq_done
    .step_seq_exit
    (fun _ ih => .step_block_body ih)
    .step_block_done
    (fun h => .step_block_exit_match h)
    (fun h => .step_block_exit_mismatch h)
    (fun h => .fetch h)
    (fun h ih => .step_cmd ⟨h, ih⟩)
    (fun h => .goto_true h)
    (fun h => .goto_false h)
    .finish
    h

/-- `EvalCmdExtE π` on an embedded base command is exactly `EvalCmdE`: a call's
    rule can never fire on a `CmdExt.cmd`, so no event is added or dropped. -/
theorem evalCmdExtE_cmd_iff
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {tr : Trace P} :
    EvalCmdExtE π fac σ (CmdExt.cmd c) σ' tr ↔
    EvalCmdE (P := P) fac σ c σ' tr := by
  constructor
  · intro h; cases h with | cmd_sem hb => exact hb
  · intro h; exact EvalCmdExtE.cmd_sem h

end

/-! ## Clauses checked at a call site -/

namespace Calls

public section

variable {P : PureExpr} [DecidableEq P.Ident]

/-- A clause of `checksAtCall callMd checks` is a clause of `checks` with the same label,
    expression and attribute. -/
theorem mem_checksAtCall {callMd : MetaData P}
    {checks : ListMap String (Check P)} {label : String} {check : Check P}
    (h : (label, check) ∈ (checksAtCall callMd checks).toList) :
    ∃ check₀, (label, check₀) ∈ checks.toList ∧ check.expr = check₀.expr ∧
      check.attr = check₀.attr := by
  obtain ⟨⟨l, c⟩, hmem, he⟩ := List.mem_map.mp h
  cases he
  exact ⟨c, hmem, rfl, rfl⟩

omit [DecidableEq P.Ident] in
/-- The assertion events `defaultAssertEvents fac σ checks` emits carry, in order, the labels
    and metadata of the non-free clauses of `checks`, whatever the factory and store. -/
theorem defaultAssertEvents_label_metadata (fac : P.Factory) (σ : SemanticStore P)
    (checks : ListMap String (Check P)) :
    (defaultAssertEvents fac σ checks).filterMap (fun
      | .assert a => some (a.label, a.metadata)
      | _ => none) =
      checks.toList.filterMap (fun (label, check) =>
        if check.attr = .Default then some (label, check.md) else none) := by
  unfold defaultAssertEvents
  induction checks.toList with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨l, c⟩ := hd
    by_cases h : c.attr = .Default <;> simp [h, ih]

end

end Calls

end Imperative

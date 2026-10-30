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
exactly `EvalCmdE`, with no call event behavior. -/

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
      (hbody : BigStepE π p.body ⟨σAO, fac, false⟩ σFinal bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σFinal σ'),
      ((∃ ss ρ', p.body = .structured ss ∧ ρ'.store = σFinal ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.stmt (Stmt.block "" ss #[]) ⟨σAO, fac, false⟩) bodyEvents (.terminal ρ')) ∨
       (∃ g ρ', p.body = .cfg g ∧ projectStore σAO ρ'.store = σFinal ∧
        StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.atBlock g g.entry ⟨σAO, fac, false⟩) bodyEvents (.terminal ρ'))) →
      motive fac σ (.call n callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO p.spec.preconditions ++ bodyEvents ++
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
    .step_admin
    (fun _ ih => .step_seq_inner ih)
    (fun _ ih => .step_block_body ih)
    (fun h ih => .step_cmd ⟨h, ih⟩)
    .step_admin
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

end Imperative

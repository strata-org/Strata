/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtCallSemantics

/-! # Properties of the call-aware command semantics

`EvalCmdExtE` is mutually inductive with `BigStepE` and nests through
`ReflTransTrace` and `StepStmtE`, so its recursor `EvalCmdExtE.rec` has four
motives and `induction` cannot use it directly.

Key theorems:
- `EvalCmdExtE.induct`: an induction principle for `EvalCmdExtE` with a single
  motive.  Its call case has an induction hypothesis for every command step of the
  callee body's run, at any call depth.  Usable as
  `induction h using EvalCmdExtE.induct`. -/

namespace Imperative

public section

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

/-- Induction on `EvalCmdExtE` with a single motive.  In the `call_sem` case the
induction hypothesis is the callee body's run, re-stated over the command relation
"`EvalCmdExtE` and the motive holds": every command step of the run, including
those inside nested calls, satisfies the motive. -/
theorem EvalCmdExtE.induct
    {π : String → Option (Procedure P (CmdExt P) Hdr)} {δ : ExtendFactory P}
    {motive : ∀ fac σ c σ' evs, EvalCmdExtE π δ fac σ c σ' evs → Prop}
    {fac : P.Factory} {σ : SemanticStore P} {c : CmdExt P} {σ' : SemanticStore P}
    {evs : Trace P}
    (h : EvalCmdExtE π δ fac σ c σ' evs)
    (cmd_sem : ∀ {fac σ c σ' emitted} (h : EvalCmdE (P := P) fac σ c σ' emitted),
      motive fac σ (.cmd c) σ' emitted (.cmd_sem h))
    (call_sem : ∀ {σ n p callArgs σ' σ_final fac_final bodyEvents md fac σAO}
      (hπ : π n = .some p)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : BigStepE π δ p.body σAO fac σ_final fac_final bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σ_final σ'),
      (∃ ss ρ', p.body = .structured ss ∧ ρ'.store = σ_final ∧ ρ'.factory = fac_final ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) δ
          (.stmt (Stmt.block "" ss #[]) ⟨σAO, fac, false⟩) bodyEvents (.terminal ρ')) →
      motive fac σ (.call n callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO p.spec.preconditions ++ bodyEvents ++
          Calls.defaultAssertEvents fac_final σ_final p.spec.postconditions)
        (.call_sem hπ hentry hbody hexit)) :
    motive fac σ c σ' evs h :=
  EvalCmdExtE.rec (motive_2 := motive)
    (motive_1 := fun b σ fac σf facf evs _ => ∃ ss ρ', b = .structured ss ∧
      ρ'.store = σf ∧ ρ'.factory = facf ∧
      StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) δ
        (.stmt (Stmt.block "" ss #[]) ⟨σ, fac, false⟩) evs (.terminal ρ'))
    (motive_3 := fun c evs c' _ =>
      StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) δ c evs c')
    (motive_4 := fun c evs c' _ =>
      StepStmtE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) δ c evs c')
    (fun _ ih => ⟨_, _, rfl, rfl, rfl, ih⟩) cmd_sem call_sem .refl
    (fun _ _ _ _ _ _ _ ih₁ ih₂ => .step _ _ _ _ _ ih₁ ih₂)
    (fun h ih => .step_cmd ⟨h, ih⟩) .step_admin (fun _ ih => .step_seq_inner ih)
    (fun _ ih => .step_block_body ih) h

end

end Imperative

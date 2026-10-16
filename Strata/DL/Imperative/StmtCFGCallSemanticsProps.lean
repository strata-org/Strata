/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtCFGCallSemantics

/-! # Properties of the call-aware command semantics

`EvalCmdExtE` is mutually inductive with `BigStepE` and `CFGRunExtE` and nests
through `ReflTransTrace` and `StepStmtE`, so its recursor `EvalCmdExtE.rec` has
five motives and `induction` cannot use it directly.

Key theorems:
- `CFGRunExtE_iff_stepCFGStarE`: the CFG run relation of `BigStepE.cfg` is the
  generic event-trace CFG closure `StepCFGStarE` at the command relation
  `EvalCmdExtE π`.
- `EvalCmdExtE.induct`: an induction principle for `EvalCmdExtE` with a single
  motive.  Its call case has an induction hypothesis for every command step of the
  callee body's run, structured or CFG, at any call depth.  Usable as
  `induction h using EvalCmdExtE.induct`. -/

namespace Imperative

public section

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

omit [DecidableEq P.Ident] [HasOldIdent P] [HasFvar P] in
/-- A `StepCFGE` step over `noCommandEvalEvents`, which has no command step, is a
control-flow step: it is a `StepCFGE` step, with the same events, over any command
relation. -/
private theorem StepCFGE.of_noCommandEvalEvents {CmdT EventT : Type} {l : Type} [BEq l]
    [HasVal P] {EvalCmd : EvalCmdParamE P CmdT EventT} {fac : P.Factory}
    {g : CFG l (DetBlock l CmdT P)} {c c' : CFGConfig l CmdT P} {evs : List EventT}
    (h : StepCFGE P (noCommandEvalEvents P CmdT EventT) fac g c evs c') :
    StepCFGE P EvalCmd fac g c evs c' := by
  cases h with
  | step_cmd h => exact h.elim
  | step_admin h => exact .step_admin h

/-- A call-aware CFG run `CFGRunExtE π fac g` has exactly the derivations of the
generic event-trace CFG closure `StepCFGStarE` over the command relation
`EvalCmdExtE π`, with the same events. -/
theorem CFGRunExtE_iff_stepCFGStarE
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {fac : P.Factory} {g : DetCFG P (CmdExt P)} {c c' : CFGConfig String (CmdExt P) P}
    {evs : Trace P} :
    CFGRunExtE π fac g c evs c' ↔ StepCFGStarE P (EvalCmdExtE π) fac g c evs c' := by
  constructor
  · exact CFGRunExtE.rec (motive_1 := fun _ _ _ _ _ => True)
      (motive_2 := fun fac g c evs c' _ => StepCFGStarE P (EvalCmdExtE π) fac g c evs c')
      (motive_3 := fun _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True) (fun _ _ => trivial) (fun _ _ => trivial) (.refl _)
      (fun h _ _ ih => .step _ _ _ _ _ (.step_cmd h) ih)
      (fun h _ ih => .step _ [] _ _ _ h.of_noCommandEvalEvents ih) (fun _ => trivial)
      (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ => trivial) (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  · intro h
    induction h with
    | refl => exact .refl
    | step _ _ _ _ _ hs _ ih =>
      cases hs with
      | step_cmd h => exact .step_cmd h ih
      | step_admin h => exact .step_admin (.step_admin h) ih

/-- Induction on `EvalCmdExtE` with a single motive.  In the `call_sem` case the
induction hypothesis is the callee body's run, structured or CFG, re-stated over the
command relation "`EvalCmdExtE` and the motive holds": every command step of the
run, including those inside nested calls, satisfies the motive. -/
theorem EvalCmdExtE.induct
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {motive : ∀ fac σ c σ' evs, EvalCmdExtE π fac σ c σ' evs → Prop}
    {fac : P.Factory} {σ : SemanticStore P} {c : CmdExt P} {σ' : SemanticStore P}
    {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs)
    (cmd_sem : ∀ {fac σ c σ' emitted} (h : EvalCmdE (P := P) fac σ c σ' emitted),
      motive fac σ (.cmd c) σ' emitted (.cmd_sem h))
    (call_sem : ∀ {σ n p callArgs σ' σ_final bodyEvents md fac σAO}
      (hπ : π n = .some p)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : BigStepE π p.body ⟨σAO, fac, false⟩ σ_final bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σ_final σ'),
      ((∃ ss ρ', p.body = .structured ss ∧ ρ'.store = σ_final ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.stmt (Stmt.block "" ss #[]) ⟨σAO, fac, false⟩) bodyEvents (.terminal ρ')) ∨
       (∃ g σ' f, p.body = .cfg g ∧ projectStore σAO σ' = σ_final ∧
        StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) fac g
          (.atBlock g.entry σAO false) bodyEvents (.terminal σ' f))) →
      motive fac σ (.call n callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO p.spec.preconditions ++ bodyEvents ++
          Calls.defaultAssertEvents fac σ_final p.spec.postconditions)
        (.call_sem hπ hentry hbody hexit)) :
    motive fac σ c σ' evs h :=
  EvalCmdExtE.rec (motive_3 := motive)
    (motive_1 := fun b ρ σf evs _ =>
      (∃ ss ρ', b = .structured ss ∧ ρ'.store = σf ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.stmt (Stmt.block "" ss #[]) ρ) evs (.terminal ρ')) ∨
      (∃ g σ' f, b = .cfg g ∧ projectStore ρ.store σ' = σf ∧
        StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) ρ.factory g
          (.atBlock g.entry ρ.store ρ.hasFailure) evs (.terminal σ' f)))
    (motive_2 := fun fac g c evs c' _ =>
      StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) fac g c evs c')
    (motive_4 := fun c evs c' _ =>
      StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_5 := fun c evs c' _ =>
      StepStmtE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (fun _ ih => .inl ⟨_, _, rfl, rfl, ih⟩) (fun _ ih => .inr ⟨_, _, _, rfl, rfl, ih⟩)
    (.refl _) (fun h _ ih₁ ih₂ => .step _ _ _ _ _ (.step_cmd ⟨h, ih₁⟩) ih₂)
    (fun h _ ih => .step _ [] _ _ _ h.of_noCommandEvalEvents ih) cmd_sem call_sem .refl
    (fun _ _ _ _ _ _ _ ih₁ ih₂ => .step _ _ _ _ _ ih₁ ih₂)
    (fun h ih => .step_cmd ⟨h, ih⟩) .step_admin (fun _ ih => .step_seq_inner ih)
    (fun _ ih => .step_block_body ih) h

end

end Imperative

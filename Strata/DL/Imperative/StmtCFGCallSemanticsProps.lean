/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.CFGSemanticsProps

/-! # Properties of the call-aware command semantics

`EvalCmdViewE` is mutually inductive with `BigStepViewE`, which nests through traced
closures of `StepStmtE` and `StepCFGE`. Its generated recursor therefore has six
motives and ordinary `induction` cannot use it directly. `EvalCmdViewE.induct` exposes a
single command motive; in its call cases the induction hypothesis covers the callee run
(`BodyRunE`). The kind of a `CmdExt` command under `Calls.CmdExt.sem` determines it
(`Calls.CmdExt.sem_kind_base`, `Calls.CmdExt.sem_kind_call`, `Calls.CmdExt.sem_kind_ne_ext`).

`EvalCmdExtE.induct` is the same principle for `EvalCmdExtE`. In its call case, the
induction hypothesis re-states the callee run over the command relation
"`EvalCmdExtE` and the motive holds", for either a structured or CFG body.
`evalCmdExtE_cmd_iff` characterizes evaluation of an embedded base command as
exactly `EvalCmdE`, with no call event behavior, so the `EvalCmdE.*_inv` inversions of
`CmdSemanticsProps` apply to it. `EvalCmdExtE.assumeRun_inv` and `EvalCmdExtE.assertRun_inv`
invert completed runs of an `assume` or `assert` statement. `EvalCmdExtE.call_iff_contract`: a
call to an opaque callee runs exactly as the contract call semantics `EvalCmdExtContractE`. `Calls.mem_checksAtCall`: a clause
checked at a call site (`Calls.checksAtCall`) is a clause of the callee's specification with
the same label, expression and attribute. `Calls.defaultAssertEvents_label_metadata`: the assertion
events emitted for a list of clauses carry the labels and metadata of its non-free clauses,
whatever the factory and store. -/

namespace Imperative

public section

section ViewInduct

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] {CmdT : Type}

/-- A run of the body `b` from `ρ` over the command relation `E` to the final store `σFinal`, as
    the two rules of `BigStepE` and `BigStepViewE` give it: the shape the induction principle
    `EvalCmdViewE.induct` uses for a callee body. -/
@[expose] def BodyRunE (E : EvalCmdParamE P CmdT (Event P)) (b : Body P CmdT) (ρ : Env P)
    (σFinal : SemanticStore P) (evs : Trace P) : Prop :=
  (∃ ss ρ' opq, b = .structured ss opq ∧ ρ'.store = σFinal ∧
    StepStmtStarE P E (.stmt (Stmt.block "" ss #[]) ρ) evs (.terminal ρ')) ∨
  (∃ g ρ' opq, b = .cfg g opq ∧ projectStore ρ.store ρ'.store = σFinal ∧
    StepCFGStarE P E (.atBlock g g.entry ρ) evs (.terminal ρ'))

/-- Induction on `EvalCmdViewE` with a single motive. In the `call_sem` and `ext_call_sem` cases
    the induction hypothesis covers every command step of the callee run (`BodyRunE`), including
    commands inside nested calls. The `call_contract_sem` and `ext_call_contract_sem` cases, calls
    to an opaque callee, have no callee run. -/
theorem EvalCmdViewE.induct
    {S : Calls.CmdSem P CmdT Hdr} {π : String → Option (Procedure P CmdT Hdr)}
    {motive : ∀ fac σ c σ' evs, EvalCmdViewE S π fac σ c σ' evs → Prop}
    {fac : P.Factory} {σ : SemanticStore P} {c : CmdT} {σ' : SemanticStore P}
    {evs : Trace P}
    (h : EvalCmdViewE S π fac σ c σ' evs)
    (base_sem : ∀ {fac σ c b σ' emitted} (hk : S.kind c = .base b)
      (h : EvalCmdE (P := P) fac σ b σ' emitted),
      motive fac σ c σ' emitted (.base_sem hk h))
    (call_sem : ∀ {σ c n inst p₀ p callArgs σ' σFinal bodyEvents md fac σAO}
      (hk : S.kind c = .call n callArgs md inst) (hπ : π n = .some p₀) (hinst : inst p₀ = .some p)
      (hno : p.body.isOpaque = false)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : BigStepViewE S π p.body ⟨σAO, fac⟩ σFinal bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σFinal σ'),
      BodyRunE (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) p.body ⟨σAO, fac⟩ σFinal
        bodyEvents →
      motive fac σ c σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σFinal p.spec.postconditions)
        (.call_sem hk hπ hinst hno hentry hbody hexit))
    (call_contract_sem : ∀ {σ σO c n inst p₀ p callArgs σ' md fac σAO}
      (hk : S.kind c = .call n callArgs md inst) (hπ : π n = .some p₀) (hinst : inst p₀ = .some p)
      (ho : p.body.isOpaque = true)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hhavoc : Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO)
      (hexit : Calls.CallExit fac σ p callArgs σO σ'),
      motive fac σ c σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)
        (.call_contract_sem hk hπ hinst ho hentry hhavoc hexit))
    (ext_sem : ∀ {fac σ c σ' emitted} (hk : S.kind c = .ext)
      (h : S.ExtE fac σ c (.done σ') emitted),
      motive fac σ c σ' emitted (.ext_sem hk h))
    (ext_call_sem : ∀ {σ σ₁ c n inst p₀ p callArgs σ' σFinal extEvents bodyEvents md fac σAO}
      (hk : S.kind c = .ext) (hx : S.ExtE fac σ c (.call σ₁ n callArgs md inst) extEvents)
      (hπ : π n = .some p₀) (hinst : inst p₀ = .some p) (hno : p.body.isOpaque = false)
      (hentry : Calls.CallEntry fac σ₁ p callArgs σAO)
      (hbody : BigStepViewE S π p.body ⟨σAO, fac⟩ σFinal bodyEvents)
      (hexit : Calls.CallExit fac σ₁ p callArgs σFinal σ'),
      BodyRunE (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) p.body ⟨σAO, fac⟩ σFinal
        bodyEvents →
      motive fac σ c σ'
        (extEvents ++
          Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σFinal p.spec.postconditions)
        (.ext_call_sem hk hx hπ hinst hno hentry hbody hexit))
    (ext_call_contract_sem : ∀ {σ σ₁ σO c n inst p₀ p callArgs σ' extEvents md fac σAO}
      (hk : S.kind c = .ext) (hx : S.ExtE fac σ c (.call σ₁ n callArgs md inst) extEvents)
      (hπ : π n = .some p₀) (hinst : inst p₀ = .some p) (ho : p.body.isOpaque = true)
      (hentry : Calls.CallEntry fac σ₁ p callArgs σAO)
      (hhavoc : Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO)
      (hexit : Calls.CallExit fac σ₁ p callArgs σO σ'),
      motive fac σ c σ'
        (extEvents ++
          Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)
        (.ext_call_contract_sem hk hx hπ hinst ho hentry hhavoc hexit)) :
    motive fac σ c σ' evs h :=
  EvalCmdViewE.rec (motive_2 := motive)
    (motive_1 := fun b ρ σFinal evs _ =>
      BodyRunE (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) b ρ σFinal evs)
    (motive_3 := fun c evs c' _ =>
      StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_4 := fun c evs c' _ =>
      StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_5 := fun c evs c' _ =>
      StepStmtE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (motive_6 := fun c evs c' _ =>
      StepCFGE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h) c evs c')
    (fun _ ih => .inl ⟨_, _, _, rfl, rfl, ih⟩)
    (fun _ ih => .inr ⟨_, _, _, rfl, rfl, ih⟩)
    base_sem call_sem call_contract_sem ext_sem ext_call_sem ext_call_contract_sem
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

end ViewInduct

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [ProcedureTypeInstantiation P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

/-- Induction on `EvalCmdExtE` with a single motive. In the `call_sem` case the
induction hypothesis covers every command step of a structured or CFG callee run,
including commands inside nested calls. The `call_abstract_sem` case, a call to an abstract
callee, has no callee run. -/
theorem EvalCmdExtE.induct
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {motive : ∀ fac σ c σ' evs, EvalCmdExtE π fac σ c σ' evs → Prop}
    {fac : P.Factory} {σ : SemanticStore P} {c : CmdExt P} {σ' : SemanticStore P}
    {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs)
    (cmd_sem : ∀ {fac σ c σ' emitted} (h : EvalCmdE (P := P) fac σ c σ' emitted),
      motive fac σ (.cmd c) σ' emitted (.cmd_sem h))
    (call_sem : ∀ {σ n tyArgs p callArgs σ' σFinal bodyEvents md fac σAO}
      (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p) (hno : p.body.isOpaque = false)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : BigStepE π p.body ⟨σAO, fac⟩ σFinal bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σFinal σ'),
      ((∃ ss ρ' opq, p.body = .structured ss opq ∧ ρ'.store = σFinal ∧
        StepStmtStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.stmt (Stmt.block "" ss #[]) ⟨σAO, fac⟩) bodyEvents (.terminal ρ')) ∨
       (∃ g ρ' opq, p.body = .cfg g opq ∧ projectStore σAO ρ'.store = σFinal ∧
        StepCFGStarE P (fun fac σ c σ' evs => ∃ h, motive fac σ c σ' evs h)
          (.atBlock g g.entry ⟨σAO, fac⟩) bodyEvents (.terminal ρ'))) →
      motive fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σFinal p.spec.postconditions)
        (.call_sem hπ hno hentry hbody hexit))
    (call_abstract_sem : ∀ {σ σO n tyArgs p callArgs σ' md fac σAO}
      (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p) (hb : p.body.isOpaque = true)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hhavoc : Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO)
      (hexit : Calls.CallExit fac σ p callArgs σO σ'),
      motive fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)
        (.call_abstract_sem hπ hb hentry hhavoc hexit)) :
    motive fac σ c σ' evs h := by
  induction h using EvalCmdViewE.induct with
  | base_sem hk h =>
    obtain rfl := Calls.CmdExt.sem_kind_base hk
    exact cmd_sem h
  | call_sem hk hπ hinst hno hentry hbody hexit ih =>
    obtain ⟨tyArgs, rfl, hcallee⟩ := Calls.CmdExt.sem_kind_call_callee hk hπ hinst
    exact call_sem hcallee hno hentry hbody hexit ih
  | call_contract_sem hk hπ hinst ho hentry hhavoc hexit =>
    obtain ⟨tyArgs, rfl, hcallee⟩ := Calls.CmdExt.sem_kind_call_callee hk hπ hinst
    exact call_abstract_sem hcallee ho hentry hhavoc hexit
  | ext_sem hk => exact absurd hk (Calls.CmdExt.sem_kind_ne_ext _)
  | ext_call_sem hk => exact absurd hk (Calls.CmdExt.sem_kind_ne_ext _)
  | ext_call_contract_sem hk => exact absurd hk (Calls.CmdExt.sem_kind_ne_ext _)

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

/-- A run of an `assume` statement that terminates or exits emits the assumption captured at
its entry environment and ends in that environment. -/
theorem EvalCmdExtE.assumeRun_inv
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {l : String} {e : P.Expr} {md : MetaData P} {ρ ρ' : Env P} {tr : Trace P}
    (h : StepStmtStarE P (EvalCmdExtE π) (.stmt (.cmd (.cmd (.assume l e md))) ρ) tr
        (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE P (EvalCmdExtE π) (.stmt (.cmd (.cmd (.assume l e md))) ρ) tr
        (.exiting lbl ρ')) :
    tr = [.assume ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  obtain ⟨hcmd, hρ'⟩ := cmdRun_invE h
  obtain ⟨hσ, rfl⟩ := EvalCmdE.assume_inv (evalCmdExtE_cmd_iff.mp hcmd)
  exact ⟨rfl, by rw [hρ', hσ]⟩

/-- A run of an `assert` statement that terminates or exits emits the assertion captured at
its entry environment and ends in that environment. -/
theorem EvalCmdExtE.assertRun_inv
    {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {l : String} {e : P.Expr} {md : MetaData P} {ρ ρ' : Env P} {tr : Trace P}
    (h : StepStmtStarE P (EvalCmdExtE π) (.stmt (.cmd (.cmd (.assert l e md))) ρ) tr
        (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE P (EvalCmdExtE π) (.stmt (.cmd (.cmd (.assert l e md))) ρ) tr
        (.exiting lbl ρ')) :
    tr = [.assert ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  obtain ⟨hcmd, hρ'⟩ := cmdRun_invE h
  obtain ⟨hσ, rfl⟩ := EvalCmdE.assert_inv (evalCmdExtE_cmd_iff.mp hcmd)
  exact ⟨rfl, by rw [hρ', hσ]⟩

/-- A call to an opaque callee (`Body.isOpaque`) has exactly the runs of the contract call
semantics: `EvalCmdExtE.call_abstract_sem` and `EvalCmdExtContractE.call_sem` relate the same
stores by the same events. -/
theorem EvalCmdExtE.call_iff_contract
    {π : String → Option (Procedure P (CmdExt P) Hdr)} {fac : P.Factory}
    {σ σ' : SemanticStore P} {n : String} {tyArgs : Option (List P.Ty)}
    {callArgs : List (CallArg P)} {md : MetaData P} {evs : Trace P}
    {p : Procedure P (CmdExt P) Hdr} (hπ : Calls.typeInstantiatedCallee π n tyArgs = some p)
    (ho : p.body.isOpaque = true) :
    EvalCmdExtE π fac σ (.call n tyArgs callArgs md) σ' evs ↔
      EvalCmdExtContractE π fac σ (.call n tyArgs callArgs md) σ' evs := by
  constructor
  · intro h
    cases h with
    | call_sem hπ' hno =>
      cases hπ.symm.trans hπ'
      exact nomatch ho.symm.trans hno
    | call_abstract_sem hπ' _ he hh hx => exact .call_sem hπ' he hh hx
  · intro h
    cases h with
    | call_sem hπ' he hh hx =>
      cases hπ.symm.trans hπ'
      exact .call_abstract_sem hπ' ho he hh hx

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

/-- Saving `old` copies of some variables leaves every slot that is not named like such a copy
    unchanged. -/
theorem withOldSnapshots_eq [HasOldIdent P] {snap : List P.Ident} {σ : SemanticStore P}
    {z : P.Ident} (h : ∀ g ∈ snap, HasOldIdent.mkOld g ≠ z) :
    withOldSnapshots snap σ z = σ z := by
  unfold withOldSnapshots
  have hnone : snap.find? (fun g => HasOldIdent.mkOld g == z) = none := by
    rw [List.find?_eq_none]
    intro g hg hb
    exact h g hg (beq_iff_eq.mp hb)
  rw [hnone]

end

end Calls

end Imperative

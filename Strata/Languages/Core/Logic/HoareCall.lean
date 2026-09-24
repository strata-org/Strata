/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import all Strata.Languages.Core.Logic.ContractToHoareTripleProps

/-! # Hoare rule for Core procedure calls

This module turns a proven `Procedure.contractTriple` into a Hoare triple for a
call to that procedure. `Procedure.storeFrame` states agreement outside the
callee's declared outputs, `Procedure.bodyFrame` requires every body execution to
establish that relation, and `Procedure.call_of_contract` transports the contract,
signature-derived input typing, and frame facts to the caller.
Supporting contract-event and statement-run metatheory lives in the corresponding
property modules.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-! ### A contract-aware rule for procedure calls

A `call` executes its callee's body; if that body meets the callee's contract, the
call satisfies a Hoare triple whose pre/postcondition are related to the contract by
two side conditions. -/

local notation "I" => EvaluatorBasedInterp Expression


/-- Entry and exit stores of `proc` agree at every variable except its declared
outputs. Since inout parameters occur among `header.outputs`, they are included in
the permitted write set. -/
@[expose] def Procedure.storeFrame (proc : Procedure)
    (σ_entry σ_exit : CoreStore) : Prop :=
  Imperative.invStoresExcept σ_entry σ_exit (ListMap.keys proc.header.outputs)

/-- Every event-producing execution of `proc`'s body respects the write set
specified by its signature. -/
@[expose] def Procedure.bodyFrame
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (proc : Procedure) : Prop :=
  ∀ σ_entry fac σ_exit fac_exit emitted,
    CoreBodyExecE π φ proc.body σ_entry fac σ_exit fac_exit emitted →
    Procedure.storeFrame proc σ_entry σ_exit

/-- **A procedure call meets a Hoare triple built from its callee's contract.**

    When the callee named `procName` meets its `contractTriple` and every execution
    respects the output write set in its signature, the call satisfies a `Triple`.
    `hentry` establishes the callee precondition, input-value typing from the
    signature, and body-frame well-formedness.
    `hexit` receives caller command well-formedness, `CallEntry`, the callee entry
    store, `Procedure.storeFrame`, and restoration of the entry factory, so it may
    relate caller actuals to preserved input-only formals before deriving the
    caller's postcondition. -/
theorem Procedure.call_of_contract (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (callArgs : List (Imperative.CallArg Expression))
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hcontract : Procedure.contractTriple φ p params procName)
    (hframe : ∀ proc, p.findProcByString? procName = some proc →
      Procedure.bodyFrame p.findProcByString? φ proc)
    (hentry : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure) (bss : Statements)
        (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName callArgs md) ρ₀ →
      p.findProcByString? procName = some proc → proc.body = .structured bss →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      (Procedure.preAsPredicate proc { store := σAO, factory := ρ₀.factory, hasFailure := false } ∧
          ({ store := σAO, factory := ρ₀.factory, hasFailure := false } :
            Imperative.Env Expression).factory = Core.Factory ∧
          Procedure.oldInoutAsPredicate proc
            { store := σAO, factory := ρ₀.factory, hasFailure := false } ∧
          Procedure.inputAsPredicate proc
            { store := σAO, factory := ρ₀.factory, hasFailure := false }) ∧
        BlockInitEnvWF params [Imperative.Stmt.block "" bss #[]]
          { store := σAO, factory := ρ₀.factory, hasFailure := false })
    (hexit : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (ρ' : Imperative.Env Expression) (σ' σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName callArgs md) ρ₀ →
      p.findProcByString? procName = some proc →
      Procedure.postAsPredicate proc ρ' →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Procedure.storeFrame proc σAO ρ'.store →
      CallExit ρ₀.factory ρ₀.store proc callArgs ρ'.store σ' →
      ρ'.factory = ρ₀.factory →
      Post { ρ₀ with store := σ' }) :
    Triple p.findProcByString? φ params Pre
      [Statement.call procName callArgs md] Post := by
  obtain ⟨cproc, cbss, hcproc, hcbody, htriple⟩ := hcontract
  refine cmd p.findProcByString? φ params (Imperative.CmdExt.call procName callArgs md)
    Pre Post (fun ρ₀ σ' emitted hpre hwf hstep => ?_)
  cases hstep with
  | call_sem hlookup hcallentry hbodyE hcallexit =>
    -- The resolved callee is the one the contract names.
    obtain rfl : cproc = _ := Option.some.inj (hcproc.symm.trans hlookup)
    have hframeRel := hframe cproc hcproc _ _ _ _ _ hbodyE
    rw [hcbody] at hbodyE
    cases hbodyE with
    | structured hrun =>
      rename_i ρ'
      have hfac' : ρ'.factory = ρ₀.factory := by
        obtain ⟨ρ_inner, _hinner, hρ'⟩ :=
          Imperative.stmt_block_reaches_doneE
            (P := Expression) (EvalCmd := EvalCommandE p.findProcByString? φ)
            (extendFactory := EvalPureFunc φ) (.inl hrun)
        simpa using congrArg Imperative.Env.factory hρ'
      -- Move the callee-body run into the singleton-list run the contract triple consumes.
      have hrun' := Imperative.stmtRun_to_singletonE
        (EvalCommandE p.findProcByString? φ) (EvalPureFunc φ) hrun
      obtain ⟨⟨hpreC, hfacC, holdC, hinputsC⟩, hbwf⟩ :=
        hentry ρ₀ cproc cbss _ hpre hwf hcproc hcbody hcallentry
      -- The contract triple validates the body trace and yields the callee postcondition.
      have htb := htriple { store := _, factory := ρ₀.factory, hasFailure := false }
        ρ' _ ⟨hpreC, hfacC, holdC, hinputsC⟩ hbwf (Or.inl hrun')
      have hvalidA :
          Trace.AssertionsValid Expression I
            (defaultAssertEvents ρ₀.factory _ cproc.spec.preconditions) :=
        assertionsValid_defaultAssertEvents ρ₀.factory _ cproc.spec.preconditions
          (fun label check hmem _ => hpreC label check hmem)
      have hvalidB : ∀ _ : Procedure.postAsPredicate cproc ρ',
          Trace.AssertionsValid Expression I
            (defaultAssertEvents ρ'.factory ρ'.store cproc.spec.postconditions) :=
        fun hpostC =>
          assertionsValid_defaultAssertEvents ρ'.factory ρ'.store cproc.spec.postconditions
            (fun label check hmem hattr => hpostC label check hmem hattr)
      refine ⟨?_, ?_⟩
      · refine Trace.AssertionsValid.append_of_reachable_left I
          (Trace.AssertionsValid.append_of_reachable_left I hvalidA (fun _ => htb.1)) ?_
        exact fun hreachAB => hvalidB (htb.2 (Trace.Reachable.right_of_append I hreachAB))
      · intro hreach
        exact hexit ρ₀ cproc ρ' σ' _ hpre hwf hcproc
          (htb.2 (Trace.Reachable.right_of_append I
            (Trace.Reachable.left_of_append I hreach)))
          hcallentry hframeRel hcallexit hfac'

end Hoare

end Core.Logic

end -- public section

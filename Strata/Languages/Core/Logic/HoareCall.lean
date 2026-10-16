/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.DL.Imperative.CFGSemanticsProps
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

    (proc : Procedure) : Prop :=
  ∀ σ_entry fac σ_exit emitted,
    CoreBodyExecE π proc.body ⟨σ_entry, fac, false⟩ σ_exit emitted →
    Procedure.storeFrame proc σ_entry σ_exit

/-- **A procedure call meets a Hoare triple built from its callee's contract.**

    When the callee named `procName` meets its `contractTriple` and every execution
    respects the output write set in its signature, the call satisfies a `Triple`.
    `hentry` establishes the contract precondition shared by both body kinds and,
    depending on the resolved body, the structured block gate or the CFG gate.
    `hexit` receives caller command well-formedness, `CallEntry`, the callee entry
    store, `Procedure.storeFrame`, and restoration of the entry factory, so it may
    relate caller actuals to preserved input-only formals before deriving the
    caller's postcondition. The CFG `contractTriple` already checks its
    postcondition on the projected final store, so no separate projection
    hypothesis is needed. -/
theorem Procedure.call_of_contract (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (callArgs : List (Imperative.CallArg Expression))
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hcontract : Procedure.contractTriple p params procName)
    (hframe : ∀ proc, p.findProcByString? procName = some proc →
      Procedure.bodyFrame p.findProcByString? proc)
    (hentry : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName callArgs md) ρ₀ →
      p.findProcByString? procName = some proc →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Procedure.contractPre proc
          { store := σAO, factory := ρ₀.factory, hasFailure := false } ∧
        match proc.body with
        | .structured bss =>
            BlockInitEnvWF params [Imperative.Stmt.block "" bss #[]]
              { store := σAO, factory := ρ₀.factory, hasFailure := false }
        | .cfg cfg =>
            CFGInitEnvWF params cfg
              { store := σAO, factory := ρ₀.factory, hasFailure := false })
    (hexit : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (ρ' : Imperative.Env Expression) (σ' σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName callArgs md) ρ₀ →
      p.findProcByString? procName = some proc →
      Procedure.postAsPredicate proc ρ' →
      ρ'.factory = ρ₀.factory →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Procedure.storeFrame proc σAO ρ'.store →
      CallExit ρ₀.factory ρ₀.store proc callArgs ρ'.store σ' →
      Post { ρ₀ with store := σ' }) :
    Triple p.findProcByString? params Pre
      [Statement.call procName callArgs md] Post := by
  obtain ⟨cproc, hcproc, htriple⟩ := hcontract
  refine cmd p.findProcByString? params (Imperative.CmdExt.call procName callArgs md)
    Pre Post (fun ρ₀ σ' emitted hpre hwf hstep => ?_)
  cases hstep with
  | @call_sem _ _ _ _ _ _ _ _ _ σAO hlookup hcallentry hbodyE hcallexit =>
    obtain rfl : cproc = _ := Option.some.inj (hcproc.symm.trans hlookup)
    have hframeRel := hframe cproc hcproc _ _ _ _ hbodyE
    obtain ⟨⟨hpreC, hfacC, holdC, hinputsC⟩, hbodyWF⟩ :=
      hentry ρ₀ cproc _ hpre hwf hcproc hcallentry
    -- The precondition assertions are valid once, independent of the body kind.
    have hvalidA :
        Trace.AssertionsValid Expression I
          (defaultAssertEvents ρ₀.factory σAO cproc.spec.preconditions) :=
      assertionsValid_defaultAssertEvents ρ₀.factory σAO cproc.spec.preconditions
        (fun label check hmem _ => hpreC label check hmem)
    -- Shared proof tail: given the body triple's conclusion about a post-env
    -- `ρpost` whose store is the callee's final store, discharge the call's
    -- obligation.  Both body kinds instantiate it, differing only in `ρpost`.
    have finish : ∀ (ρpost : Imperative.Env Expression) (bodyEvents : Trace Expression),
        ρpost.factory = ρ₀.factory →
        Procedure.storeFrame cproc σAO ρpost.store →
        CallExit ρ₀.factory ρ₀.store cproc callArgs ρpost.store σ' →
        (Trace.AssertionsValid Expression I bodyEvents ∧
          (Trace.Reachable Expression I bodyEvents →
            Procedure.postAsPredicate cproc ρpost)) →
        Trace.AssertionsValid Expression I
            (defaultAssertEvents ρ₀.factory σAO cproc.spec.preconditions ++ bodyEvents ++
              defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions) ∧
          (Trace.Reachable Expression I
              (defaultAssertEvents ρ₀.factory σAO cproc.spec.preconditions ++ bodyEvents ++
                defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions) →
            Post { ρ₀ with store := σ' }) := by
      intro ρpost bodyEvents hρpostfac hframeρ hcallexitρ htb
      have hvalidB : Procedure.postAsPredicate cproc ρpost →
          Trace.AssertionsValid Expression I
            (defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions) :=
        fun hpostC =>
          assertionsValid_defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions
            (fun label check hmem hattr => hρpostfac ▸ hpostC label check hmem hattr)
      refine ⟨?_, ?_⟩
      · refine Trace.AssertionsValid.append_of_reachable_left I
          (Trace.AssertionsValid.append_of_reachable_left I hvalidA (fun _ => htb.1)) ?_
        exact fun hreachAB => hvalidB (htb.2 (Trace.Reachable.right_of_append I hreachAB))
      · intro hreach
        exact hexit ρ₀ cproc ρpost σ' _ hpre hwf hcproc
          (htb.2 (Trace.Reachable.right_of_append I
            (Trace.Reachable.left_of_append I hreach)))
          hρpostfac hcallentry hframeρ hcallexitρ
    cases hcbody : cproc.body with
    | structured cbss =>
      rw [hcbody] at hbodyE htriple hbodyWF
      cases hbodyE with
      | structured hrun =>
        rename_i ρ'
        have hρ'fac : ρ'.factory = ρ₀.factory :=
          (Imperative.starE_preserves_factory hrun).symm
        have hrun' := Imperative.stmtRun_to_singletonE
          (EvalCommandE p.findProcByString?) hrun
        have htb := htriple
          { store := σAO, factory := ρ₀.factory, hasFailure := false }
          ρ' _ ⟨hpreC, hfacC, holdC, hinputsC⟩ hbodyWF (Or.inl hrun')
        exact finish ρ' _ hρ'fac hframeRel hcallexit htb
    | cfg cfg =>
      rw [hcbody] at hbodyE htriple hbodyWF
      cases hbodyE with
      | cfg hrun =>
        rename_i ρ'
        have hρ'fac : ρ'.factory = ρ₀.factory :=
          (StepCFGStarE.preserves_factory hrun).symm
        have htb := htriple
          { store := σAO, factory := ρ₀.factory, hasFailure := false }
          { store := σAO, factory := ρ₀.factory, hasFailure := false }
          ρ' _ ⟨⟨hpreC, hfacC, holdC, hinputsC⟩, rfl⟩ hbodyWF (Or.inl hrun)
        exact finish { ρ' with store := Imperative.projectStore σAO ρ'.store } _
          hρ'fac hframeRel hcallexit htb

end Hoare

end Core.Logic

end -- public section

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.InterpreterCallProps
import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.Languages.Core.Logic.ContractToHoareTripleProps

/-! # Hoare rule for Core procedure calls

This module turns a proven `Procedure.contractTriple` into a Hoare triple for a
call to that procedure. `Procedure.storeFrame` states agreement outside the
callee's declared outputs, `Procedure.bodyFrame` requires every body execution to
establish that relation, and `Procedure.bodyOutputsTyped` guarantees canonical values
for declared output types. `Procedure.call_of_contract` transports these facts and the
semantic contract to the caller.
`HoareTotal.Procedure.call_of_contract` is its total-correctness counterpart: it gives a
`HoareTotal.Triple` for the call when the call can also execute.
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
    CoreBodyExecE π proc.body ⟨σ_entry, fac⟩ σ_exit emitted →
    Procedure.storeFrame proc σ_entry σ_exit

/-- Every event-producing execution of `proc`'s body binds its declared outputs
    to values matching their types, provided its inputs do so at entry. -/
@[expose] def Procedure.bodyOutputsTyped
    (factory : Lambda.Factory CoreLParams)
    (π : String → Option Procedure) (proc : Procedure) : Prop :=
  ∀ σ_entry fac σ_exit emitted,
    fac.factory = factory →
    Procedure.inputAsPredicate proc
        { store := σ_entry, factory := fac } →
    CoreBodyExecE π proc.body ⟨σ_entry, fac⟩ σ_exit emitted →
    Procedure.outputAsPredicate proc
      { store := σ_exit, factory := fac }

/-- A havoc keeps the declared sort of every variable: a value of sort `ty` before the havoc
    becomes a value of the same sort after it, since each havocked value shares a type with the
    value it replaces. -/
private theorem sortAt_of_havocVars {fac : Expression.Factory} {σ σ' : CoreStore}
    {xs : List Expression.Ident} (h : HavocVars fac σ xs σ') :
    ∀ id ty, (∃ v, σ id = some v ∧ Procedure.valueHasType ty v) →
      ∃ v, σ' id = some v ∧ Procedure.valueHasType ty v := by
  induction h with
  | update_none => exact fun _ _ h => h
  | @update_some τ x v τ' _ _ _ hu hst _ ih =>
    intro id ty ⟨w, hw, hty⟩
    refine ih id ty ?_
    obtain ⟨_, hx', hfr⟩ := hu
    rcases Classical.em (x = id) with rfl | hne
    · obtain ⟨prev, ty', hprev, ⟨-, hp⟩, ⟨-, hv⟩⟩ := hst
      cases hprev.symm.trans hw
      exact ⟨v, hx', (Option.some.inj (hv.symm.trans hp)).trans hty⟩
    · exact ⟨w, (hfr id hne).trans hw, hty⟩

/-- **A procedure call meets a Hoare triple built from its callee's contract.**

    When the callee named `procName` meets its `contractTriple` and every execution
    respects the output write set and declared output types, the call satisfies a
    `Triple`.  The call runs the instance of the callee at its type arguments
    (`Calls.typeInstantiatedCallee`), and the premises below are stated of that instance, which
    meets the contract as `contractTriple` requires of every instance.
    `hentry` establishes the contract precondition shared by both body kinds,
    which includes the callee's output typing at entry, and, depending on the resolved
    body, the structured block gate or the CFG gate.
    `haxioms` establishes, at the callee's entry, the axioms and `distinct`
    declarations visible to the callee, which its `contractTriple` assumes;
    `Core.Specification.AxiomsBeforeProcedureDecl.callee` gives it from the caller's
    entry when they read no variable and the callee is declared no later.
    `hexit` receives caller command well-formedness, `CallEntry`, the callee entry
    store, output typing, `Procedure.storeFrame`, and restoration of the entry factory,
    so it may relate caller actuals to preserved input-only formals before deriving the
    caller's postcondition. The CFG `contractTriple` already checks its
    postcondition on the projected final store, so no separate projection
    hypothesis is needed. For an opaque callee (`Body.isOpaque`) the call havocs the outputs and
    assumes the postconditions: the havoc keeps the declared output types that `contractPre`
    gives at the entry store, and the assumed postconditions give the contract postcondition, so
    `hentry` asks nothing more of an opaque callee. -/
theorem Procedure.call_of_contract (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) {tyArgs : Option (List Expression.Ty)}
    (callArgs : List (Imperative.CallArg Expression)) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hcontract : Procedure.contractTriple p params procName)
    (hframe : ∀ proc,
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      Procedure.bodyFrame p.findProcByString? proc)
    (houtputs : ∀ proc,
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      Procedure.bodyOutputsTyped (p.factoryBeforeProcedure procName)
        p.findProcByString? proc)
    (hentry : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Procedure.contractPre (p.factoryBeforeProcedure procName) proc
          { store := σAO, factory := ρ₀.factory } ∧
        if proc.body.isOpaque = Bool.true then True
        else match proc.body with
          | .structured bss _ =>
              BlockInitEnvWF params [Imperative.Stmt.block "" bss #[]]
                { store := σAO, factory := ρ₀.factory }
          | .cfg cfg _ =>
              CFGInitEnvWF params cfg
                { store := σAO, factory := ρ₀.factory }
          | .abstract => True)
    (haxioms : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Core.Specification.AxiomsBeforeProcedureDecl procName p
        { store := σAO, factory := ρ₀.factory })
    (hexit : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (ρ' : Imperative.Env Expression) (σ' σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      Procedure.contractPost (p.factoryBeforeProcedure procName) proc ρ' →
      Procedure.outputAsPredicate proc ρ' →
      ρ'.factory = ρ₀.factory →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Procedure.storeFrame proc σAO ρ'.store →
      CallExit ρ₀.factory ρ₀.store proc callArgs ρ'.store σ' →
      Post { ρ₀ with store := σ' }) :
    Triple p.findProcByString? params Pre
      [Statement.call procName tyArgs callArgs md] Post
      (factory := p.factoryBeforeProcedure procName) := by
  obtain ⟨cproc₀, hcproc₀, hinsts⟩ := hcontract
  refine cmd (factory := p.factoryBeforeProcedure procName)
    p.findProcByString? params
    (Imperative.CmdExt.call procName tyArgs callArgs md)
    Pre Post (fun ρ₀ σ' emitted hpre hwf hstep => ?_)
  let I := DenoteBasedInterp (p.factoryBeforeProcedure procName)
  cases hstep with
  | @call_sem _ _ _ cproc _ _ _ _ _ _ σAO hcproc hno hcallentry hbodyE hcallexit =>
    -- The call runs an instance of the callee, which meets the callee's contract.
    obtain ⟨-, htriple⟩ : Procedure.contractChecksTyped cproc ∧ _ := by
      have hinst := hcproc
      simp only [Calls.typeInstantiatedCallee, hcproc₀, Option.bind_some] at hinst
      exact hinsts _ _ hinst
    have hframeRel := hframe cproc hcproc _ _ _ _ hbodyE
    obtain ⟨hcontractPre, hbodyWF⟩ :=
      hentry ρ₀ cproc _ hpre hwf hcproc hcallentry
    have hax := haxioms ρ₀ cproc _ hpre hwf hcproc hcallentry
    have houtputsRel := houtputs cproc hcproc _ _ _ _ hcontractPre.2.1
      hcontractPre.2.2.2.1 hbodyE
    -- The precondition assertions are valid once, independent of the body kind.
    have hvalidA :
        Trace.AssertionsValid Expression I
          (defaultAssertEvents ρ₀.factory σAO (Calls.checksAtCall md cproc.spec.preconditions)) :=
      assertionsValid_defaultAssertEvents I ρ₀.factory σAO _
        (fun label check hmem _ => by
          obtain ⟨c₀, hmem₀, hexpr, -⟩ := Calls.mem_checksAtCall hmem
          exact Procedure.checkAsPredicate_of_exprEq label check hcontractPre.2.1 hexpr.symm
            (hcontractPre.1 label c₀ hmem₀))
    -- Shared proof tail: given the body triple's conclusion about a post-env
    -- `ρpost` whose store is the callee's final store, discharge the call's
    -- obligation.  Both body kinds instantiate it, differing only in `ρpost`.
    have finish : ∀ (ρpost : Imperative.Env Expression) (bodyEvents : Trace Expression),
        ρpost.factory = ρ₀.factory →
        Procedure.outputAsPredicate cproc ρpost →
        Procedure.storeFrame cproc σAO ρpost.store →
        CallExit ρ₀.factory ρ₀.store cproc callArgs ρpost.store σ' →
        (Trace.AssertionsValid Expression I bodyEvents ∧
          (Trace.Reachable Expression I bodyEvents →
            Procedure.contractPost (p.factoryBeforeProcedure procName) cproc ρpost)) →
        Trace.AssertionsValid Expression I
            (defaultAssertEvents ρ₀.factory σAO (Calls.checksAtCall md cproc.spec.preconditions) ++
              bodyEvents ++
              defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions) ∧
          (Trace.Reachable Expression I
              (defaultAssertEvents ρ₀.factory σAO
                  (Calls.checksAtCall md cproc.spec.preconditions) ++
                bodyEvents ++
                defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions) →
            Post { ρ₀ with store := σ' }) := by
      intro ρpost bodyEvents hρpostfac houtputsρ hframeρ hcallexitρ htb
      have hvalidB : Procedure.postAsPredicate (p.factoryBeforeProcedure procName) cproc ρpost →
          Trace.AssertionsValid Expression I
            (defaultAssertEvents ρ₀.factory ρpost.store cproc.spec.postconditions) := by
        intro hpostC
        refine assertionsValid_defaultAssertEvents I ρ₀.factory ρpost.store
          cproc.spec.postconditions (fun label check hmem hattr world => ?_)
        have h := hpostC label check hmem hattr world
        rw [hρpostfac] at h
        exact h
      refine ⟨?_, ?_⟩
      · refine Trace.AssertionsValid.append_of_reachable_left I
          (Trace.AssertionsValid.append_of_reachable_left I hvalidA (fun _ => htb.1)) ?_
        exact fun hreachAB => hvalidB (htb.2 (Trace.Reachable.right_of_append I hreachAB))
      · intro hreach
        exact hexit ρ₀ cproc ρpost σ' _ hpre hwf hcproc
          (htb.2 (Trace.Reachable.right_of_append I
            (Trace.Reachable.left_of_append I hreach)))
          houtputsρ hρpostfac hcallentry hframeρ hcallexitρ
    simp only [hno, Bool.false_eq_true, ↓reduceIte] at hbodyWF
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
        have htb := Strata.Logic.Hoare.TripleWith.run htriple
          { store := σAO, factory := ρ₀.factory }
          ρ' _ ⟨hcontractPre, hax⟩ hbodyWF (Or.inl hrun')
        exact finish ρ' _ hρ'fac houtputsRel hframeRel hcallexit htb
    | cfg cfg =>
      rw [hcbody] at hbodyE htriple hbodyWF
      cases hbodyE with
      | cfg hrun =>
        rename_i ρ'
        have hρ'fac : ρ'.factory = ρ₀.factory :=
          (StepCFGStarE.preserves_factory hrun).symm
        have htb := Strata.Logic.Hoare.TripleWith.run
          (htriple { store := σAO, factory := ρ₀.factory })
          { store := σAO, factory := ρ₀.factory }
          ρ' _ ⟨⟨hcontractPre, hax⟩, rfl⟩ hbodyWF (Or.inl hrun)
        exact finish { ρ' with store := Imperative.projectStore σAO ρ'.store } _
          hρ'fac houtputsRel hframeRel hcallexit htb
    | abstract =>
      rw [hcbody] at hbodyE
      cases hbodyE
  | @call_abstract_sem _ σO _ _ cproc _ _ _ _ σAO hcproc hab hcallentry hhavoc hcallexit =>
    obtain ⟨hcontractPre, -⟩ := hentry ρ₀ cproc _ hpre hwf hcproc hcallentry
    have hout : Procedure.outputAsPredicate cproc { store := σO, factory := ρ₀.factory } :=
      fun id ty hmem => sortAt_of_havocVars hhavoc id ty (hcontractPre.2.2.2.2 id ty hmem)
    have hvalidA :
        Trace.AssertionsValid Expression I
          (defaultAssertEvents ρ₀.factory σAO (Calls.checksAtCall md cproc.spec.preconditions)) :=
      assertionsValid_defaultAssertEvents I ρ₀.factory σAO _
        (fun label check hmem _ => by
          obtain ⟨c₀, hmem₀, hexpr, -⟩ := Calls.mem_checksAtCall hmem
          exact Procedure.checkAsPredicate_of_exprEq label check hcontractPre.2.1 hexpr.symm
            (hcontractPre.1 label c₀ hmem₀))
    refine ⟨Trace.AssertionsValid.append_of_reachable_left I hvalidA
      (fun _ => Trace.AssertionsValidFrom.of_forall_assume I fun _ he => by
        simp only [Calls.assumeEvents, List.mem_map] at he
        obtain ⟨_, -, rfl⟩ := he
        exact ⟨_, rfl⟩), fun ⟨w, hw⟩ => ?_⟩
    refine hexit ρ₀ cproc { store := σO, factory := ρ₀.factory } σ' σAO hpre hwf hcproc
      (fun label check hmem _ world => ?_) hout rfl hcallentry
      (invStoresExceptComm (InvStoresExceptHavocVars InvStoresExceptEmpty hhavoc)) hcallexit
    have hmem' : Event.assume ⟨ρ₀.factory, σO, label, check.expr, check.md⟩ ∈
        assumeEvents ρ₀.factory σO cproc.spec.postconditions := by
      simp only [assumeEvents, Calls.assumeEvents]
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
    rcases hw _ (List.mem_append_right _ hmem') with h | ⟨hne, -⟩
    · exact .inl h
    · exact absurd hcontractPre.2.1 hne

end Hoare

namespace HoareTotal

/-- **A procedure call meets a total-correctness Hoare triple built from its callee's
    contract.**

    The runs are those of `Hoare.Procedure.call_of_contract`, which takes the same
    `hcontract`, `hframe`, `houtputs`, `hentry`, `haxioms` and `hexit` premises, and which
    gives the validity of the assertions a call emits.  A call runs its callee's body to
    completion within one step, so the call then terminates with valid assertions as soon as it
    can execute.  The further premises make sure it can: `hcallee` that the call's type
    arguments instantiate the callee (`Calls.typeInstantiatedCallee`), and `hcallEntry` that
    the call has a callee entry store. For a callee that is not opaque (`Body.isOpaque`), the
    call runs its body: `hbodyRun` gives a finished run of the body from the entry store, and
    `hcallExit` a write-back from the final store of every such run.  The callee's other runs
    do not matter to the call's termination; a proof of `hbodyRun` may use the callee's
    `contractTripleTotal`, which gives a finished run when no `assume` of the body can fail.
    For an opaque callee, the call runs its contract (`EvalCmdExtE.call_abstract_sem`): the
    havoc of the outputs can keep their entry values, since each of them holds a value of its
    declared type at the entry store (`contractPre`, with the store values that `InitEnvWF`
    makes well formed), and `hcallExitOpaque` gives a write-back from that store. The
    postconditions are assumed, and an assumption does not block a run, so the call terminates
    without any premise on them. -/
theorem Procedure.call_of_contract (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) {tyArgs : Option (List Expression.Ty)}
    (callArgs : List (Imperative.CallArg Expression)) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hcontract : Hoare.Procedure.contractTriple p params procName)
    (hcallee : ∃ proc, Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc)
    (hframe : ∀ proc,
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      Hoare.Procedure.bodyFrame p.findProcByString? proc)
    (houtputs : ∀ proc,
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      Hoare.Procedure.bodyOutputsTyped (p.factoryBeforeProcedure procName)
        p.findProcByString? proc)
    (hentry : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Hoare.Procedure.contractPre (p.factoryBeforeProcedure procName) proc
          { store := σAO, factory := ρ₀.factory } ∧
        if proc.body.isOpaque = Bool.true then True
        else match proc.body with
          | .structured bss _ =>
              BlockInitEnvWF params [Imperative.Stmt.block "" bss #[]]
                { store := σAO, factory := ρ₀.factory }
          | .cfg cfg _ =>
              CFGInitEnvWF params cfg
                { store := σAO, factory := ρ₀.factory }
          | .abstract => True)
    (haxioms : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Core.Specification.AxiomsBeforeProcedureDecl procName p
        { store := σAO, factory := ρ₀.factory })
    (hexit : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure)
        (ρ' : Imperative.Env Expression) (σ' σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      Hoare.Procedure.contractPost (p.factoryBeforeProcedure procName) proc ρ' →
      Hoare.Procedure.outputAsPredicate proc ρ' →
      ρ'.factory = ρ₀.factory →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      Hoare.Procedure.storeFrame proc σAO ρ'.store →
      CallExit ρ₀.factory ρ₀.store proc callArgs ρ'.store σ' →
      Post { ρ₀ with store := σ' })
    (hcallEntry : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      ∃ σAO, CallEntry ρ₀.factory ρ₀.store proc callArgs σAO)
    (hbodyRun : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure) (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      proc.body.isOpaque = Bool.false →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      ∃ σEnd bodyEvents,
        CoreBodyExecE p.findProcByString? proc.body ⟨σAO, ρ₀.factory⟩ σEnd bodyEvents)
    (hcallExit : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure) (σAO σEnd : CoreStore)
        (bodyEvents : Trace Expression),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      CoreBodyExecE p.findProcByString? proc.body ⟨σAO, ρ₀.factory⟩ σEnd bodyEvents →
      ∃ σ', CallExit ρ₀.factory ρ₀.store proc callArgs σEnd σ')
    (hcallExitOpaque : ∀ (ρ₀ : Imperative.Env Expression) (proc : Procedure) (σAO : CoreStore),
      Pre ρ₀ → InitEnvWF params (Statement.call procName tyArgs callArgs md) ρ₀ →
      Calls.typeInstantiatedCallee p.findProcByString? procName tyArgs = some proc →
      proc.body.isOpaque = Bool.true →
      CallEntry ρ₀.factory ρ₀.store proc callArgs σAO →
      ∃ σ', CallExit ρ₀.factory ρ₀.store proc callArgs σAO σ') :
    Triple p.findProcByString? params Pre
      [Statement.call procName tyArgs callArgs md] Post
      (factory := p.factoryBeforeProcedure procName) :=
  cmd (factory := p.factoryBeforeProcedure procName) p.findProcByString? params _ Pre Post
    (fun ρ₀ hpre hwf => by
      obtain ⟨cproc, hcproc⟩ := hcallee
      obtain ⟨σAO, hce⟩ := hcallEntry ρ₀ cproc hpre hwf hcproc
      cases ho : cproc.body.isOpaque
      · obtain ⟨σEnd, bodyEvents, hb⟩ := hbodyRun ρ₀ cproc σAO hpre hwf hcproc ho hce
        obtain ⟨σ', hcx⟩ := hcallExit ρ₀ cproc σAO σEnd bodyEvents hpre hwf hcproc hce hb
        exact ⟨σ', _, .call_sem hcproc ho hce hb hcx⟩
      · obtain ⟨σ', hcx⟩ := hcallExitOpaque ρ₀ cproc σAO hpre hwf hcproc ho hce
        obtain ⟨⟨-, -, -, -, hout⟩, -⟩ := hentry ρ₀ cproc σAO hpre hwf hcproc hce
        have htyped : ∀ x ∈ ProcedureHeader.outputParams (P := Expression) cproc.header,
            ∃ v ty, σAO x = some v ∧ HasVal.valueOfTy ρ₀.factory v ty := by
          obtain ⟨ins, outs, hev, hrd, hfr⟩ := hce
          obtain ⟨-, -, rfl⟩ := Imperative.Calls.callEntryStore_of_initCallFrame cproc ins outs _ hfr
          have hws := Imperative.Calls.wellFormedStore_callEntryStore (f := ρ₀.factory) cproc ins
            outs (evalExpressions_values hwf.val hwf.storeWellDefined hev) (readValues_values hrd)
          intro x hx
          have hk : x ∈ ListMap.keys cproc.header.outputs := hx
          obtain ⟨⟨_, ty⟩, hmem, rfl⟩ := List.mem_map.1 (ListMap.keys_eq_map_fst _ ▸ hk)
          obtain ⟨v, hv, hvt⟩ := hout _ ty hmem
          exact ⟨v, .forAll [] ty, hv, hws _ v hv, by
            simp only [Hoare.Procedure.valueHasType] at hvt
            simp [hvt, Lambda.LTy.toMonoType?]⟩
        exact ⟨σ', _, .call_abstract_sem hcproc ho hce (HavocVarsId htyped) hcx⟩)
    (Hoare.Procedure.call_of_contract p params procName callArgs md Pre Post hcontract hframe
      houtputs hentry haxioms hexit)

end HoareTotal

end Core.Logic

end -- public section

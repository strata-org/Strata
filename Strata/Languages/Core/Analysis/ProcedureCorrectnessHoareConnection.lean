/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Analysis.ProcedureCorrectness
public import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProcedureProps
import all Strata.DL.Lambda.LTy

/-! # Procedure correctness from a contract triple

`Procedure.contractTriple` and `ProcedureAssertsValidOnTraces.denote` read the same
executions of the body through the same interpretation: both ask for the validity of every
assertion of every finite execution, finished or not, and both ask for the postconditions
of every finished run. The entry environments of the latter (`ProcEntryEnv`) satisfy the
precondition of the former, so a proved triple gives procedure correctness.  For example, a
body `assert false; while (true) {}` meets neither.

## Key results

- `ProcEntryEnv.contractPre`: an entry environment of procedure correctness satisfies
  the precondition of `Procedure.contractTriple`.
- `contract_of_contractTriple`: a proved `Procedure.contractTriple` gives the
  `contract` field of `ProcedureAssertsValidOnTraces.denote`.
- `assertsValid_of_contractTriple`: it gives the `assertsValid` field.
- `procedureAssertsValidOnTraces_of_contractTriple`: it gives
  `ProcedureAssertsValidOnTraces.denote`.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-- An entry environment of procedure correctness satisfies the precondition of
    `Procedure.contractTriple`: the contract precondition over the factory visible
    before the procedure, and the axioms and `distinct` declarations visible to it. -/
theorem ProcEntryEnv.contractPre {params : InitEnvWFParams} {entryProcName : String}
    {p : Program} {proc : Procedure} {ρ₀ : Imperative.Env Expression}
    (h : ProcEntryEnv params entryProcName p proc ρ₀) :
    Hoare.Procedure.contractPre (p.factoryBeforeProcedure entryProcName) proc ρ₀ ∧
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ := by
  obtain ⟨hwf, hax, hfac⟩ := h
  refine ⟨⟨?_, hfac, ?_, ?_, ?_⟩, hax⟩
  · intro label check hmem world
    exact Or.inl ⟨hfac, hwf.preconditionsHold label check hmem⟩
  · intro id hid
    exact (hwf.oldInoutMatchesInout id hid).symm
  · intro id ty hmem
    obtain ⟨v, hv, -, hty⟩ := hwf.inputTyped hmem
    simp only [Lambda.LTy.toMonoType?, Option.some.injEq] at hty
    exact ⟨v, hv, hty.symm⟩
  · intro id ty hmem
    obtain ⟨v, hv, -, hty⟩ := hwf.outputTyped hmem
    simp only [Lambda.LTy.toMonoType?, Option.some.injEq] at hty
    exact ⟨v, hv, hty.symm⟩

/-- The triple a proved `Procedure.contractTriple` asserts about a structured body declaring
    variables only at monotypes: that of its instance at its own type parameters, which differs
    from it only in having none. -/
private theorem triple_of_contractTriple {params : InitEnvWFParams} {entryProcName : String}
    {p : Program} (h : Hoare.Procedure.contractTriple p params entryProcName)
    {proc : Procedure} {ss : Statements}
    (hproc : p.findProcByString? entryProcName = some proc)
    (hbody : proc.body = .structured ss opq) (hinits : proc.initTypesMono = Bool.true) :
    Hoare.Triple p.findProcByString? params
      (fun ρ => Hoare.Procedure.contractPre (p.factoryBeforeProcedure entryProcName) proc ρ ∧
        AxiomsBeforeProcedureDecl entryProcName p ρ)
      [Stmt.block "" ss #[]]
      (Hoare.Procedure.contractPost (p.factoryBeforeProcedure entryProcName) proc)
      (factory := p.factoryBeforeProcedure entryProcName) := by
  obtain ⟨proc', hproc', hinsts⟩ := h
  obtain rfl : proc = proc' := Option.some.inj (hproc.symm.trans hproc')
  -- The instance at the procedure's own type parameters reads the same contract and body.
  obtain ⟨-, htriple⟩ := hinsts _ _ (Procedure.instantiateTypes_own_typeArgs proc hinits)
  change match proc.body with
    | .structured bss _ => Hoare.Triple p.findProcByString? params
        (fun ρ => Hoare.Procedure.contractPre (p.factoryBeforeProcedure entryProcName) proc ρ ∧
          AxiomsBeforeProcedureDecl entryProcName p ρ)
        [Stmt.block "" bss #[]]
        (Hoare.Procedure.contractPost (p.factoryBeforeProcedure entryProcName) proc)
        (factory := p.factoryBeforeProcedure entryProcName)
    | .cfg _ _ => _
    | .abstract => _ at htriple
  rw [hbody] at htriple
  exact htriple

/-- **A proved contract triple gives the contract of procedure correctness.** From every entry
    environment `ProcEntryEnv` admits, every finished run of the body, followed by the
    procedure's non-free postconditions as assertions, is assertion-valid: the `contract` field
    of `ProcedureAssertsValidOnTraces.denote`, for a procedure whose body declares variables
    only at monotypes, as every type-checked one does.  For a polymorphic procedure, this is the
    triple of its instance at its own type parameters, which differs from it only in having
    none. -/
theorem contract_of_contractTriple {params : InitEnvWFParams} {entryProcName : String}
    {p : Program} (h : Hoare.Procedure.contractTriple p params entryProcName)
    (proc : Procedure) (ss : Statements)
    (hproc : p.findProcByString? entryProcName = some proc)
    (hbody : proc.body = .structured ss opq) (hinits : proc.initTypesMono = Bool.true)
    (ρ₀ ρ' : Imperative.Env Expression) (trace : Trace Expression)
    (hentry : ProcEntryEnv params entryProcName p proc ρ₀)
    (hrun : (Core.Logic.EventLang.coreBlock p.findProcByString?).TerminatesAt
      [Stmt.block "" ss #[]] ρ₀ trace ρ') :
    Trace.AssertionsValid Expression
      (DenoteBasedInterp (p.factoryBeforeProcedure entryProcName))
      (trace ++ postconditionEvents proc ρ') := by
  obtain ⟨hvalid, hpost⟩ := Strata.Logic.Hoare.TripleWith.run
    (triple_of_contractTriple h hproc hbody hinits) ρ₀ ρ' trace hentry.contractPre
    (hentry.1.structuredBodyWF ss _ hbody) hrun
  exact Trace.AssertionsValid.append_of_reachable_left _ hvalid fun hreach =>
    Hoare.assertionsValid_defaultAssertEvents _ ρ'.factory ρ'.store
      proc.spec.postconditions (hpost hreach)

/-- **A proved contract triple validates every assertion of the procedure's body.**  From every
    entry environment `ProcEntryEnv` admits, every occurrence of every assertion on every finite
    execution of the body, finished or not, is valid: the `assertsValid` field of
    `ProcedureAssertsValidOnTraces.denote`, for a procedure whose body declares variables only
    at monotypes.  A finite execution of the body's block is one of the one-element list the
    triple speaks of. -/
theorem assertsValid_of_contractTriple {params : InitEnvWFParams} {entryProcName : String}
    {p : Program} (h : Hoare.Procedure.contractTriple p params entryProcName)
    {proc : Procedure} {ss : Statements}
    (hproc : p.findProcByString? entryProcName = some proc)
    (hbody : proc.body = .structured ss opq) (hinits : proc.initTypesMono = Bool.true)
    (a : Imperative.AssertId Expression) :
    AssertValidOnTracesInProcedure (DenoteBasedInterp (p.factoryBeforeProcedure entryProcName))
      params entryProcName p a := by
  refine ⟨proc, ss, opq, hproc, hbody, fun ρ₀ cfg trace hentry hrun => ?_⟩
  have hblock : (Core.Logic.EventLang.coreBlock p.findProcByString?).traceStar
      ((Core.Logic.EventLang.coreBlock p.findProcByString?).stmtCfg [Stmt.block "" ss #[]] ρ₀)
      trace (.seq cfg []) := by
    show ReflTransTrace (StepStmtE Expression (EvalCommandE p.findProcByString?))
      (.stmts [Stmt.block "" ss #[]] ρ₀) trace (.seq cfg [])
    simpa using ReflTransTrace.step _ [] _ _ _
      (.step_stmts_cons : StepStmtE Expression (EvalCommandE p.findProcByString?) _ _ _)
      (seq_inner_starE (EvalCommandE p.findProcByString?) (ss := []) hrun)
  exact Trace.AssertionValid.of_assertionsValid _ a
    (((triple_of_contractTriple h hproc hbody hinits) ρ₀ hentry.contractPre
      (hentry.1.structuredBodyWF ss _ hbody)).1 _ trace hblock)

/-- **A proved contract triple gives the deductive correctness of the procedure.**  For a
    procedure with a structured body declaring variables only at monotypes, as every
    type-checked one does, `Procedure.contractTriple` gives
    `ProcedureAssertsValidOnTraces.denote`: every assertion of every finite execution of the
    body is valid (`assertsValid_of_contractTriple`), and every finished run meets the
    contract (`contract_of_contractTriple`). -/
theorem procedureAssertsValidOnTraces_of_contractTriple {params : InitEnvWFParams}
    {entryProcName : String} {p : Program}
    (h : Hoare.Procedure.contractTriple p params entryProcName)
    {proc : Procedure} {ss : Statements}
    (hproc : p.findProcByString? entryProcName = some proc)
    (hbody : proc.body = .structured ss opq) (hinits : proc.initTypesMono = Bool.true) :
    ProcedureAssertsValidOnTraces.denote params entryProcName p where
  procedureExists := ⟨proc, hproc⟩
  assertsValid := assertsValid_of_contractTriple h hproc hbody hinits
  contract := fun proc' ss' opq' hproc' hbody' => by
    obtain rfl : proc = proc' := Option.some.inj (hproc.symm.trans hproc')
    rw [hbody] at hbody'
    cases hbody'
    exact contract_of_contractTriple h proc ss hproc hbody hinits

end Core.Specification

end -- public section

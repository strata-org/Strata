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

`Procedure.contractTriple` and the contract of `ProcedureAssertsValidOnTraces.denote`
read the same finished runs of the body through the same interpretation. The entry
environments of the latter (`ProcEntryEnv`) satisfy the precondition of the former,
so a proved triple gives the contract. The other part of
`ProcedureAssertsValidOnTraces`, validity of every assertion on every prefix of a
run, also covers runs that never finish and needs termination
(`triple_implies_assertValidOnTracesWhen`).

## Key results

- `ProcEntryEnv.contractPre`: an entry environment of procedure correctness satisfies
  the precondition of `Procedure.contractTriple`.
- `contract_of_contractTriple`: a proved `Procedure.contractTriple` gives the
  `contract` field of `ProcedureAssertsValidOnTraces.denote`.
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
    (hbody : proc.body = .structured ss) (hinits : proc.initTypesMono = Bool.true)
    (ρ₀ ρ' : Imperative.Env Expression) (trace : Trace Expression)
    (hentry : ProcEntryEnv params entryProcName p proc ρ₀)
    (hrun : (Core.Logic.EventLang.coreBlock p.findProcByString?).TerminatesAt
      [Stmt.block "" ss #[]] ρ₀ trace ρ') :
    Trace.AssertionsValid Expression
      (DenoteBasedInterp (p.factoryBeforeProcedure entryProcName))
      (trace ++ postconditionEvents proc ρ') := by
  obtain ⟨proc', hproc', hinsts⟩ := h
  obtain rfl : proc = proc' := Option.some.inj (hproc.symm.trans hproc')
  -- The instance at the procedure's own type parameters reads the same contract and body.
  obtain ⟨-, htriple⟩ := hinsts _ _ (Procedure.instantiateTypes_own_typeArgs proc hinits)
  change match proc.body with
    | .structured bss => Hoare.Triple p.findProcByString? params
        (fun ρ => Hoare.Procedure.contractPre (p.factoryBeforeProcedure entryProcName) proc ρ ∧
          AxiomsBeforeProcedureDecl entryProcName p ρ)
        [Stmt.block "" bss #[]]
        (Hoare.Procedure.contractPost (p.factoryBeforeProcedure entryProcName) proc)
        (factory := p.factoryBeforeProcedure entryProcName)
    | .cfg _ => _ at htriple
  rw [hbody] at htriple
  obtain ⟨hvalid, hpost⟩ :=
    htriple ρ₀ ρ' trace hentry.contractPre (hentry.1.structuredBodyWF ss hbody) hrun
  exact Trace.AssertionsValid.append_of_reachable_left _ hvalid fun hreach =>
    Hoare.assertionsValid_defaultAssertEvents _ ρ'.factory ρ'.store
      proc.spec.postconditions (hpost hreach)

end Core.Specification

end -- public section

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreSpecification
public import Strata.DL.Imperative.Analysis.Assertions
public import Strata.DL.Imperative.Logic.Termination
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.Languages.Core.Logic.FactoryInterp

public section

/-! # Correctness of Core procedures and of Core's verifier

- **`ProcedureAssertsValidOnTraces`**, **`ProcedureAssertsSatisfiableOnTraces`** —
  assertion validity or satisfiability plus postconditions on event traces,
  read through a `ConditionInterp`. A trace
  records the assertions of every callee call that completes, so validity covers
  those transitively; a call whose callee never finishes contributes no events.
  The valid form checks the procedure's contract by reading its non-free
  postconditions as assertions appended to each finished run's trace.
- **`ProcedureAssertsValidOnTraces.denote`**,
  **`ProcedureAssertsSatisfiableOnTraces.denote`** — the same properties with
  conditions read by Lambda's denotational semantics over the factory visible
  before the entry procedure.
- **`CoreVerifierModel`** — the desirable property of Core's verifier under each
  verification mode.
-/

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ## Procedure correctness -/


/-- The initial environments a procedure body is verified from: `ProcEnvWF`, the
    axioms and distincts visible to `entryProcName`, and a runtime factory over the
    factory visible before the procedure (`Program.factoryBeforeProcedure`), as in
    `Procedure.contractTriple`. Steps keep the factory, so every condition a run from
    such an environment captures is over that factory. -/
@[expose] def ProcEntryEnv (params : InitEnvWFParams) (entryProcName : String)
    (p : Program) (proc : Procedure) (ρ₀ : Imperative.Env Expression) : Prop :=
  ProcEnvWF params proc ρ₀ ∧ AxiomsBeforeProcedureDecl entryProcName p ρ₀ ∧
    ρ₀.factory.factory = p.factoryBeforeProcedure entryProcName

/-- Common shape of Core-level assertion specifications on a procedure named
    `entryProcName` in program `p`: `Spec` is asked of the body from the entry
    environments `ProcEntryEnv` admits. -/
@[expose] def AssertSpecInProcedure (params : InitEnvWFParams)
    (Spec : (Imperative.Env Expression → Prop) → Statements → Statement → Prop)
    (entryProcName : String) (p : Program) : Prop :=
  ∃ proc ss,
    p.findProcByString? entryProcName = some proc ∧
    proc.body = .structured ss ∧
    Spec (ProcEntryEnv params entryProcName p proc) ss (Stmt.block "" ss #[])

/-! ## Procedure correctness on event traces

The definitions below state procedure correctness over the event-trace semantics
`EventLang.core`. A run's trace records each assertion and assumption it
executes, including those of its callees: a call emits the callee's
non-free preconditions, the callee body's events, and its non-free
postconditions. Validity is therefore checked at every assertion a run reaches,
transitively, under the assumptions that precede it, and conditions are read
through a `ConditionInterp` rather than fixed to the evaluator.

A call is a single step that runs the callee body to completion (`BigStepE`),
so its events appear in a trace only if the callee finishes. A call whose callee
never finishes contributes no events, not even its precondition checks: the
caller's runs end before the call. For example, with

```
procedure Q() { assert false; while true {}; };
procedure P() { call Q(); };
```

no trace of `P` contains `Q`'s `assert false`, so `P` satisfies
`ProcedureAssertsValidOnTraces`. The assertion is checked when `Q` is itself an
entry procedure: its own body's runs reach it. So the guarantee covers what a
nonterminating callee does only through that callee's own correctness. -/

variable (I : ConditionInterp Expression)

/-- The events the body's caller observes after the body terminates in `ρ'`:
    the procedure's non-free postconditions, as the call rule emits them. -/
@[expose] def postconditionEvents (proc : Procedure) (ρ' : Imperative.Env Expression) :
    Trace Expression :=
  defaultAssertEvents ρ'.factory ρ'.store proc.spec.postconditions

/-- Assertion `a` is valid on every trace of the procedure named
    `entryProcName`, from entry environments satisfying `ProcEntryEnv`. -/
@[expose] def AssertValidOnTracesInProcedure (params : InitEnvWFParams)
    (entryProcName : String) (p : Program)
    (a : Imperative.AssertId Expression) : Prop :=
  AssertSpecInProcedure params
    (fun Pre _ss s =>
      Imperative.Specification.AssertValidOnTracesWhen
        (Core.Logic.EventLang.core p.findProcByString?) I Pre s a)
    entryProcName p

/-- Assertion `a`, when it occurs in the body, holds on some trace of the
    procedure named `entryProcName` under the assumptions preceding it. -/
@[expose] def AssertSatisfiableOnTracesInProcedure (params : InitEnvWFParams)
    (entryProcName : String) (p : Program)
    (a : Imperative.AssertId Expression) : Prop :=
  AssertSpecInProcedure params
    (fun Pre ss s =>
      a ∈ Statements.collectAssertIds ss →
      Imperative.Specification.AssertSatisfiableOnTracesWhen
        (Core.Logic.EventLang.core p.findProcByString?) I Pre s a)
    entryProcName p

/-- Deductive correctness of the procedure named `entryProcName` on event
    traces: every assertion any run of the body reaches is valid, and the body
    meets the procedure's contract.

    The two parts differ in which runs they read. The first quantifies over every
    finite prefix of the body's runs, so it covers runs that never finish; a
    partial-correctness contract says nothing about those. The prefixes are those
    of `EventLang.core`, where a call runs its callee to completion in one step,
    so they do not include prefixes inside a callee that never finishes (see the
    section comment above). The second is the contract: from an entry
    environment satisfying `ProcEntryEnv`, every run that finishes, normally or
    by an exit, is followed by the non-free postconditions as its caller observes
    them (`postconditionEvents`), and the whole trace is assertion-valid. So each
    postcondition holds in every world that satisfies the run's assumptions.

    The contract reads postconditions through `I`, as the body's own assertions
    are, rather than through a separate predicate on the final environment. With
    an interpretation whose worlds differ, such as one quantifying over
    valuations, this is what lets the postconditions share the world of the
    run's assumptions. -/
structure ProcedureAssertsValidOnTraces (params : InitEnvWFParams)
    (entryProcName : String) (p : Program) : Prop where
  /-- The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  assertsValid : ∀ a, AssertValidOnTracesInProcedure I params entryProcName p a
  contract : ∀ proc ss, p.findProcByString? entryProcName = some proc →
    proc.body = .structured ss →
    ∀ (ρ₀ ρ' : Imperative.Env Expression) (trace : Trace Expression),
      ProcEntryEnv params entryProcName p proc ρ₀ →
      (Core.Logic.EventLang.coreBlock p.findProcByString?).TerminatesAt
        [Stmt.block "" ss #[]] ρ₀ trace ρ' →
      Trace.AssertionsValid Expression I (trace ++ postconditionEvents proc ρ')

/-- The existential dual of `ProcedureAssertsValidOnTraces`, for bug finding:
    each assertion in the body holds on some trace, and some terminating run
    has every assertion it reaches and every non-free postcondition holding in
    one world that also satisfies its assumptions. -/
structure ProcedureAssertsSatisfiableOnTraces (params : InitEnvWFParams)
    (entryProcName : String) (p : Program) : Prop where
  /-- The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  assertsSatisfiable : ∀ a, AssertSatisfiableOnTracesInProcedure I params entryProcName p a
  postconditionsSatisfiable : ∀ proc ss, p.findProcByString? entryProcName = some proc →
    proc.body = .structured ss →
    ∃ (ρ₀ ρ' : Imperative.Env Expression) (trace : Trace Expression) (world : I.World),
      ProcEntryEnv params entryProcName p proc ρ₀ ∧
      CoreStepStarE p.findProcByString? (.stmt (Stmt.block "" ss #[]) ρ₀) trace
        (.terminal ρ') ∧
      Trace.AssumptionsHold Expression I world trace ∧
      ∀ condition, Event.assert condition ∈ trace ++ postconditionEvents proc ρ' →
        I.holds world condition

/-! ## Procedure correctness read by denotation

Core reads conditions by Lambda's denotational semantics (`DenoteBasedInterp`)
over the factory visible before the entry procedure, matching
`Procedure.contractTriple`. `ProcEntryEnv` fixes the entry's runtime factory to be
over that factory, so every condition a run captures holds when it evaluates to
`true` in the runtime factory's model, and the entry environments these instances
quantify over range over every model. -/

/-- **Deductive correctness of a procedure on event traces, read by
    denotation**: `ProcedureAssertsValidOnTraces` over the factory visible before the
    procedure. -/
@[expose] def ProcedureAssertsValidOnTraces.denote (params : InitEnvWFParams)
    (entryProcName : String) (p : Program) : Prop :=
  ProcedureAssertsValidOnTraces
      (Core.Logic.DenoteBasedInterp (p.factoryBeforeProcedure entryProcName))
    params entryProcName p

/-- **Satisfiability of a procedure on event traces, read by denotation**:
    `ProcedureAssertsSatisfiableOnTraces` over the factory visible before the
    procedure. -/
@[expose] def ProcedureAssertsSatisfiableOnTraces.denote (params : InitEnvWFParams)
    (entryProcName : String) (p : Program) : Prop :=
  ProcedureAssertsSatisfiableOnTraces
    (Core.Logic.DenoteBasedInterp (p.factoryBeforeProcedure entryProcName))
    params entryProcName p

/-! ## Analysis -/

namespace Analysis

/-- A program input to a contract checker: the procedure names to consider as
    entry points, paired with the enclosing program. -/
structure CoreVerifierInput where
  entryPoints : List String
  prog : Program

/-- The definition of Core verification under each `VerificationMode`. A
    `VCResults` array passing under the mode claims:

    * `.deductive`: `ProcedureAssertsValidOnTraces.denote` (universal: from
      every entry environment, so in every model, every assertion a run reaches
      is valid and every terminating run satisfies the postconditions);
    * `.bugFinding`: `ProcedureAssertsSatisfiableOnTraces.denote`
      (existential dual: from some entry environment, some run reaches each
      assert and some terminating run satisfies the postconditions);
    * `.bugFindingAssumingCompleteSpec`: not yet specified. Every result
      passes and claims `False`, so no analyzer implements this mode yet.
    * `.deductiveAssumingSatisfiablePaths`: as `.deductive`. The mode's premise
      only adds failures, never passes, so a pass claims the same as in
      `.deductive`; failures reported under the premise are not specified.

    A result that does not pass claims nothing. An analyzer `analyze` implements
    the mode when `MatchesAnalysis (analyze mode) (CoreVerifierModel mode params)`.
    `params` fixes the entry well-formedness of procedure bodies (see
    `ProcEnvWF`). It must admit the program's entry environments: when it
    admits none, the property holds vacuously, so a soundness statement should
    fix `params` to the one the verifier assumes rather than leave it free. -/
def CoreVerifierModel
    (mode : VerificationMode)
    (params : InitEnvWFParams) :
    CoreVerifierInput → VCResults → Prop :=
  Imperative.Analysis.Sound
    (fun input =>
      match mode with
      | .deductive | .deductiveAssumingSatisfiablePaths =>
        ∀ procName ∈ input.entryPoints,
          ProcedureAssertsValidOnTraces.denote params procName input.prog
      | .bugFinding =>
        ∀ procName ∈ input.entryPoints,
          ProcedureAssertsSatisfiableOnTraces.denote params procName input.prog
      | .bugFindingAssumingCompleteSpec =>
        -- bugFinding, but postcondition being checked with validity
        -- TODO!
        False)
    (fun results =>
      match mode with
      | .deductive | .deductiveAssumingSatisfiablePaths =>
        ∀ r ∈ results, VCResult.isSuccess r = Bool.true
      | .bugFinding => ∀ r ∈ results, VCResult.isBugFindingSuccess r = Bool.true
      | .bugFindingAssumingCompleteSpec => True)

end Analysis

end Core.Specification

end -- public section

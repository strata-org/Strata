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

- **`AssertValidInProcedure`**, **`AssertSatisfiableInProcedure`** — assertion
  validity and satisfiability in a procedure's body, from its entry
  environments (failure-flag semantics; the valid form is deprecated).
- **`ProcedureAssertsValid`**, **`ProcedureAssertsSatisfiable`** — assert
  validity or satisfiability plus postconditions (failure-flag semantics).
- **`ProcedureAssertsValidOnTraces`**, **`ProcedureAssertsSatisfiableOnTraces`** —
  the same properties on event traces, read through a `ConditionInterp`. A trace
  records the assertions of every callee call that completes, so validity covers
  those transitively; a call whose callee never finishes contributes no events.
  The valid form checks the procedure's contract by reading its non-free
  postconditions as assertions appended to each finished run's trace.
- **`ProcedureAssertsValidOnTraces.denote`**,
  **`ProcedureAssertsSatisfiableOnTraces.denote`** — the same properties with
  conditions read by Lambda's denotational semantics: validity in every model
  of `Core.Factory`, satisfiability in some model.
- **`CoreVerifierModel`** — what a passing `VCResults` claims under each
  verification mode.
-/

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ## Procedure correctness -/


/-- Common shape of Core-level assertion specifications on a procedure named
    `entryProcName` in program `p`. -/
@[expose] def AssertSpecInProcedure (params : InitEnvWFParams)
    (Spec : (Imperative.Env Expression → Prop) → Statements → Statement → Prop)
    (entryProcName : String) (p : Program) : Prop :=
  ∃ proc ss,
    p.findProcByString? entryProcName = some proc ∧
    proc.body = .structured ss ∧
    Spec
      (fun ρ₀ => ProcEnvWF params proc ρ₀ ∧ AxiomsBeforeProcedureDecl entryProcName p ρ₀)
      ss
      (Stmt.block "" ss #[])

/-- A specific assertion `a` in the procedure named `entryProcName` of program
    `p` is valid for initial program states that satisfy `ProcEnvWF` and the
    program-level axioms and distincts visible to `entryProcName`
    (`AxiomsBeforeProcedureDecl`). -/
@[expose, deprecated "use `AssertValidOnTracesInProcedure`" (since := "2026-10-02")]
def AssertValidInProcedure (params : InitEnvWFParams)
    (entryProcName : String) (p : Program)
    (a : Imperative.AssertId Expression) : Prop :=
  AssertSpecInProcedure params
    (fun Pre _ss s =>
      Specification.AssertValidWhen (Core.Logic.Lang.core p.findProcByString?) Pre s a)
    entryProcName p

/-- A specific assertion `a` in the procedure named `entryProcName` of program
    `p` is satisfiable: some initial program state satisfying `ProcEnvWF` and
    `AxiomsBeforeProcedureDecl` reaches a configuration at the assert with the
    expression evaluating to `tt`. We restrict the obligation to `a`s that
    syntactically appear in the body (via `Statements.collectAssertIds`),
    otherwise it is vacuously true (unless entryProcName is an invalid procedure
    or the procedure doesn't have a structured body). -/
@[expose] def AssertSatisfiableInProcedure (params : InitEnvWFParams)
    (entryProcName : String) (p : Program)
    (a : Imperative.AssertId Expression) : Prop :=
  AssertSpecInProcedure params
    (fun Pre ss s =>
      a ∈ Statements.collectAssertIds ss →
      -- `AssertSatisfiableWhen` checks the witnessing run's assert under its
      -- own reached-configuration factory (`(L.getEnv cfg).factory`).
      Specification.AssertSatisfiableWhen (Core.Logic.Lang.core p.findProcByString?) Pre s a)
    entryProcName p

set_option linter.deprecated false in
/-- The procedure named `entryProcName` (looked up in `p` via
    `Program.findProcByString?`) has every assert valid and its postconditions
    valid on termination.

    0. The procedure exists in `p` (`procedureExists`);

    1. Every reachable assert in the procedure body evaluates to `true`
       (`AssertValidInProcedure`);

    2. Postcondition: When the procedure body terminates from a `ProcEnvWF`
       initial environment, every non-free postcondition holds and
       `hasFailure` stays `false`.

    This is partial correctness: if the program has an infinite loop, the
    postcondition is considered to be satisfied. Since total correctness is
    a conjunction of partial correctness and termination, having partial
    correctness-only definition here is useful.

    A possibly more succinct style of ProcedureAssertsValid is using Hoare
    triple (`Hoare.TripleWith` in `Strata.DL.Imperative.Logic.HoareTemplate`). Since
    `Hoare.TripleWith` also
    uses partial correctness, this seems natural. However, there is a very
    subtle issue due to the fact that programs can also have `assert`s in the
    middle of procedures, which leads `Hoare.TripleWith` to too weak notion to use
    for us.

    For example, let's consider this program:

    ```
    procedure P()
    spec { ensures false; }
    { while true {};
    };
    ```

    Since the program iterates indefinitely, the postcondition is considered
    met in our partial correctness definition; hence the contract is true.
    This is OK.

    However, if we slightly extend the body of P to include `assert false`:

    ```
    procedure P()
    spec { ensures false; }
    { assert false; // -- A
      while true {};
    };
    ```

    We know that the assert A does not hold. However, if we use `Hoare.TripleWith` which
    inspects asserts and postconditions *only if the code terminates*,
    we end up accepting this procedure P as 'correct'.

    Therefore, we define ProcedureAssertsValid as a structure with three fields:
    (0) the procedure exists in `p`,
    (1) assert validity in the body, and
    (2) postcondition validity on termination.
-/
@[deprecated "use `ProcedureAssertsValidOnTraces`" (since := "2026-10-02")]
structure ProcedureAssertsValid (params : InitEnvWFParams) (entryProcName : String)
    (p : Program) : Prop where
  /-- (0) The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are valid. -/
  assertsValid : ∀ a, AssertValidInProcedure params entryProcName p a
  /-- (2) The postconditions hold on termination.
      Uses `CoreBodyExec` to abstract over both structured and CFG bodies.
      The factory is the initial environment's own `ρ₀.factory`. -/
  postconditionsValid : ∀ proc, p.findProcByString? entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ : Imperative.Env Expression),
      ProcEnvWF params proc ρ₀ →
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ →
      ∀ (σ' : CoreStore) (failed : Bool),
        CoreBodyExec (p.findProcByString?) proc.body ρ₀ σ' failed →
        (∀ (label : CoreLabel) (check : Procedure.Check),
          (label, check) ∈ proc.spec.postconditions.toList →
          check.attr = Procedure.CheckAttr.Default →
          Expression.eval ρ₀.factory σ' check.expr = some HasBool.tt) ∧
        failed = Bool.false

/-- The existential dual of `ProcedureAssertsValid`, intended as the target
    for bug-finding–style analyses.

    0. The procedure exists in `p`;
    1. Every assert in the body is *satisfiable*: some `ProcEnvWF` initial
       environment reaches a configuration at the assert with the expression
       evaluating to `tt`;
    2. The postconditions are *satisfiable*: some terminating run from a
       `ProcEnvWF` initial environment makes every non-free postcondition
       evaluate to `tt` and leaves `hasFailure = false`. -/
structure ProcedureAssertsSatisfiable (params : InitEnvWFParams) (entryProcName : String)
    (p : Program) : Prop where
  /-- (0) The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are satisfiable.
      `AssertSatisfiableInProcedure` is defined to be trivially true for
      `AssertId`s that don't syntactically appear in the procedure body.

      NOTE: this excludes satisfiability of the asserts that are not in the
      body of the entryProcName but can be transitively reached. This is related
      to the fact that call is defined as a command in Core. In Strata, commands
      cannot change control flow according to small-step semantics, but a
      function call jumping to the subprocedure is a change in its control flow.
      Instead, if call is defined as a statement, not command, we can now describe
      reachability & validity & satisfiability of the assertions in subprocedures.
  -/
  assertsSatisfiable : ∀ a, AssertSatisfiableInProcedure params entryProcName p a
  /-- (2) Some terminating run satisfies all postconditions.
      Note that postconditionsSatisfiable doesn't have to describe the satisfiability of postconditions
      of other procedures called during execution of entryProcName because call_sem of EvalCommand
      will have the postcondition check (for the particular input of procedure invocation)
      already.
  -/
  postconditionsSatisfiable : ∀ proc, p.findProcByString? entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∃ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore),
      ProcEnvWF params proc ρ₀ ∧
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ ∧
      CoreBodyExec (p.findProcByString?) proc.body ρ₀ σ' false ∧
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.postconditions.toList →
        check.attr = Procedure.CheckAttr.Default →
        Expression.eval ρ₀.factory σ' check.expr = some HasBool.tt)

/-! ## Procedure correctness on event traces

The definitions below state the same properties over the event-trace semantics
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

/-- The initial environments a procedure body is verified from: `ProcEnvWF` and
    the axioms and distincts visible to `entryProcName`. -/
@[expose] def ProcEntryEnv (params : InitEnvWFParams) (entryProcName : String)
    (p : Program) (proc : Procedure) (ρ₀ : Imperative.Env Expression) : Prop :=
  ProcEnvWF params proc ρ₀ ∧ AxiomsBeforeProcedureDecl entryProcName p ρ₀

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
in a model of `Core.Factory`, as Core's Hoare triples do. These instances fix
that reading: validity must hold in every model, satisfiability in some model. -/

/-- **Deductive correctness of a procedure on event traces, read by
    denotation**: `ProcedureAssertsValidOnTraces` in every model of
    `Core.Factory`. -/
@[expose] def ProcedureAssertsValidOnTraces.denote (params : InitEnvWFParams)
    (entryProcName : String) (p : Program) : Prop :=
  ∀ model : Lambda.Interp Core.Factory,
    ProcedureAssertsValidOnTraces (Core.Logic.DenoteBasedInterp model) params entryProcName p

/-- **Satisfiability of a procedure on event traces, read by denotation**:
    `ProcedureAssertsSatisfiableOnTraces` in some model of `Core.Factory`. -/
@[expose] def ProcedureAssertsSatisfiableOnTraces.denote (params : InitEnvWFParams)
    (entryProcName : String) (p : Program) : Prop :=
  ∃ model : Lambda.Interp Core.Factory,
    ProcedureAssertsSatisfiableOnTraces (Core.Logic.DenoteBasedInterp model)
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

    * `.deductive`: `ProcedureAssertsValidOnTraces.denote` (universal: in
      every model, every assertion a run reaches is valid and every
      terminating run satisfies the postconditions);
    * `.bugFinding`: `ProcedureAssertsSatisfiableOnTraces.denote`
      (existential dual: in some model, some run reaches each assert and some
      terminating run satisfies the postconditions);
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

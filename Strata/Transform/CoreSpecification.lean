/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Transform.Specification
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.Verifier

public section

/-! # Core-Level Specification

Bridges Core procedures to the generic Imperative specification framework
(`AssertValidWhen`, `AllAssertsValidWhen`).

## Overview

- **`Lang.core`** — the `Lang Expression` bundle for Core small-step semantics
- **`ProcEnvWF`** — well-formedness condition on the initial verification env
- **`AssertValidInProcedure`** — `AssertValidWhen` on the verification statement
- **`AssertSatisfiableInProcedure`** — `AssertSatisfiableWhen` on the verification statement
- **`ProcedureAssertsValid`** — assert validity + postconditions + hasFailure on termination
- **`ProcedureAssertsSatisfiable`** — existential dual: some run reaches each
  assert with a passing expression and some terminating run satisfies the
  postconditions (the natural target for bug-finding modes)
-/

namespace Core.Specification

open Core Imperative

/-! ## Core `Lang` bundle -/

/-- The `Lang Expression` bundle for Core small-step semantics. -/
@[expose] def Lang.core
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Specification.Lang Expression :=
  Imperative.Specification.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert

/-! ## Well-formed program state at the entry of procedure -/

/-- The list of variables that must have been declared,
    to make execution of the body of this procedure not stuck.
    outputs are included because the body refers to the output variables without
    initialization.
    Old snapshot variables for in-out parameters (those appearing in both
    inputs and outputs) are included because the body or spec of the
    procedure may refer to those with "old g".  -/
@[expose] def procVerifyInitIdents (proc : Procedure) : List Expression.Ident :=
  ListMap.keys proc.header.inputs ++
  ListMap.keys proc.header.outputs ++
  (ListMap.keys proc.header.getInoutParams).map (fun id => CoreIdent.mkOld id.name)

/-- A well-formed initial environment for executing the procedure body.
    This captures the state after inputs, outputs, modified globals have been
    initialized and preconditions assumed.
    The well-formed environment also includes old snapshots in store -/
structure ProcEnvWF (proc : Procedure) (ρ : Imperative.Env Expression) : Prop where
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfCong : WellFormedCoreEvalCong ρ.eval
  wfExprCongr : WellFormedSemanticEvalExprCongr ρ.eval
  storeDefined : ∀ id ∈ procVerifyInitIdents proc, (ρ.store id).isSome
  -- When a procedure is called, the value of "old g" must be equal to "g"
  -- for in-out parameters.
  oldInoutMatchesInout : ∀ id ∈ ListMap.keys proc.header.getInoutParams,
    ρ.store id = ρ.store (CoreIdent.mkOld id.name)
  -- Precondition holds in the body, and input state had no failure.
  preconditionsHold : ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    ρ.eval ρ.store check.expr = some HasBool.tt
  noFailure : ρ.hasFailure = Bool.false

/-! ## Procedure correctness -/

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

/-- A specific assertion `a` in procedure `proc` is valid
    for initial program states satisfying the preconditions (`ProcEnvWF`). -/
@[expose] def AssertValidInProcedure
    (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  Imperative.Specification.AssertValidWhen (Specification.Lang.core π φ)
    (ProcEnvWF proc) (Stmt.block "" proc.body #[]) a

/-- A specific assertion `a` in procedure `proc` is satisfiable: some
    initial program state satisfying the preconditions (`ProcEnvWF`) reaches
    a configuration at the assert with the expression evaluating to `tt`. -/
@[expose] def AssertSatisfiableInProcedure
    (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  Imperative.Specification.AssertSatisfiableWhen (Specification.Lang.core π φ)
    (ProcEnvWF proc) (Stmt.block "" proc.body #[]) a

/-- The procedure named `entryProcName` (looked up via `π`) has every assert
    valid and its postconditions valid on termination.

    0. The procedure exists in the lookup `π` (`procedureExists`);

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
    triple (`Hoare.Triple` in Specification.lean). Since `Hoare.Triple` also
    uses partial correctness, this seems natural. However, there is a very
    subtle issue due to the fact that programs can also have `assert`s in the
    middle of procedures, which leads `Hoare.Triple` to too weak notion to use
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

    We know that the assert A does not hold. However, if we use `Hoare.Triple` which
    inspects asserts and postconditions *only if the code terminates*,
    we end up accepting this procedure P as 'correct'.

    Therefore, we define ProcedureAssertsValid as a structure with three fields:
    (0) the procedure exists in `π`,
    (1) assert validity in the body, and
    (2) postcondition validity on termination.
-/
structure ProcedureAssertsValid (entryProcName : String) (p : Program) : Prop where
  /-- (0) The procedure name resolves in the lookup `π`. -/
  procedureExists : ∃ proc, π entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are valid. -/
  assertsValid : ∀ proc, π entryProcName = some proc →
    ∀ a, AssertValidInProcedure π φ proc a
  /-- (2) The postconditions hold on termination.
      Note that postconditionsValid doesn't have to describe the validity of postconditions
      of other procedures called during execution of entryProcName because call_sem of EvalCommand
      will have the postcondition check (for the particular input of procedure invocation)
      already.
  -/
  postconditionsValid : ∀ proc, π entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ ρ' : Imperative.Env Expression),
      ProcEnvWF proc ρ₀ →
      CoreStepStar π φ (.stmts proc.body ρ₀) (.terminal ρ') →
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.postconditions.toList →
        check.attr = Procedure.CheckAttr.Default →
        ρ'.eval ρ'.store check.expr = some HasBool.tt) ∧
      ρ'.hasFailure = Bool.false

/-- The existential dual of `ProcedureAssertsValid`, intended as the target
    for bug-finding–style analyses.

    0. The procedure exists in the lookup `π`;
    1. Every assert in the body is *satisfiable*: some `ProcEnvWF` initial
       environment reaches a configuration at the assert with the expression
       evaluating to `tt`;
    2. The postconditions are *satisfiable*: some terminating run from a
       `ProcEnvWF` initial environment makes every non-free postcondition
       evaluate to `tt` and leaves `hasFailure = false`. -/
structure ProcedureAssertsSatisfiable (entryProcName : String) (p : Program) : Prop where
  /-- (0) The procedure name resolves in the lookup `π`. -/
  procedureExists : ∃ proc, π entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are satisfiable. -/
  assertsSatisfiable : ∀ proc, π entryProcName = some proc →
    ∀ a, AssertSatisfiableInProcedure π φ proc a
  /-- (2) Some terminating run satisfies all postconditions.
      Note that postconditionsSatisfiable doesn't have to describe the satisfiability of postconditions
      of other procedures called during execution of entryProcName because call_sem of EvalCommand
      will have the postcondition check (for the particular input of procedure invocation)
      already.
  -/
  postconditionsSatisfiable : ∀ proc, π entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∃ (ρ₀ ρ' : Imperative.Env Expression),
      ProcEnvWF proc ρ₀ ∧
      CoreStepStar π φ (.stmts proc.body ρ₀) (.terminal ρ') ∧
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.postconditions.toList →
        check.attr = Procedure.CheckAttr.Default →
        ρ'.eval ρ'.store check.expr = some HasBool.tt) ∧
      ρ'.hasFailure = Bool.false

/-! ## Analysis -/

namespace Analysis

/-- A program input to a contract checker: the procedure names to consider as
    entry points, paired with the enclosing program
    The procedure lookup function `π` is used. -/
structure CoreVerifierInput where
  entryPoints: String → Prop
  prog : Program

/-- An analysis whose desirable property under each `VerificationMode` is:

    * `.deductive` — `ProcedureAssertsValid` (universal: every assert valid
      and every terminating run satisfies the postconditions);
    * `.bugFinding` — `ProcedureAssertsSatisfiable` (existential dual: some
      run reaches each assert and some terminating run satisfies the
      postconditions);
    * `.bugFindingAssumingCompleteSpec` — `False` (not yet specified).

    The diagnostic is a `VCResults` array; the `analyze` function
    additionally receives the `VerificationMode` so it can shape the
    obligations it produces, and `pass` reports success on every `VCResult`
    under the given mode. -/
def CoreVerifierModel
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (mode : VerificationMode)
    (analyze : VerificationMode → CoreVerifierInput → VCResults) :
    Imperative.Specification.Analysis CoreVerifierInput VCResults :=
  { desirableProperty := fun input =>
      match mode with
      | .deductive =>
        forall procName, input.entryPoints procName
          → ProcedureAssertsValid π φ procName input.prog
      | .bugFinding =>
        forall procName, input.entryPoints procName
          → ProcedureAssertsSatisfiable π φ procName input.prog
      | .bugFindingAssumingCompleteSpec =>
        -- bugFinding, but postcondition being checked with validity
        -- TODO!
        False
    analyze := analyze mode
    pass := fun results =>
      match mode with
      | .deductive => ∀ r ∈ results, VCResult.isSuccess r = Bool.true
      | .bugFinding => ∀ r ∈ results, VCResult.isBugFindingSuccess r = Bool.true
      | .bugFindingAssumingCompleteSpec => False }

end Analysis

end Core.Specification

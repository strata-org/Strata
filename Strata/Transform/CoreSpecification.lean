/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.Specification
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.Verifier
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.Factory

public section

/-! # Core-Level Specification

Bridges Core procedures to the generic Imperative specification framework
(`AssertValidWhen`, `AllAssertsValidWhen`).  The `Lang` bundles themselves
(`Lang.core`, `Lang.coreBlock`) and their gates
(`InitEnvWFParams`, `InitEnvWF`, `BlockInitEnvWF`) live in
`Strata.Languages.Core.Logic.LangDef`.

## Overview

- **`ProcEnvWF`** — well-formedness condition on the initial verification env
- **`AssertValidInProcedure`** — `AssertValidWhen` on the verification statement
- **`AssertSatisfiableInProcedure`** — `AssertSatisfiableWhen` on the verification statement
- **`ProcedureAssertsValid`** — assert validity + postconditions + hasFailure on termination
- **`ProcedureAssertsSatisfiable`** — existential dual: some run reaches each
  assert with a passing expression and some terminating run satisfies the
  postconditions (the natural target for bug-finding modes)
-/

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

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
structure ProcEnvWF (proc : Procedure) (ρ : Imperative.Env Expression)
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  -- The verification env's store holds only values (true of reachable stores).
  storeValues : Imperative.WellFormedStore ρ.store ρ.factory
  storeDefined : ∀ id ∈ procVerifyInitIdents proc, (ρ.store id).isSome
  -- When a procedure is called, the value of "old g" must be equal to "g"
  -- for in-out parameters.
  oldInoutMatchesInout : ∀ id ∈ ListMap.keys proc.header.getInoutParams,
    ρ.store id = ρ.store (CoreIdent.mkOld id.name)
  -- Precondition holds in the body, and input state had no failure.
  preconditionsHold : ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    Expression.eval ρ.factory ρ.store check.expr = some HasBool.tt
  noFailure : ρ.hasFailure = Bool.false

/-! ## Axioms and distincts visible to a procedure

A program also contains `axiom` declarations (boolean expressions that holds
globally) and `distinct` declarations (lists of expressions whose values must differ).
For verification, the initial environment of a procedure must satisfy the
axioms and distincts that have been declared *before* the procedure in the
program. -/

/-- Declarations in `p` that appear strictly before the procedure named
    `entryProcName`. -/
@[expose] def declsBefore (entryProcName : String) (p : Program) : List Decl :=
  p.decls.takeWhile fun d =>
    match d with
    | .proc proc _ => proc.header.name.name != entryProcName
    | _ => true

/-- The initial environment `ρ₀` satisfies all axioms and `distinct`
    declarations that appear in `p.decls` before the procedure named
    `entryProcName`. -/
@[expose] def AxiomsBeforeProcedureDecl
    (entryProcName : String) (p : Program)
    (ρ₀ : Imperative.Env Expression) : Prop :=
  (declsBefore entryProcName p).foldr
    (fun d acc =>
      match d with
      | .ax a _ =>
          Expression.eval ρ₀.factory ρ₀.store a.e = some HasBool.tt ∧ acc
      | .distinct _ es _ =>
          List.Pairwise (fun e₁ e₂ =>
            Expression.eval ρ₀.factory ρ₀.store e₁ ≠ Expression.eval ρ₀.factory ρ₀.store e₂) es ∧ acc
      | _ => acc)
    True

/-! ## Procedure correctness -/

variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-- Common shape of Core-level assertion specifications on a procedure named
    `entryProcName` in program `p`. -/
@[expose] def AssertSpecInProcedure
    (Spec : (Imperative.Env Expression → Prop) → Statements → Statement → Prop)
    (entryProcName : String) (p : Program) : Prop :=
  ∃ proc ss,
    p.findProcByString? entryProcName = some proc ∧
    proc.body = .structured ss ∧
    Spec
      (fun ρ₀ => ProcEnvWF proc ρ₀ ∧ AxiomsBeforeProcedureDecl entryProcName p ρ₀)
      ss
      (Stmt.block "" ss #[])

/-- A specific assertion `a` in the procedure named `entryProcName` of program
    `p` is valid for initial program states that satisfy `ProcEnvWF` and the
    program-level axioms and distincts visible to `entryProcName`
    (`AxiomsBeforeProcedureDecl`). -/
@[expose] def AssertValidInProcedure
    (entryProcName : String) (p : Program)
    (a : Imperative.AssertId Expression) : Prop :=
  AssertSpecInProcedure
    (fun Pre _ss s =>
      Imperative.Specification.AssertValidWhen
        (Core.Logic.Lang.core p.findProcByString? φ) Pre s a)
    entryProcName p

/-- A specific assertion `a` in the procedure named `entryProcName` of program
    `p` is satisfiable: some initial program state satisfying `ProcEnvWF` and
    `AxiomsBeforeProcedureDecl` reaches a configuration at the assert with the
    expression evaluating to `tt`. We restrict the obligation to `a`s that
    syntactically appear in the body (via `Statements.collectAssertIds`),
    otherwise it is vacuously true (unless entryProcName is an invalid procedure
    or the procedure doesn't have a structured body). -/
@[expose] def AssertSatisfiableInProcedure
    (entryProcName : String) (p : Program)
    (a : Imperative.AssertId Expression) : Prop :=
  AssertSpecInProcedure
    (fun Pre ss s =>
      a ∈ Statements.collectAssertIds ss →
      Imperative.Specification.AssertSatisfiableWhen
        (Core.Logic.Lang.core p.findProcByString? φ) Pre s a)
    entryProcName p

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
    triple (`Hoare.Triple` in `Strata.DL.Imperative.Logic.HoareTemplate`). Since
    `Hoare.Triple` also
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
    (0) the procedure exists in `p`,
    (1) assert validity in the body, and
    (2) postcondition validity on termination.
-/
structure ProcedureAssertsValid (entryProcName : String) (p : Program) : Prop where
  /-- (0) The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are valid. -/
  assertsValid : ∀ a, AssertValidInProcedure φ entryProcName p a
  /-- (2) The postconditions hold on termination.
      Uses `CoreBodyExec` to abstract over both structured and CFG bodies.
      For structured bodies, the terminal factory `fac'` comes from the terminal
      `Env` (may differ from `fac` due to `funcDecl` extensions). For CFG
      bodies, `fac' = fac` since `CoreCFGStepStar` does not track factory changes. -/
  postconditionsValid : ∀ proc, p.findProcByString? entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ : Imperative.Env Expression),
      ProcEnvWF proc ρ₀ →
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ →
      ∀ (σ' : CoreStore) (fac' : Expression.Factory) (failed : Bool),
        CoreBodyExec (p.findProcByString?) φ proc.body ρ₀.store ρ₀.factory σ' fac' failed →
        (∀ (label : CoreLabel) (check : Procedure.Check),
          (label, check) ∈ proc.spec.postconditions.toList →
          check.attr = Procedure.CheckAttr.Default →
          Expression.eval fac' σ' check.expr = some HasBool.tt) ∧
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
structure ProcedureAssertsSatisfiable (entryProcName : String) (p : Program) : Prop where
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
  assertsSatisfiable : ∀ a, AssertSatisfiableInProcedure φ entryProcName p a
  /-- (2) Some terminating run satisfies all postconditions.
      Note that postconditionsSatisfiable doesn't have to describe the satisfiability of postconditions
      of other procedures called during execution of entryProcName because call_sem of EvalCommand
      will have the postcondition check (for the particular input of procedure invocation)
      already.
  -/
  postconditionsSatisfiable : ∀ proc, p.findProcByString? entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∃ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (fac' : Expression.Factory),
      ProcEnvWF proc ρ₀ ∧
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ ∧
      CoreBodyExec (p.findProcByString?) φ proc.body ρ₀.store ρ₀.factory σ' fac' false ∧
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.postconditions.toList →
        check.attr = Procedure.CheckAttr.Default →
        Expression.eval fac' σ' check.expr = some HasBool.tt)

/-! ## Analysis -/

namespace Analysis

/-- A program input to a contract checker: the procedure names to consider as
    entry points, paired with the enclosing program. -/
structure CoreVerifierInput where
  entryPoints : List String
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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (mode : VerificationMode)
    (analyze : VerificationMode → CoreVerifierInput → VCResults) :
    Imperative.Specification.Analysis CoreVerifierInput VCResults :=
  { desirableProperty := fun input =>
      match mode with
      | .deductive =>
        ∀ procName ∈ input.entryPoints,
          ProcedureAssertsValid φ procName input.prog
      | .bugFinding =>
        ∀ procName ∈ input.entryPoints,
          ProcedureAssertsSatisfiable φ procName input.prog
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

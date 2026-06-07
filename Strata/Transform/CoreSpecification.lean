/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Transform.Specification
public import Strata.Languages.Core.WF

public section

/-! # Core-Level Specification

Bridges Core procedures to the generic Imperative specification framework
(`AssertValidWhen`, `AllAssertsValidWhen`).

## Overview

- **`Lang.core`** — the `Lang Expression` bundle for Core small-step semantics
- **`ProcEnvWF`** — well-formedness condition on the initial verification env
- **`AssertValidInProcedure`** — `AssertValidWhen` on the verification statement
- **`ProcedureCorrect`** — assert validity + postconditions + hasFailure on termination
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

-- NOTE: A CFG-flavored `Lang` bundle (`Lang.coreCFG` plus `CoreCFGStepStar`)
-- requires the `cmd`-constructor refactoring of `EvalDetBlock` from the
-- unstructured-infra changes. On the procedure-body branch, only structured
-- bodies have a small-step semantics, so the `.cfg` arm of
-- `AssertValidInProcedure` below collapses to `False`.

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
structure ProcEnvWF (proc : Procedure) (ρ : Env Expression) : Prop where
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
  match proc.body with
  | .structured ss =>
    Imperative.Specification.AssertValidWhen (Specification.Lang.core π φ)
      (ProcEnvWF proc) (Stmt.block "" ss #[]) a
  -- CFG bodies don't yet have a small-step semantics on this branch, so
  -- they are vacuously asserts-valid.  Real CFG support arrives with
  -- `Lang.coreCFG` once the unstructured-infra changes land.
  | .cfg _ => True

/-- A procedure is correct with respect to its specification.

    1. Every reachable assert in the procedure body evaluates to `true`
       (`AssertValidInProcedure`);

    2. Postcondition: When the procedure body terminates from a `ProcEnvWF`
       initial environment, every non-free postcondition holds and
       `hasFailure` stays `false`.

    This is partial correctness: if the program has an infinite loop, the
    postcondition is considered to be satisfied. Since total correctness is
    a conjunction of partial correctness and termination, having partial
    correctness-only definition here is useful.

    A possibly more succinct style of ProcedureCorrect is using Hoare triple
    (`Hoare.Triple` in Specification.lean). Since `Hoare.Triple` also uses
    partial correctness, this seems natural. However, there is a very subtle
    issue due to the fact that programs can also have `assert`s in the middle
    of procedures, which leads `Hoare.Triple` to too weak notion to use for us.

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

    Therefore, we define ProcedureCorrect as a structure with two fields:
    (1) assert validity in the body, and
    (2) postcondition validity on termination.
-/
structure ProcedureCorrect (proc : Procedure) (p : Program) : Prop where
  /-- (1) The asserts in the body of proc are valid. -/
  assertsValid : ∀ a, AssertValidInProcedure π φ proc a
  /-- (2) The postconditions hold on termination.
      Uses `CoreBodyExec` to abstract over both structured and CFG bodies.
      For structured bodies, the terminal eval `δ'` comes from the terminal
      `Env` (may differ from `δ` due to `funcDecl` extensions). For CFG
      bodies, `δ' = δ` since `CoreCFGStepStar` does not track eval changes. -/
  postconditionsValid :
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ : Env Expression),
      ProcEnvWF proc ρ₀ →
      ∀ (σ' : CoreStore) (δ' : CoreEval) (failed : Bool),
        CoreBodyExec π φ proc.body ρ₀.store ρ₀.eval σ' δ' failed →
        (∀ (label : CoreLabel) (check : Procedure.Check),
          (label, check) ∈ proc.spec.postconditions.toList →
          check.attr = Procedure.CheckAttr.Default →
          δ' σ' check.expr = some HasBool.tt) ∧
        failed = Bool.false

end Core.Specification

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.StatementSemanticsProps
import Strata.Transform.Specification
import Strata.Languages.Core.WF

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
def Lang.core
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Specification.Lang Expression :=
  Imperative.Specification.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert

/-! ## Well-formed program state at the entry of procedure -/

def procVerifyInitIdents (proc : Procedure) : List Expression.Ident :=
  ListMap.keys proc.header.inputs ++
  ListMap.keys proc.header.outputs ++
  proc.spec.modifies ++
  proc.spec.modifies.map (fun g => CoreIdent.mkOld g.name)

/-- A well-formed initial environment for executing the procedure body.
    This captures the state after inputs, outputs, modified globals (with
    their `old` snapshots) have been initialized and preconditions assumed. -/
structure ProcEnvWF (proc : Procedure) (ρ : Env Expression) : Prop where
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  wfBool : WellFormedSemanticEvalBool ρ.eval
  storeDefined : ∀ id ∈ procVerifyInitIdents proc, (ρ.store id).isSome
  oldMatchesCurrent : ∀ g ∈ proc.spec.modifies,
    ρ.store g = ρ.store (CoreIdent.mkOld g.name)
  preconditionsHold : ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    ρ.eval ρ.store check.expr = some HasBool.tt
  noFailure : ρ.hasFailure = Bool.false
  initIdentsNodup : (procVerifyInitIdents proc).Nodup
  modifiesNeOld : ∀ g ∈ proc.spec.modifies, g ≠ CoreIdent.mkOld g.name

/-! ## Procedure correctness -/

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

/-- A specific assertion `a` in procedure `proc` is valid
    for initial program states satisfying the preconditions (`ProcEnvWF`). -/
def AssertValidInProcedure
    (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  ∀ (ρ₀ : Env Expression), ProcEnvWF proc ρ₀ →
    ∀ cfg, CoreStepStar π φ (.stmts proc.body ρ₀) cfg →
      coreIsAtAssert cfg a →
      cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- A procedure is correct with respect to its specification.

    1. Every reachable assert in the procedure body evaluates to `true`
       (`AssertValidInProcedure`);

    2. Postcondition: When the procedure body terminates from a `ProcEnvWF`
       initial environment, every non-free postcondition holds and
       `hasFailure` stays `false`.

    Note that this is partial correctness: if the program has
    an infinite loop, the postcondition considered to be satisfied. Since total
    correctness is a conjunction of partial correctness and termination, having
    partial correctness-only definition here is useful.

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

    Therefore, we define ProcedureCorrect as a conjunction of
    (1) explicit inspection of validity of asserts in the the body, and
    (2) a predicate stating that the postcondition holds.
-/
def ProcedureCorrect (proc : Procedure) (p : Program) : Prop :=
  -- (1) The asserts in the body of proc are valid
  (∀ a, AssertValidInProcedure π φ proc a) ∧
  -- (2) The postcondition is valid.
  (WF.WFProcedureProp p proc →
   ∀ (ρ₀ ρ' : Env Expression),
    ProcEnvWF proc ρ₀ →
    CoreStepStar π φ (.stmts proc.body ρ₀) (.terminal ρ') →
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      ρ'.eval ρ'.store check.expr = some HasBool.tt) ∧
    ρ'.hasFailure = Bool.false)

end Core.Specification

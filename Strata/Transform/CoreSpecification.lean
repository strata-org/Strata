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
- **`ProcedurePre`** / **`procStartEnv`** — procedure preconditions and starting env
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
  proc.header.inputs.keys ++ proc.header.outputs.keys

/-- A well-formed initial environment for procedure verification. -/
structure ProcEnvWF (proc : Procedure) (ρ : Env Expression) : Prop where
  wfVar : WellFormedSemanticEvalVar ρ.eval
  wfBool : WellFormedSemanticEvalBool ρ.eval
  -- The register file contains all input and output arguments of the procedure.
  storeDefined : ∀ id ∈ procVerifyInitIdents proc, (ρ.store id).isSome

/-! ## Procedure correctness -/

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

/-- A program state that passed precondition of procedure. -/
def ProcedurePre (proc : Procedure) (ρ₀ : Env Expression) : Prop :=
  (∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    ρ₀.eval ρ₀.store check.expr = some HasBool.tt) ∧
  WellFormedSemanticEvalBool ρ₀.eval ∧
  ρ₀.hasFailure = Bool.false

/-- The augmented starting environment for body execution:
    `ρ₀` with old-variable bindings added. -/
abbrev procStartEnv (proc : Procedure) (ρ₀ : Env Expression) : Env Expression :=
  withOldBindings proc.spec.modifies ρ₀

/-- A specific assertion `a` in procedure `proc` is valid
    for initial program states satisfying the preconditions (`ProcEnvWF`). -/
def AssertValidInProcedure
    (proc : Procedure) (verifyStmt : Statement)
    (a : Imperative.AssertId Expression) : Prop :=
  Imperative.Specification.AssertValidWhen (Lang.core π φ) (ProcEnvWF proc) verifyStmt a

/-- A procedure is correct with respect to its verification statement.

    1. Every reachable assert in the procedure evaluates to `true`
       (`AllAssertsValidWhen`);

    2. Postcondition: When the verification statement terminates from a `ProcEnvWF`
       initial environment with `hasFailure = false`, every non-free
       postcondition holds and `hasFailure` stays `false`.

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
def ProcedureCorrect (proc : Procedure) (p : Program) (verifyStmt : Statement) : Prop :=
  (∀ a, AssertValidInProcedure π φ proc verifyStmt a) ∧
  (WF.WFProcedureProp p proc →
   ∀ (ρ₀ ρ' : Env Expression),
    ProcEnvWF proc ρ₀ → ρ₀.hasFailure = Bool.false →
    CoreStepStar π φ (.stmt verifyStmt ρ₀) (.terminal ρ') →
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      ρ'.eval ρ'.store check.expr = some HasBool.tt) ∧
    ρ'.hasFailure = Bool.false)

end Core.Specification

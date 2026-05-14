/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.StatementSemanticsProps
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

/-- Store-well-formedness needed for a statement `s` to execute in env `ρ` without
    getting stuck:
    - `readWritesDefined`: vars in `touchedVars \ definedVars` are `isSome`. These are
      read (via `getVars`) or written by `set` (in `modifiedVars`); both require the
      var to already exist in the store.
    - `defsUndefined`: vars in `definedVars` are `isNone`. These are introduced by
      `init`, which requires the var to NOT already exist (matching `InitState`'s
      `σ x = none` precondition).
    - `reservedFresh`: every name in `ρ.store` whose existence is `isSome` must NOT
      start with any prefix in `reserved`. The `reserved` parameter lists name
      prefixes that downstream transforms claim ownership of (e.g., loop-elim's
      `$__loop_measure_*` and `loopElim_*`). Reserving a prefix means `ρ` does
      not pre-populate any name with that prefix, so transform-introduced names
      with that prefix are guaranteed `isNone` at entry.
    - `evalCong`, `exprCongr`: eval congruence requirements.

    The `defsUndefined` requirement simultaneously:
    - Ensures `init` commands can fire.
    - Rules out shadowing at the top-level scope (inner `init`s must not clash with
      outer bindings).
    - Allows transforms that introduce fresh init-target vars (e.g., loop-elim's
      `$__loop_measure_N`) to preserve the invariant cleanly. -/
structure InitEnvWF (reserved : List String) (s : Statement) (ρ : Env Expression) :
    Prop where
  readWritesDefined : ∀ n ∈ Stmt.touchedVars s, n ∉ Stmt.definedVars s →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Stmt.definedVars s, (ρ.store n).isNone
  definedVarsNodup : (Stmt.definedVars s).Nodup
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ reserved, ¬ p.toList.isPrefixOf n.name.toList
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfVal  : WellFormedSemanticEvalVal ρ.eval
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  evalCong : WellFormedCoreEvalCong ρ.eval
  exprCongr : WellFormedSemanticEvalExprCongr ρ.eval

/-- Block-level analog of `InitEnvWF`: well-formedness for executing a block of
    statements `bss` from env `ρ`. -/
structure BlockInitEnvWF (reserved : List String) (bss : Statements)
    (ρ : Env Expression) : Prop where
  readWritesDefined : ∀ n ∈ Block.touchedVars bss, n ∉ Block.definedVars bss →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Block.definedVars bss, (ρ.store n).isNone
  definedVarsNodup : (Block.definedVars bss).Nodup
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ reserved, ¬ p.toList.isPrefixOf n.name.toList
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfVal  : WellFormedSemanticEvalVal ρ.eval
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  evalCong : WellFormedCoreEvalCong ρ.eval
  exprCongr : WellFormedSemanticEvalExprCongr ρ.eval

/-- The `Lang Expression` bundle for Core small-step semantics, parameterised
    by a list of reserved name prefixes. Transforms that introduce fresh names
    via `init` (e.g., loop-elim's `$__loop_measure_*`) require the caller to
    reserve their prefixes, ensuring those names are absent from the entry
    store. -/
@[expose] def Lang.core
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (reserved : List String) :
    Imperative.Specification.Lang Expression :=
  Imperative.Specification.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    (InitEnvWF reserved)

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
    for initial program states satisfying the preconditions (`ProcEnvWF`).

    The `reserved` parameter lists name prefixes that downstream transforms
    own (e.g., `["$__loop"]` for loop-elim). It is propagated to `Lang.core`'s
    `initEnvWF`. The default `reserved = []` imposes no prefix constraints. -/
@[expose] def AssertValidInProcedure
    (reserved : List String)
    (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  Imperative.Specification.AssertValidWhen (Specification.Lang.core π φ reserved)
    (ProcEnvWF proc) (Stmt.block "" proc.body #[]) a

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
structure ProcedureCorrect (reserved : List String) (proc : Procedure)
    (p : Program) : Prop where
  /-- (1) The asserts in the body of proc are valid. -/
  assertsValid : ∀ a, AssertValidInProcedure π φ reserved proc a
  /-- (2) The postconditions hold on termination. -/
  postconditionsValid :
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ ρ' : Env Expression),
      ProcEnvWF proc ρ₀ →
      CoreStepStar π φ (.stmts proc.body ρ₀) (.terminal ρ') →
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.postconditions.toList →
        check.attr = Procedure.CheckAttr.Default →
        ρ'.eval ρ'.store check.expr = some HasBool.tt) ∧
      ρ'.hasFailure = Bool.false

end Core.Specification

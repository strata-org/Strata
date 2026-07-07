/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Transform.Specification
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.Factory
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.Factory

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

/-- Parameters threaded into `Core.Specification.InitEnvWF` (the Core language's
    `Lang.InitEnvWFParamsTy`).

    The `prefixIdents : List String` lists "fresh-prefixes": prefixes of
    identifiers that must NOT appear in the initial environment.  Downstream
    transforms reserve such prefixes so they can introduce fresh names with
    that prefix without colliding with user names.

    The `declaredFuncs : Expression.Ident → Bool` characterizes the set of
    operator/function names already defined in the initial evaluator.  Concrete
    instantiations use this to enforce a `defUseWellFormed` invariant that all
    operator references in the program are pre-declared, and any `funcDecl`
    introduces a fresh name. -/
structure InitEnvWFParams where
  /-- Reserved "fresh-prefixes" that must not appear in the initial env. -/
  prefixIdents : List String
  /-- Predicate of operator/function names already defined in the evaluator. -/
  declaredFuncs : Expression.Ident → Bool

/-- Store-well-formedness needed for a statement `s` to execute in env `ρ` without
    getting stuck.

    Extends `Imperative.WellFormedSemanticEval` on `ρ.factory`, which
    contributes the evaluator-level conditions `bool`/`val`/`var`/`exprCongr`/`int`.
    The remaining fields are Core-specific (store definedness, reserved-prefix
    freshness, `defUse` well-formedness, factory membership). -/
structure InitEnvWF (params : InitEnvWFParams)
    (s : Statement) (ρ : Env Expression) : Prop
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  readWritesDefined : ∀ n ∈ Stmt.touchedVars s, n ∉ Stmt.definedVars s false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Stmt.definedVars s false, (ρ.store n).isNone
  /-- Source's `definedVars` don't use any of the reserved prefixes. -/
  definedVarsNotReserved : ∀ n ∈ Stmt.definedVars s false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  /-- Source's `funcDeclNames` don't use any of the reserved prefixes.
      `funcDecl` names live in the evaluator (not the store), so they aren't
      covered by `definedVarsNotReserved`. -/
  funcDeclNamesNotReserved : ∀ n ∈ Stmt.funcDeclNames s false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  defUseOk : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs s = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true

/-- Block-level analog of `InitEnvWF`: well-formedness for executing a block of
    statements `bss` from env `ρ`. -/
structure BlockInitEnvWF (params : InitEnvWFParams)
    (bss : Statements)
    (ρ : Env Expression) : Prop
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  readWritesDefined : ∀ n ∈ Block.touchedVars bss, n ∉ Block.definedVars bss false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Block.definedVars bss false, (ρ.store n).isNone
  definedVarsNotReserved : ∀ n ∈ Block.definedVars bss false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  funcDeclNamesNotReserved : ∀ n ∈ Block.funcDeclNames bss false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  defUseOk : Block.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs bss = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true

/-- The `Lang Expression` bundle for Core small-step semantics. -/
@[expose] def Lang.core
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Specification.Lang Expression :=
  Imperative.Specification.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    (ParamsTy := InitEnvWFParams) (initEnvWF := InitEnvWF)

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
structure ProcEnvWF (proc : Procedure) (ρ : Env Expression) : Prop
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

/-! ## Procedure correctness -/

variable (π : String → Option Procedure)
variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-- A specific assertion `a` in procedure `proc` is valid
    for initial program states satisfying the preconditions (`ProcEnvWF`). -/
@[expose] def AssertValidInProcedure
    (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  match proc.body with
  | .structured ss =>
    Imperative.Specification.AssertValidWhen (Specification.Lang.core π φ)
      (ProcEnvWF proc) (Stmt.block "" ss #[]) a
  -- CFG bodies don't yet have a small-step semantics, so there is nothing to
  -- certify.  We pick `False` rather than `True` to be conservative: a CFG
  -- procedure cannot be claimed asserts-valid (and hence cannot be proven
  -- `ProcedureCorrect`) until CFG bodies gain an executable semantics.  This
  -- is sound against the current proofs because the only producer of
  -- `ProcedureCorrect` (`procBodyVerify_procedureCorrect`) is gated on
  -- `procToVerifyStmt` succeeding, which forces `proc.body = .structured _`
  -- (see `procToVerifyStmt_is_structured`), so this arm is never entered.
  | .cfg _ => False

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
      For structured bodies, the terminal factory `fac'` comes from the terminal
      `Env` (may differ from `fac` due to `funcDecl` extensions). For CFG
      bodies, `fac' = fac` since `CoreCFGStepStar` does not track factory changes. -/
  postconditionsValid :
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ : Env Expression),
      ProcEnvWF proc ρ₀ →
      ∀ (σ' : CoreStore) (fac' : Expression.Factory) (failed : Bool),
        CoreBodyExec π φ proc.body ρ₀.store ρ₀.factory σ' fac' failed →
        (∀ (label : CoreLabel) (check : Procedure.Check),
          (label, check) ∈ proc.spec.postconditions.toList →
          check.attr = Procedure.CheckAttr.Default →
          Expression.eval fac' σ' check.expr = some HasBool.tt) ∧
        failed = Bool.false

end Core.Specification

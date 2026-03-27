/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.Specification

/-! # Core-Level Specification

Bridges Core procedures to the generic Imperative specification framework
(`AssertValid`, `AllAssertsValid`, `Hoare.Triple`, `PredicatedStmt`).

## Overview

- **`coreIsAtAssert`** — assert detection for Core configs
- **`Lang.core`** — the `Lang Expression` bundle for Core small-step semantics
- **`withOldBindings`** — augments an environment with pre-state snapshots
- **`AssertValidInProcedure`** — body-assert validity under preconditions
- **`ProcedureCorrect`** — partial-correctness contract for a procedure

## Old-variable handling

`withOldBindings` augments the store of an environment `ρ₀` by mapping
`CoreIdent.mkOld g.name` to `ρ₀.store g` for each `g ∈ modifies`.
The body runs from this augmented environment, so postcondition expressions
can reference `old g` directly in the terminal store.

This is a *semantic* specification: it describes what the old-variable setup
means, not how it is implemented.  The implementation
(`ProcBodyVerify.procToVerifyStmt` emitting `set old_g := g`) is verified
separately to match this spec.
-/

namespace Core.Specification

open Core Imperative

/-! ## Assert detection for Core configs -/

/-- Assert detection for Core configurations.

    Core commands have type `Command = CmdExt Expression`, so an assert
    command appears as `.cmd (CmdExt.cmd (Cmd.assert l e md))`.
    Call commands (`.cmd (CmdExt.call ...)`) never trigger assert detection. -/
def coreIsAtAssert : CoreConfig → Imperative.AssertId Expression → Prop
  | .stmt (.cmd (.cmd (.assert label expr _))) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.cmd (.assert label expr _))) :: _) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .block _ inner, aid => coreIsAtAssert inner aid
  | .seq inner _, aid => coreIsAtAssert inner aid
  | _, _ => False

/-! ## Core `Lang` bundle -/

/-- The `Lang Expression` bundle for Core small-step semantics. -/
def Lang.core
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Specification.Lang Expression :=
  Imperative.Specification.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert

/-! ## Old-variable environment augmentation -/

/-- Augment an environment with old-variable bindings for the modifies clause.

    For each `g ∈ modifies`, the store is extended so that
    `(withOldBindings modifies ρ).store (CoreIdent.mkOld g.name) = ρ.store g`.
    All other store lookups (including `g` itself) are unchanged.
    The evaluator and `hasFailure` flag are preserved. -/
def withOldBindings
    (modifies : List Expression.Ident) (ρ : Env Expression) : Env Expression :=
  { ρ with store := fun id =>
      match modifies.find? (fun g => CoreIdent.mkOld g.name == id) with
      | some g => ρ.store g
      | none   => ρ.store id }

/-! ## Procedure correctness -/

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

/-- The precondition for a procedure: all preconditions hold,
    the evaluator is well-formed, and no prior failure. -/
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

/-- A specific assertion is valid in a procedure body.

    For all initial environments satisfying `ProcedurePre`, the body runs
    from `procStartEnv` (augmented with old-variable bindings).  Whenever
    execution reaches a configuration at assert `a`, the assert expression
    evaluates to `true`.

    This is a restricted form of `AssertValid`.  The implementation
    (`ProcBodyVerify`) emits `set` and `assume` commands that realise
    this restriction; proving its soundness connects `AssertValid` of the
    implementation to this specification. -/
def AssertValidInProcedure
    (proc : Procedure) (a : Imperative.AssertId Expression) : Prop :=
  ∀ (ρ₀ : Env Expression) (cfg : CoreConfig),
    ProcedurePre proc ρ₀ →
    CoreStepStar π φ (.stmts proc.body (procStartEnv proc ρ₀)) cfg →
    coreIsAtAssert cfg a →
    cfg.getEval cfg.getStore a.expr = some HasBool.tt

/-- A procedure is correct (partial-correctness).

    For all initial environments satisfying `ProcedurePre`:

    1. Every body-internal assert is valid (`AssertValidInProcedure`).

    2. If the body terminates at `ρ'`, every non-free postcondition holds.
       The terminal store contains both post-state values and `old_g`
       snapshots from the pre-state (set by `procStartEnv`).

    3. On termination, `hasFailure = false`. -/
def ProcedureCorrect (proc : Procedure) : Prop :=
  -- All body asserts pass
  (∀ a, AssertValidInProcedure π φ proc a) ∧
  -- Postconditions hold on termination
  (∀ (ρ₀ ρ' : Env Expression),
    ProcedurePre proc ρ₀ →
    CoreStepStar π φ (.stmts proc.body (procStartEnv proc ρ₀)) (.terminal ρ') →
    (∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      ρ'.eval ρ'.store check.expr = some HasBool.tt) ∧
    ρ'.hasFailure = Bool.false)

/-! ## Statement-level definitions (for `Sound` compatibility) -/

/-- Validity of a specific assertion in a Core statement.
    This is `AssertValid` of `Lang.core`, specialised to Core. -/
def AssertValidInStmt
    (stmt : Statement) (a : Imperative.AssertId Expression) : Prop :=
  Imperative.Specification.AssertValid (Lang.core π φ) stmt a

/-- All asserts in a Core statement are valid. -/
def StmtCorrect (stmt : Statement) : Prop :=
  Imperative.Specification.AllAssertsValid (Lang.core π φ) stmt

end Core.Specification

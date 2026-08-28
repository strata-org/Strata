/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Program
import all Strata.Languages.Core.Logic.Hoare

/-! # A procedure's contract, read as a Hoare triple

A Core procedure carries its own specification: `spec { requires …; ensures …; }`.
Read as a Hoare triple, the preconditions are the precondition and the
(non-`free`) postconditions are the postcondition, over the procedure's body.
`Procedure.contractTriple` packages that reading, so that "this procedure meets
its contract" becomes a single `Strata.Logic.Hoare` judgement.

The postcondition drops `free` `ensures` checks: those are assumed at the call sites rather
than proved by the body, exactly as `Core.Specification.ProcedureAssertsValid`
treats them.
The `free` `requires` checks are still included in the precondition of the Hoare triple,
because the caller will guarantee them 'for free' (caller will not have to actually prove the `free` `requires` conditions).

## Where this sits

`Strata.Languages.Core.Logic.Hoare` is the logic: the judgements and the structural
rules.  This module is the *reading* that connects it to Core's surface language —
how a `Procedure`'s `spec { requires …; ensures …; }` becomes a pre/postcondition
pair.  Kept separate because none of it is part of the logic proper.

## Key results

- `Procedure.preAsPredicate` / `Procedure.postAsPredicate` — the two halves of the
  reading; the latter drops `free` clauses.
- `Procedure.contractTriple` — "the procedure named `procName` in `p` meets its
  contract", as a single judgement.  It names the procedure rather than taking it, so
  the environment a `call` resolves against is `p`'s own `findProcByString?` by
  construction, and it is existential in both the procedure and its body so that
  neither an unresolvable name nor a `.cfg` body makes it vacuous.
- `Procedure.ensuresAmongRequires` / `preHoldsAt` / `postRefutedAt` — the `Bool`
  decision procedures for the clause-list conditions above.

Ways to *establish* a `contractTriple`, and the lemmas relating the `Bool` checks back
to the propositions, are in `Strata.Languages.Core.Logic.ContractToHoareTripleProps`.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-- A procedure's preconditions, as a predicate on the initial environment. -/
@[expose] def Procedure.preAsPredicate (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    Expression.eval ρ.factory ρ.store check.expr = some HasBool.tt

/-- A procedure's non-`free` postconditions, as a predicate on the final
    environment. -/
@[expose] def Procedure.postAsPredicate (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.postconditions.toList →
    check.attr = Procedure.CheckAttr.Default →
    Expression.eval ρ.factory ρ.store check.expr = some HasBool.tt

/-- **The Hoare triple a procedure's contract asserts about its body.**

    `{ requires } body { ensures }` as a `Triple` over the body wrapped in its procedure
    block `Stmt.block "" bss #[]`, so the `ensures` are checked at the environment that
    block leaves behind (an `ensures` naming a variable the body *declares* is therefore
    false — leaving the block drops it).  Partial correctness: a diverging body satisfies
    any contract, so this is the contract obligation, not the whole of
    `ProcedureAssertsValid`.

    The precondition pins the initial environment to `Core.Factory`, so a body proof may
    use the concrete evaluator's operator semantics; over an arbitrary well-formed factory
    those value laws are unspecified.  Discharge with `contractTriple_of` (factory
    discarded) or `contractTriple_of_core` (factory assumption kept). -/
@[expose] def Procedure.contractTriple (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) : Prop :=
  ∃ proc bss, p.findProcByString? procName = some proc ∧
    proc.body = .structured bss ∧
    Triple p.findProcByString? φ params
      (fun ρ => Procedure.preAsPredicate proc ρ ∧ ρ.factory = Core.Factory)
      [Imperative.Stmt.block "" bss #[]] (Procedure.postAsPredicate proc)

/-! ### Decidable bridges to a procedure's contract

`preAsPredicate` / `postAsPredicate` quantify over the spec's clause lists, so at
a *concrete* procedure and environment they are decidable.  The three `Bool`
functions below are those decision procedures, and the lemmas relate them back to
the propositions.  They exist so that a test can settle a concrete contract with
`decide` / `native_decide` instead of unfolding a DDM-translated AST by hand. -/

/-- Every non-`free` `ensures` expression also occurs among the `requires`. -/
@[expose] def Procedure.ensuresAmongRequires (proc : Procedure) : Bool :=
  proc.spec.postconditions.toList.all fun lc =>
    decide (lc.2.attr ≠ Procedure.CheckAttr.Default) ||
      proc.spec.preconditions.toList.any fun lc' => decide (lc'.2.expr = lc.2.expr)

/-- Every `requires` evaluates to `true` in `ρ`. -/
@[expose] def Procedure.preHoldsAt (proc : Procedure) (ρ : Imperative.Env Expression) : Bool :=
  proc.spec.preconditions.toList.all fun lc =>
    decide (Expression.eval ρ.factory ρ.store lc.2.expr = some HasBool.tt)

/-- Some non-`free` `ensures` fails to evaluate to `true` in `ρ` — a witness that
    `postAsPredicate` is *false* there. -/
@[expose] def Procedure.postRefutedAt (proc : Procedure) (ρ : Imperative.Env Expression) : Bool :=
  proc.spec.postconditions.toList.any fun lc =>
    decide (lc.2.attr = Procedure.CheckAttr.Default) &&
      decide (Expression.eval ρ.factory ρ.store lc.2.expr ≠ some HasBool.tt)

end Hoare

end Core.Logic

end -- public section

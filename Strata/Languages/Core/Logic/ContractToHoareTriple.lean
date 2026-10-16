/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.HoareUnstructured
public import Strata.Languages.Core.Program
import Strata.DL.Lambda.LExprType
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
- `Procedure.oldInoutAsPredicate` — the entry relation between each inout formal and its
  `old` snapshot, carried in `contractTriple`'s precondition.
- `Procedure.valueHasType` / `Procedure.inputAsPredicate` — connect runtime input
  values to the types declared by the procedure signature.
- `Procedure.contractTriple` — "the procedure named `procName` in `p` meets its
  contract", as a single judgement.  It names the procedure rather than taking it, so
  the environment a `call` resolves against is `p`'s own `findProcByString?` by
  construction, and dispatches on the resolved procedure's body so neither an
  unresolvable name nor either body representation makes the obligation vacuous.
- `Procedure.ensuresAmongRequires` / `preHoldsAt` / `postRefutedAt` — the `Bool`
  decision procedures for the clause-list conditions above.

Ways to *establish* a `contractTriple`, and the lemmas relating the `Bool` checks back
to the propositions, are in `ContractToHoareTripleProps`. The call rule that
consumes one is in `HoareCall`.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare


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

/-- The `old`-snapshot relation a procedure's inout parameters carry into its body:
    for every id among the keys of `proc.header.getInoutParams`, `old id` holds the
    same value as `id` itself. -/
@[expose] def Procedure.oldInoutAsPredicate (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  ∀ id ∈ ListMap.keys proc.header.getInoutParams,
    ρ.store (CoreIdent.mkOld id.name) = ρ.store id

/-- Runtime values matching a declared Core type. Integers and bitvectors use
their literal runtime representations; other values must type-check as closed
expressions.

TODO: this represents the executable subset of a value. Once the computable
subset of values of ty is defined, valueHasType will have to be replaced with
the function.
-/
@[expose] def Procedure.valueHasType (ty : Lambda.LMonoTy)
    (v : Expression.Expr) : Prop :=
  match ty with
  | .int => ∃ i : Int, v = Lambda.LExpr.intConst () i
  | .bitvec n => ∃ b : BitVec n, v = Lambda.LExpr.bitvecConst () n b
  | _ => Lambda.LExpr.typeCheck [] v = some ty

/-- Every input and inout formal is bound to a value matching its declared type. -/
@[expose] def Procedure.inputAsPredicate (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  ∀ id ty, (id, ty) ∈ proc.header.inputs.toList →
    ∃ v, ρ.store id = some v ∧ Procedure.valueHasType ty v

/-- Entry condition shared by structured and CFG readings of a procedure contract. -/
@[expose] def Procedure.contractPre (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  Procedure.preAsPredicate proc ρ ∧ ρ.factory = Core.Factory ∧
    Procedure.oldInoutAsPredicate proc ρ ∧ Procedure.inputAsPredicate proc ρ

/-- **The Hoare triple a procedure's contract asserts about its body.**

    Structured bodies use `EventLang.coreBlock` over the body wrapped in its
    procedure block, so body-local declarations are dropped before checking the
    postcondition. CFG bodies use `TripleUnstructured`, backed by
    `EventLang.coreCFG`, from their entry block to a terminal configuration. The
    CFG reading matches the structured one by checking the postcondition on the
    final store *projected through the entry store*, dropping CFG-local
    declarations just as the procedure block drops its locals. The entry
    environment is universally quantified and pinned in the precondition
    (`ρ = ρEntry`) so the postcondition predicate, which only sees the final
    environment, can still refer to the entry store.
    Both readings use the same contract precondition and postcondition.

    The precondition pins the initial environment to `Core.Factory`, carries the
    entry snapshots of inout parameters, and requires every input value to match
    its declared type. Partial correctness means a diverging body satisfies any
    postcondition. -/
@[expose] def Procedure.contractTriple (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) : Prop :=
  ∃ proc, p.findProcByString? procName = some proc ∧
    match proc.body with
    | .structured bss =>
        Triple p.findProcByString? params (Procedure.contractPre proc)
          [Imperative.Stmt.block "" bss #[]] (Procedure.postAsPredicate proc)
    | .cfg cfg =>
        ∀ ρEntry, TripleUnstructured p.findProcByString? params
          (fun ρ => Procedure.contractPre proc ρ ∧ ρ = ρEntry) cfg
          (fun ρ' => Procedure.postAsPredicate proc
            { ρ' with store := Imperative.projectStore ρEntry.store ρ'.store })

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

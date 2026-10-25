/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.FactoryInterp
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

- `Procedure.preAsPredicate` / `Procedure.postAsPredicate` — the model-indexed contract
  clauses; the latter drops `free` clauses.
- `Procedure.oldInoutAsPredicate` — the entry relation between each inout formal and its
  `old` snapshot, carried in `contractTriple`'s precondition.
- `Procedure.valueHasType` / `Procedure.inputAsPredicate` /
  `Procedure.outputAsPredicate` — connect runtime parameter values to the types declared
  by the procedure signature.
- `Procedure.contractTriple` — "the procedure named `procName` in `p` meets its
  contract", as a single judgement.  It names the procedure rather than taking it, so
  the environment a `call` resolves against is `p`'s own `findProcByString?` by
  construction, and dispatches on the resolved procedure's body so neither an
  unresolvable name nor either body representation makes the obligation vacuous.
- `Procedure.ensuresAmongRequires` — the structural check that every non-`free`
  postcondition also occurs among the preconditions.
- `Procedure.contractChecksTyped` — a conjunct of `contractTriple` requiring every
  `requires`/`ensures` expression to type-check at `bool`, so an ill-typed clause cannot
  make the obligation vacuous.

Ways to *establish* a `contractTriple`, and the lemmas relating the `Bool` checks back
to the propositions, are in `ContractToHoareTripleProps`. The call rule that
consumes one is in `HoareCall`.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare


/-- A captured contract check holds in every valuation of `model`.

The intended justification for this universal closure is that a checked procedure
is monomorphic and every free term variable in a contract clause is bound in the
captured register file. `capturedExpr` then substitutes those stored expressions,
so denotation consults neither `world.freeVarVal` nor `world.tyVarVal` and cannot
vary with `world`.

This definition does not itself carry that closure invariant:
`substFvarsFromEnv` leaves a variable unchanged when the store has no binding,
and `contractChecksTyped` does not prove the absence of residual type variables.

TODO: Prove and require the closure invariant from the typed Core pipeline. If
open or polymorphic contract clauses are instead supported directly, take
`world` as an argument and thread that same valuation through the precondition,
body trace interpretation, and postcondition. -/
@[expose] def Procedure.checkAsPredicate (model : Lambda.Interp Core.Factory)
    (ρ : Imperative.Env Expression) (label : CoreLabel)
    (check : Procedure.Check) : Prop :=
  ∀ world, (DenoteBasedInterp model).holds world
    { factory := ρ.factory, store := ρ.store, label := label,
      expr := check.expr, metadata := check.md }

/-- A procedure's preconditions in one model. -/
@[expose] def Procedure.preAsPredicate (model : Lambda.Interp Core.Factory)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    Procedure.checkAsPredicate model ρ label check

/-- A procedure's non-`free` postconditions in one model. -/
@[expose] def Procedure.postAsPredicate (model : Lambda.Interp Core.Factory)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.postconditions.toList →
    check.attr = Procedure.CheckAttr.Default →
    Procedure.checkAsPredicate model ρ label check

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

/-- Every output and inout formal is bound to a value matching its declared type. -/
@[expose] def Procedure.outputAsPredicate (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  ∀ id ty, (id, ty) ∈ proc.header.outputs.toList →
    ∃ v, ρ.store id = some v ∧ Procedure.valueHasType ty v

/-- Entry condition shared by structured and CFG readings of a procedure contract. -/
@[expose] def Procedure.contractPre (model : Lambda.Interp Core.Factory)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  Procedure.preAsPredicate model proc ρ ∧ ρ.factory = Core.Factory ∧
    Procedure.oldInoutAsPredicate proc ρ ∧ Procedure.inputAsPredicate proc ρ

/-- Exit condition shared by structured and CFG readings of a procedure contract. -/
@[expose] def Procedure.contractPost (model : Lambda.Interp Core.Factory)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  Procedure.postAsPredicate model proc ρ

/-- Every `requires` and `ensures` expression type-checks as `bool`. This is a
    conjunct of `contractTriple`, so malformed clauses are rejected independently of
    precondition satisfaction. -/
@[expose, reducible] def Procedure.contractChecksTyped (proc : Procedure) : Prop :=
  (proc.spec.preconditions.toList.all fun lc =>
      decide (Lambda.LExpr.typeCheck [] lc.2.expr = some .bool)) = Bool.true ∧
    (proc.spec.postconditions.toList.all fun lc =>
      decide (Lambda.LExpr.typeCheck [] lc.2.expr = some .bool)) = Bool.true

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

    Current scope: this judgement is intended for typed pipeline procedures whose
    captured contract clauses satisfy the world-independence invariant described
    on `checkAsPredicate`; that invariant is not yet carried as a hypothesis here.

    The precondition pins the initial environment to `Core.Factory`, carries the
    entry snapshots of inout parameters, and requires every input value to match
    its declared type. Partial correctness means a diverging body satisfies any
    postcondition. -/
@[expose] def Procedure.contractTriple (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) : Prop :=
  ∃ proc, p.findProcByString? procName = some proc ∧
    Procedure.contractChecksTyped proc ∧
    ∀ model : Lambda.Interp Core.Factory,
      match proc.body with
      | .structured bss =>
          TripleWithModel p.findProcByString? model params
            (Procedure.contractPre model proc)
            [Imperative.Stmt.block "" bss #[]] (Procedure.contractPost model proc)
      | .cfg cfg =>
          ∀ ρEntry, TripleUnstructuredWith p.findProcByString?
            (DenoteBasedInterp model) params
            (fun ρ => Procedure.contractPre model proc ρ ∧ ρ = ρEntry) cfg
            (fun ρ' => Procedure.contractPost model proc
              { ρ' with store := Imperative.projectStore ρEntry.store ρ'.store })

/-- Every non-`free` `ensures` expression also occurs among the `requires`. -/
@[expose] def Procedure.ensuresAmongRequires (proc : Procedure) : Bool :=
  proc.spec.postconditions.toList.all fun lc =>
    decide (lc.2.attr ≠ Procedure.CheckAttr.Default) ||
      proc.spec.preconditions.toList.any fun lc' => decide (lc'.2.expr = lc.2.expr)

end Hoare

end Core.Logic

end -- public section

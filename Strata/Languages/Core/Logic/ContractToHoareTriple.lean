/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.FactoryInterp
public import Strata.Languages.Core.Logic.HoareUnstructured
public import Strata.Languages.Core.Logic.HoareTotal
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Analysis.ProcedureCorrectness
import Strata.DL.Lambda.LExprType
import all Strata.Languages.Core.Logic.Hoare

/-! # A procedure's contract, read as a Hoare triple

A Core procedure carries its own specification: `spec { requires …; ensures …; }`.
Read as a Hoare triple, the preconditions are the precondition and the
(non-`free`) postconditions are the postcondition, over the procedure's body.
`Procedure.contractTriple` packages that reading, so that "this procedure meets
its contract" becomes a single `Strata.Logic.Hoare` judgement.

The postcondition drops `free` `ensures` checks: those are assumed at the call sites rather
than proved by the body, matching `Core.Specification.ProcedureAssertsValidOnTraces`.
The `free` `requires` checks are still included in the precondition of the Hoare triple,
because the caller will guarantee them 'for free' (caller will not have to actually prove the `free` `requires` conditions).

## Where this sits

`Strata.Languages.Core.Logic.Hoare` is the logic: the judgements and the structural
rules.  This module is the *reading* that connects it to Core's surface language —
how a `Procedure`'s `spec { requires …; ensures …; }` becomes a pre/postcondition
pair.  Kept separate because none of it is part of the logic proper.

## Key results

- `Procedure.preAsPredicate` / `Procedure.postAsPredicate` — the contract clauses read
  over a factory; the latter drops `free` clauses.
- `Procedure.oldInoutAsPredicate` — the entry relation between each inout formal and its
  `old` snapshot, carried in `contractTriple`'s precondition.
- `Procedure.valueHasType` / `Procedure.inputAsPredicate` /
  `Procedure.outputAsPredicate` — connect runtime parameter values to the types declared
  by the procedure signature.
- `Procedure.contractTriple` — "the procedure named `procName` in `p` meets its
  contract", as a single judgement, at every instance of its type parameters
  (`Procedure.instantiateTypes`).  It names the procedure rather than taking it, so
  the environment a `call` resolves against is `p`'s own `findProcByString?` by
  construction, and dispatches on the resolved procedure's body so neither an
  unresolvable name nor either body representation makes the obligation vacuous.
  Its precondition also assumes the axioms and `distinct` declarations visible to the
  procedure (`Core.Specification.AxiomsBeforeProcedureDecl`), as
  `Core.Specification.ProcEntryEnv` does.
- `Procedure.contractTripleTotal` — the total-correctness counterpart of `contractTriple`,
  with the same precondition and postcondition: the body also terminates with valid assertions from
  every admitted entry satisfying the precondition.
- `Procedure.bodyTerminatesAndAssertsValid` — that termination on its own, for either body
  kind.
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


/-- A captured contract check holds in every world over `factory`.  On a runtime factory
over `factory` the check holds exactly when it evaluates to `true`, so the universal
closure over worlds only matters for checks captured under another runtime factory.

A check evaluates only when every free variable is bound in the captured store and the
clause type checks at a ground type; otherwise it does not hold.  The intended
justification is that a checked procedure is monomorphic and every free term variable
in a contract clause is bound in the captured register file.

This definition does not itself carry that invariant.

TODO: Prove and require the invariant from the typed Core pipeline: every contract
clause of a checked procedure evaluates in the stores it is captured in.  Without it,
a clause that fails to evaluate makes a precondition unsatisfiable and a postcondition
unprovable instead of being rejected.  If open or polymorphic contract clauses are
instead supported directly, thread a valuation of the extra variables through the
precondition, body trace interpretation, and postcondition. -/
@[expose] def Procedure.checkAsPredicate (factory : Lambda.Factory CoreLParams)
    (ρ : Imperative.Env Expression) (label : CoreLabel)
    (check : Procedure.Check) : Prop :=
  ∀ world, (DenoteBasedInterp factory).holds world
    { factory := ρ.factory, store := ρ.store, label := label,
      expr := check.expr, metadata := check.md }

/-- A procedure's preconditions, read over `factory`. -/
@[expose] def Procedure.preAsPredicate (factory : Lambda.Factory CoreLParams)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    Procedure.checkAsPredicate factory ρ label check

/-- A procedure's non-`free` postconditions, read over `factory`. -/
@[expose] def Procedure.postAsPredicate (factory : Lambda.Factory CoreLParams)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.postconditions.toList →
    check.attr = Procedure.CheckAttr.Default →
    Procedure.checkAsPredicate factory ρ label check

/-- The `old`-snapshot relation a procedure's inout parameters carry into its body:
    for every id among the keys of `proc.header.getInoutParams`, `old id` holds the
    same value as `id` itself. -/
@[expose] def Procedure.oldInoutAsPredicate (proc : Procedure)
    (ρ : Imperative.Env Expression) : Prop :=
  ∀ id ∈ ListMap.keys proc.header.getInoutParams,
    ρ.store (CoreIdent.mkOld id.name) = ρ.store id

/-- A runtime value matches a declared Core type when its sort is that type. -/
@[expose] def Procedure.valueHasType (ty : Lambda.LMonoTy)
    (v : Expression.Val) : Prop :=
  v.sort.toMonoTy = ty

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

/-- Entry condition shared by structured and CFG readings of a procedure contract: the
    preconditions hold, the runtime factory is over `factory`, the inout formals match their
    `old` snapshots, and the input, inout and output formals hold values of their declared
    types. -/
@[expose] def Procedure.contractPre (factory : Lambda.Factory CoreLParams)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  Procedure.preAsPredicate factory proc ρ ∧ ρ.factory.factory = factory ∧
    Procedure.oldInoutAsPredicate proc ρ ∧ Procedure.inputAsPredicate proc ρ ∧
    Procedure.outputAsPredicate proc ρ

/-- Exit condition shared by structured and CFG readings of a procedure contract. -/
@[expose] def Procedure.contractPost (factory : Lambda.Factory CoreLParams)
    (proc : Procedure) (ρ : Imperative.Env Expression) : Prop :=
  Procedure.postAsPredicate factory proc ρ

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
    Both readings use the same contract precondition and postcondition. An abstract
    procedure has no body to check against its contract, which is trusted: its judgement is
    `True`.

    A polymorphic procedure must meet its contract at every instance a call can run: for every
    list of type arguments `tys` that instantiates it (`Procedure.instantiateTypes`), the
    instantiated procedure's body meets the instantiated contract.  A monomorphic procedure
    has one instance, itself, at `[]`.

    Current scope: this judgement is intended for typed pipeline procedures whose
    contract clauses evaluate in the stores they are captured in (the invariant
    described on `checkAsPredicate`); that invariant is not yet carried as a
    hypothesis here.

    The precondition pins the initial environment's runtime factory to one over
    `p.factoryBeforeProcedure procName` (with any model of it), carries the entry
    snapshots of inout parameters, and requires every input and output value to match its
    declared type, as the entries of deductive verification do (`ProcEnvWF`). It also
    assumes the axioms and `distinct` declarations that precede the procedure in `p`
    (`Core.Specification.AxiomsBeforeProcedureDecl`), the entry assumption of
    `Core.Specification.ProcEntryEnv`, so a body proof may use them and the triple
    quantifies over the models that satisfy them.
    On a well-formed program, the factory contains Core's built-ins and exactly
    the user-defined functions declared before the procedure and the functions
    generated for the datatypes declared before it. Partial correctness
    means a diverging body satisfies any postcondition, though its assertions must still
    hold on every finite execution, finished or not. -/
@[expose] def Procedure.contractTriple (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) : Prop :=
  ∃ proc₀, p.findProcByString? procName = some proc₀ ∧
    ∀ tys proc, proc₀.instantiateTypes tys = some proc →
    Procedure.contractChecksTyped proc ∧
      match proc.body with
      | .structured bss _ =>
          Triple p.findProcByString? params
            (fun ρ => Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
              Core.Specification.AxiomsBeforeProcedureDecl procName p ρ)
            [Imperative.Stmt.block "" bss #[]]
            (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
            (factory := p.factoryBeforeProcedure procName)
      | .cfg cfg _ =>
          ∀ ρEntry, TripleUnstructured p.findProcByString? params
            (fun ρ => (Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
              Core.Specification.AxiomsBeforeProcedureDecl procName p ρ) ∧
              ρ = ρEntry) cfg
            (fun ρ' => Procedure.contractPost (p.factoryBeforeProcedure procName) proc
              { ρ' with store := Imperative.projectStore ρEntry.store ρ'.store })
            (factory := p.factoryBeforeProcedure procName)
      | .abstract => True

/-- **The total-correctness Hoare triple a procedure's contract asserts about its body.**

    The counterpart of `Procedure.contractTriple`, with the same precondition and
    postcondition, and `HoareTotal.Triple` and `HoareTotal.TripleUnstructured` in place of
    `Triple` and `TripleUnstructured`, at every instance of the procedure as there: it is
    `contractTriple` together with termination
    with valid assertions of the body from every admitted entry satisfying the precondition
    (`Procedure.contractTripleTotal_iff`).  The output typing in the precondition matters
    here: an assignment to an output steps only to a value of the type of the value the
    output holds, so a body writing an output that holds a value of another type would get
    stuck. -/
@[expose] def Procedure.contractTripleTotal (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) : Prop :=
  ∃ proc₀, p.findProcByString? procName = some proc₀ ∧
    ∀ tys proc, proc₀.instantiateTypes tys = some proc →
    Procedure.contractChecksTyped proc ∧
      match proc.body with
      | .structured bss _ =>
          HoareTotal.Triple p.findProcByString? params
            (fun ρ => Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
              Core.Specification.AxiomsBeforeProcedureDecl procName p ρ)
            [Imperative.Stmt.block "" bss #[]]
            (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
            (factory := p.factoryBeforeProcedure procName)
      | .cfg cfg _ =>
          ∀ ρEntry, HoareTotal.TripleUnstructured p.findProcByString? params
            (fun ρ => (Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
              Core.Specification.AxiomsBeforeProcedureDecl procName p ρ) ∧
              ρ = ρEntry) cfg
            (fun ρ' => Procedure.contractPost (p.factoryBeforeProcedure procName) proc
              { ρ' with store := Imperative.projectStore ρEntry.store ρ'.store })
            (factory := p.factoryBeforeProcedure procName)
      | .abstract => True

/-- **The body of the procedure named `procName` in `p` terminates with valid assertions**, at
    every instance of the procedure (`Procedure.instantiateTypes`), from
    every entry admitted by the body's gate that satisfies `contractTriple`'s precondition:
    in every world, every execution of the body whose assumptions hold there terminates and
    has its assertions hold there.  With
    `contractTriple`, it makes up `contractTripleTotal` (`Procedure.contractTripleTotal_iff`). -/
@[expose] def Procedure.bodyTerminatesAndAssertsValid (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) : Prop :=
  ∃ proc₀, p.findProcByString? procName = some proc₀ ∧
    ∀ tys proc, proc₀.instantiateTypes tys = some proc →
      match proc.body with
      | .structured bss _ =>
          ∀ ρ, Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
              Core.Specification.AxiomsBeforeProcedureDecl procName p ρ →
            BlockInitEnvWF params [Imperative.Stmt.block "" bss #[]] ρ →
            (EventLang.coreBlock p.findProcByString?).TerminatesAndAssertsValid
              (DenoteBasedInterp (p.factoryBeforeProcedure procName))
              [Imperative.Stmt.block "" bss #[]] ρ
      | .cfg cfg _ =>
          ∀ ρ, Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
              Core.Specification.AxiomsBeforeProcedureDecl procName p ρ →
            CFGInitEnvWF params cfg ρ →
            (EventLang.coreCFG p.findProcByString?).TerminatesAndAssertsValid
              (DenoteBasedInterp (p.factoryBeforeProcedure procName)) cfg ρ
      | .abstract => True

/-- Every non-`free` `ensures` expression also occurs among the `requires`. -/
@[expose] def Procedure.ensuresAmongRequires (proc : Procedure) : Bool :=
  proc.spec.postconditions.toList.all fun lc =>
    decide (lc.2.attr ≠ Procedure.CheckAttr.Default) ||
      proc.spec.preconditions.toList.any fun lc' => decide (lc'.2.expr = lc.2.expr)

end Hoare

end Core.Logic

end -- public section

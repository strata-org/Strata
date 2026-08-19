/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.DL.Lambda.LExprWF
public import Strata.Pipeline.FactSet

/-! # Program facts

A `ProgramFact` is a property of a program that the pipeline framework
tracks: a phase may require it of its input, establish it on its output, or
preserve it through its body. Every fact here happens to be a property of the
program's form, decidable by inspecting it, but nothing in the framework asks
for that: a fact such as termination would be a proposition with no check.

This module carries the fact enum, what it means for a list of facts to be
*canonical*, and what each fact says about a program. It is split from
`ProgramFactSet` because that module's tactic reflects on `ProgramFact.all` and so
must import this one at `meta` level.

The predicates the facts are built from live with the constructs they inspect:
the command-independent statement shapes in `Imperative.Stmt`, the ones that
mention a Core command in `Core.Statement`, the lifts to a body, declaration
and program in `Core.Procedure` and `Core.Program`, and the redex check in
`Lambda.LExprWF`. -/

namespace Core

public section

/-- Property of a program tracked by the pipeline framework.
    Closed enum, kept in sync with `ProgramFact.holds` and `ProgramFact.check`
    below and the list `ProgramFact.all`.

    **Constraint: nullary constructors only.** The framework's
    expression-to-value reduction (`reduceFactList` in
    `ProgramFactSet.lean`) matches on the head constant of a `ProgramFact`
    expression and looks it up in `ProgramFact.all`. A parameterised
    constructor `| boundedDepth (n : Nat)` would have the same head for
    every `n` but represent distinct facts; the reflection layer would
    conflate them. If parameterised facts are ever needed, the
    reflection layer must be redesigned. -/
inductive ProgramFact where
  /-- Every procedure body is `.structured _` (not `.cfg _`).
      Required by every statement-level transform, because
      `Transform.runProgram` throws on a CFG body, and by symbolic
      evaluation, which reports "CFG bodies not supported yet". -/
  | noCFGBodies
  /-- No procedure body contains a `call` command, in a statement or in a
      CFG block. Established by call elimination, which replaces each call
      by its callee's contract. -/
  | noCalls
  /-- No procedure body contains a `loop` statement. Established by loop
      elimination and required by symbolic evaluation, which rejects a `loop`
      through its error channel. -/
  | noLoops
  /-- No `loop` carries invariants. Established by
      `InsertLoopInvariantAsserts`, which materializes them as
      `assert`/`assume` statements and clears the clause, and required by
      `LoopElim`, which throws on a loop that still carries one. -/
  | noLoopInvariants
  /-- No `loop` carries a `decreases` measure. Established and required by
      the same two phases as `noLoopInvariants`, for the same reason: the
      measure's verification conditions have to be materialized before the
      loop is dissolved. -/
  | noLoopMeasures
  /-- Every variable is written exactly once: no `set` (and so no `havoc`,
      which is a `set` to a nondeterministic value) overwrites a variable.
      This is the assignment half of SSA only: shadowing an outer `init`
      satisfies it, so if the SMT conversion needs distinct names, that is a
      separate fact.

      This is what the final SMT conversion needs — an SMT formula has no
      notion of a variable changing value — and it is what symbolic
      evaluation delivers: its output carries no assignment at all, each one
      having been resolved into the obligation's expressions on the way. The
      phases before it neither hold it nor claim it: they insert `havoc`s.

      A phase that emits a `havoc` or a `set` cannot preserve this fact, which
      is why `CallElim` (it havocs a call's outputs) and `LoopElim` (it havocs
      the variables a loop writes) leave it unclaimed. -/
  | staticSingleAssignment
  /-- No expression is an `.app` of an `.abs`. Established by `BetaReduce`
      and needed by the SMT encoder, which rejects an application of an
      abstraction: front-end lowerings introduce such a redex whenever they
      name an intermediate value with a `let`-style binding.

      This is a property of the encoder as it stands, not of SMT. SMT-LIB has
      `let`, and `SMT.Term` could grow a binder for it; until then the redex
      has to be contracted before encoding, and this fact is what says so.

      A phase that instantiates a contract, a precondition or a measure by
      substituting a call's actual arguments for its formals cannot preserve
      this fact: a function-typed formal that is applied, given an abstraction
      as its actual, leaves an application of an abstraction behind. That rules
      it out for `CallElim`, `PrecondElim` and `TerminationCheck` even though
      first-order programs are unaffected, and partial-evaluation inlining
      rules it out for symbolic evaluation. -/
  | noBetaRedexes
  /-- No function carries a precondition, at top level or declared inside a
      procedure body. Established by `PrecondElim`, which turns each into an
      `assert` at the call sites and a well-formedness check on the contracts.
      Required by the SMT encoder rather than by a phase: a precondition that
      survives is a proof obligation nothing downstream generates, and the
      encoder relies on it having been checked when it encodes `SafeDiv`,
      `SafeMod` and the safe bitvector operations as total. -/
  | noPrecondsFromFuncs
  /-- No `ite` or `loop` guard is nondeterministic. Established by `NondetElim`,
      which replaces such a guard with a fresh boolean it initializes, and by a
      loop also havocs at the end of the body. Required by symbolic evaluation,
      which rejects a nondeterministic guard outright.

      Not required by the back end: obligation extraction accepts a
      nondeterministic `ite`, and symbolic evaluation has removed every guard by
      the time the program reaches it. -/
  | noNondetGuards
  /-- No procedure body declares a function. Established by
      `LiftInternalFuncDecls`, which makes each local function a closed
      top-level one. Required by `MonomorphizeFunctions`, which specializes
      top-level function declarations, and by the back end, which has no
      encoding for a function declared inside a body. -/
  | noInternalFuncDecl
  /-- No procedure carries type parameters. Established by
      `MonomorphizeProcedures`, which specializes each polymorphic procedure and
      clears `header.typeArgs`. Required by the back end: SMT has no
      procedure-level polymorphism to encode. -/
  | noPolymorphicProcedures
  /-- No function carries type parameters, wherever it is declared. Established
      by `MonomorphizeFunctions`, which replaces a polymorphic function by
      copies at the instantiations reached from the program. Required by the back
      end, since an SMT function symbol has one signature. -/
  | noPolymorphicFunctions
  deriving DecidableEq, Repr

/-! ### Adding a fact

Add a fact when some code already refuses to work without the property it names:
a transform that rejects input of the wrong shape, or a consumer downstream of the
pipeline that cannot accept anything else. Every fact above comes from such a
place.

Adding a constructor is deliberately not a local edit: a phase's `preserves`
is usually an explicit `factSet![…]` literal, so a new fact is claimed by
nobody until each phase's contract is revisited. That is the point — a fact
silently inherited by every phase would assert something no one checked. The
exception is a phase that changes nothing, which preserves `ProgramFactSet.all`
by construction.

### The lowering's preconditions

`Strata.DL.Imperative.Stmt` states five preconditions of the
structured-to-unstructured lowering, and three of them are facts above:
`noLoopInvariants`, `noLoopMeasures` and `noNondetGuards`. The remaining
two — `Block.loopBodyNoInits` and `Block.uniqueInits` — are deliberately *not*
facts: no phase here establishes or requires them, so a fact for each would
be a claim nobody makes and nobody reads. They belong with the change that
gives `StructuredToUnstructured` a `PipelinePhase`, which is what will
require them. Wiring
them to that phase also needs a bridge from each fact to the Imperative
predicate its soundness theorem is stated over. -/

/-- Short, human-readable name for each fact. Used in diagnostic
    messages produced by the pipeline-composition check and by
    `canon_fact_set`. -/
def ProgramFact.name : ProgramFact → String
  | .noCFGBodies => "noCFGBodies"
  | .noCalls => "noCalls"
  | .noLoops => "noLoops"
  | .noLoopInvariants => "noLoopInvariants"
  | .noLoopMeasures => "noLoopMeasures"
  | .staticSingleAssignment => "staticSingleAssignment"
  | .noBetaRedexes => "noBetaRedexes"
  | .noPrecondsFromFuncs => "noPrecondsFromFuncs"
  | .noNondetGuards => "noNondetGuards"
  | .noInternalFuncDecl => "noInternalFuncDecl"
  | .noPolymorphicProcedures => "noPolymorphicProcedures"
  | .noPolymorphicFunctions => "noPolymorphicFunctions"

/-- All known facts, in the order that defines canonical form. Verified
    complete by `ProgramFact.all_complete` and duplicate-free by
    `ProgramFact.all_nodup`.

    Marked `@[expose]` so that `FactsCanonical` — and hence every fact
    set's proof obligation — reduces in importing modules, which is what
    lets `canon_facts` discharge it statically. -/
@[expose] def ProgramFact.all : List ProgramFact :=
  [.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants, .noLoopMeasures,
   .staticSingleAssignment, .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
   .noInternalFuncDecl, .noPolymorphicProcedures, .noPolymorphicFunctions]

/-- `ProgramFact` is a fact vocabulary: a closed enumeration with names, which
    is all the language-neutral pipeline machinery needs of it. Completeness and
    duplicate-freeness are `by decide` over the twelve constructors. -/
instance : Strata.Pipeline.FactVocabulary ProgramFact where
  decEq := inferInstance
  all := ProgramFact.all
  all_complete := by intro f; cases f <;> decide
  all_nodup := by decide
  name := ProgramFact.name

---------------------------------------------------------------------

/-! ## Meaning of a fact

A fact is a `Prop` on programs, because what a phase's contract will
eventually have to *prove* is that Prop. A fact *may* also have an executable
check, `check?`, which is what an asserting phase runs and what a test can
evaluate; `holds_iff_check` ties the two together where one exists.

A check is a convenience, not a requirement. A future fact — termination, for
instance — can be a `Prop` no function decides, and a phase can still require
it, establish it or preserve it; only an asserting phase is out of reach,
since there is nothing to run. Where a check does exist, the fact's `Prop` should still be written the way a
proof about it will want to read, with the check proved equal to it, rather
than the `Prop` being bent into the shape of a `Bool`. -/

/-- Executable check for a fact, for the facts that have one. `none` means
    the fact is still perfectly usable in a contract — it just cannot be
    asserted, since there is nothing to run. -/
@[expose] def ProgramFact.check? : ProgramFact → Option (Program → Bool)
  | .noCFGBodies      => some Program.allStructured
  | .noCalls          => some (Program.allStatements Statements.noCalls)
  | .noLoops          => some (Program.allStatements Imperative.Block.noLoops)
  | .noLoopInvariants => some (Program.allStatements Imperative.Block.loopHasNoInvariants)
  | .noLoopMeasures   => some (Program.allStatements Imperative.Block.noMeasureLoops)
  | .staticSingleAssignment =>
    some (Program.allStatements Statements.staticSingleAssignment)
  | .noBetaRedexes    => some (Program.allExprs Lambda.LExpr.noBetaRedex)
  | .noPrecondsFromFuncs => some Program.noFuncPreconditions
  | .noNondetGuards => some (Program.allStatements Imperative.Block.noNondetGuards)
  | .noInternalFuncDecl => some (Program.allStatements Statements.noFuncDecls)
  | .noPolymorphicProcedures => some Program.noPolymorphicProcedures
  | .noPolymorphicFunctions => some Program.noPolymorphicFunctions

/-- What a fact asserts about a program: the `Prop` that a phase claiming
    the fact will have to prove of its output. -/
@[expose] def ProgramFact.holds : ProgramFact → Program → Prop
  | .noCFGBodies      => fun p => Program.allStructured p = true
  | .noCalls          => fun p => Program.allStatements Statements.noCalls p = true
  | .noLoops          => fun p => Program.allStatements Imperative.Block.noLoops p = true
  | .noLoopInvariants =>
    fun p => Program.allStatements Imperative.Block.loopHasNoInvariants p = true
  | .noLoopMeasures   =>
    fun p => Program.allStatements Imperative.Block.noMeasureLoops p = true
  | .staticSingleAssignment =>
    fun p => Program.allStatements Statements.staticSingleAssignment p = true
  | .noBetaRedexes    => fun p => Program.allExprs Lambda.LExpr.noBetaRedex p = true
  | .noPrecondsFromFuncs => fun p => Program.noFuncPreconditions p = true
  | .noNondetGuards =>
    fun p => Program.allStatements Imperative.Block.noNondetGuards p = true
  | .noInternalFuncDecl =>
    fun p => Program.allStatements Statements.noFuncDecls p = true
  | .noPolymorphicProcedures => fun p => Program.noPolymorphicProcedures p = true
  | .noPolymorphicFunctions => fun p => Program.noPolymorphicFunctions p = true

end -- public section

end Core

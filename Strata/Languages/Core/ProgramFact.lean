/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.CallWFProps
public import Strata.DL.Lambda.LExprWF
public import Strata.Pipeline.FactSet
public import Strata.Languages.Core.NameMangling

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
    Closed enum, kept in sync with `ProgramFact.holds` and `ProgramFact.check?`
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
  /-- Every call is well-formed (`Program.callsWellFormed`): it names a declared
      procedure, its arguments match the procedure's signature in number and mode,
      and its result variables are distinct. Established by `assertWellFormedCalls`. -/
  | wellFormedCalls
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
  /-- Initializer names are globally unique within each procedure body. Required
      by loop-initializer hoisting and structured-to-CFG lowering, which move
      declarations across structured scopes. -/
  | uniqueInits
  /-- No loop body contains an initializer at any nesting depth. Established by
      loop-initializer hoisting and required by structured-to-CFG lowering. -/
  | loopBodyNoInits
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
      which rejects a nondeterministic guard outright. -/
  | noNondetGuards
  /-- Every procedure body contains only `assume`, `assert`, `cover` and `init`,
      nested under `ite *` to any depth. Established by symbolic evaluation.
      Required by the back end, whose obligation extraction handles only bodies
      of this shape. Also required by `UnrollBoundedQuantifiers`. -/
  | hasObligationForm
  /-- No procedure carries a `requires` or `ensures` clause, free or checked.
      Established by symbolic evaluation, which assumes a procedure's
      preconditions and asserts its postconditions in the obligations it emits,
      and emits a procedure with an empty contract. Required by the back end:
      obligation extraction reads only procedure bodies, so a surviving
      `ensures` would go unchecked and a surviving `requires` would be dropped
      from the path condition. -/
  | noProcedureContracts
  /-- No procedure carries type parameters. Established by
      `GenOpaqueTypeParams`, which replaces each type parameter of a procedure
      by a fresh opaque type and clears `header.typeArgs`. Required by the back end: SMT has no
      procedure-level polymorphism to encode. -/
  | noPolymorphicProcedures
  /-- No function carries type parameters, wherever it is declared. Established
      by `MonomorphizeFunctions`, which replaces a polymorphic function by
      copies at the instantiations reached from the program. Required by the back
      end, since an SMT function symbol has one signature. -/
  | noPolymorphicFunctions
  /-- Every type annotation the back end reads is present: no operation, free
      variable or quantifier carries a `none` type. Established by `typeCheck`,
      which annotates the program, and required by the back end, whose SMT
      encoder rejects an unannotated operation, free variable or quantifier.

      Unlike every other fact this one exposes no executable check
      (`check?` is `none`), so it has no `assert` form: confirming that
      annotations are *present* would not establish that they are *correct*,
      and a sound check means binding the type-checking algorithm to the
      typing rules, which is future work. `typeCheck` is therefore its only
      source. -/
  | typeAnnotated
  /-- No procedure body contains an `init`: every variable a body reads is free in it.
      Established by symbolic evaluation, whose obligation procedures only assume, assert
      and cover. Required by `CommonSubexprElim`, which names each shared subexpression in an
      `init` it prepends to the body: a subexpression that reads a variable declared by an
      `init` of the body would be evaluated before that declaration, and the SMT encoding
      would declare the variable twice. The obligation program of the SSA phase declares
      its variables in place, so it does not have this fact. -/
  | noInits
  /-- Every procedure body is in tree form: it contains only `init`, `set`, `assume`,
      `assert` and `cover`, nested under `ite *` to any depth, and every `ite *` is the last
      statement of its list. Established by the WP phase, whose output (a guarded program)
      has this shape. Required by the SSA phase, which translates exactly these statements
      and needs no join after an `ite *`. -/
  | treeForm
  /-- Every `exit` in a structured procedure body targets an enclosing `block` of the body
      (`Imperative.Block.exitsCoveredByBlocks []`), so no body can end by exiting.
      Established by `typeCheck`, which rejects an `exit` whose label names no enclosing
      block. Required by the WP phase, which resolves each `exit` at the enclosing block it
      targets, and which checks this of each procedure body again (`Core.WP.checkLoopFree`),
      failing on an `exit` that targets no enclosing block. -/
  | exitsCovered
  /-- Every arm of every `ite` of every procedure body, at any depth, contains an `assert` or a
      `cover` (`Imperative.Block.armsHaveChecks`). Established by the WP phase, whose guarded
      program opens an `ite` only for a run of obligations or for a branch both of whose arms
      carry one. Required by the SSA phase, which drops an arm without obligations and inlines
      the other one: a run through the dropped arm would be replayed by running the other
      arm's definitions, which need not agree with it. -/
  | armsHaveObligations
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
structured-to-unstructured lowering. They are represented by
`noLoopInvariants`, `noLoopMeasures`, `noNondetGuards`, `uniqueInits`, and
`loopBodyNoInits`; the latter two connect the lowering to the loop-init-hoist
phase that establishes the required declaration shape.
The `ProgramFact.*_of_program` lemmas in `ProgramFactProps` turn these facts
into the matching `Block` conditions on each structured procedure body. -/

/-! ### Shapes the correctness proofs of the pipeline's phases cover

Checks on a program that the correctness proofs of the phases assume of their input. -/

namespace Specification.Analysis

open Lambda

/-- Every datatype block of `p` is one datatype without recursive constructor arguments,
    in the shape `LDatatype.argsWF` checks: what the proofs about the functions generated
    for datatypes cover. -/
@[expose] def DatatypesProvable (p : Program) : Bool :=
  p.decls.all fun
    | .type (.data block) _ => block.length == 1 && Lambda.MutualDatatype.NoRecursive block &&
        block.all Lambda.LDatatype.argsWF
    | _ => Bool.true


mutual
/-- Is every character of every string literal in the constant `c`, including the strings
    inside map and sequence literals, in SMT-LIB's string alphabet (see `StrLitsInAlphabet`)? -/
@[expose] def ConstStrsInAlphabet : LConst → Bool
  | .strConst str => str.toList.all (·.toNat ≤ 0x2FFFF)
  | .mapConst _ _ d ⟨es⟩ => ConstStrsInAlphabet d && EntriesStrsInAlphabet es
  | .sequenceConst _ ⟨es⟩ => ElemsStrsInAlphabet es
  | .intConst _ | .rationalConst _ | .bitvecConst _ _ | .boolConst _ => true
/-- `ConstStrsInAlphabet` holds of the key and the value of every entry of a map literal. -/
@[expose] def EntriesStrsInAlphabet : List (LConst × LConst) → Bool
  | [] => true
  | (k, v) :: r => ConstStrsInAlphabet k && ConstStrsInAlphabet v && EntriesStrsInAlphabet r
/-- `ConstStrsInAlphabet` holds of every element of a sequence literal. -/
@[expose] def ElemsStrsInAlphabet : List LConst → Bool
  | [] => true
  | e :: r => ConstStrsInAlphabet e && ElemsStrsInAlphabet r
end

/-- Is every character of every string literal of `e` in SMT-LIB's string alphabet, the
    code points 0 to 0x2FFFF? Lean characters go up to 0x10FFFF. The bound is the SMT
    encoder's `Strata.SMT.StringLit.maxCodePoint`, written out here so that the check
    reduces in proofs: `maxCodePoint` is not exposed outside its module. The strings
    inside map and sequence literals count (`ConstStrsInAlphabet`). -/
@[expose] def StrLitsInAlphabet : Expression.Expr → Bool
  | .const _ c => ConstStrsInAlphabet c
  | .app _ f a => StrLitsInAlphabet f && StrLitsInAlphabet a
  | .abs _ _ _ e => StrLitsInAlphabet e
  | .quant _ _ _ _ tr e => StrLitsInAlphabet tr && StrLitsInAlphabet e
  | .ite _ c t e => StrLitsInAlphabet c && StrLitsInAlphabet t && StrLitsInAlphabet e
  | .eq _ e1 e2 => StrLitsInAlphabet e1 && StrLitsInAlphabet e2
  | .op _ _ _ | .bvar _ _ | .fvar _ _ _ => true

end Specification.Analysis

namespace MonomorphizeFunctions

open Lambda

/-- The type variables of the annotated operators of `e` are among `vs`. -/
@[expose] def opAnnotsWithin (vs : List TyIdentifier) (e : Expression.Expr) : Bool :=
  e.opAnnots.all fun a => a.2.freeVars.all (· ∈ vs)

/-- The type variables in `f`'s expressions are among its type parameters. -/
@[expose] def fnAnnotsWithin (f : LFunc CoreLParams) : Bool :=
  f.toFunc.exprs.all (opAnnotsWithin f.typeArgs)

/-- **Every instantiation the pass can make is ground**, as a Boolean: the operators of `p`'s
    lemmas, axioms and `distinct` declarations are annotated with ground types, and the
    expressions of every function `p` declares, and of every function of the factory `F`,
    mention only that function's type parameters (none for a monomorphic one). The pass reads
    instantiations off these annotations, so each copy it makes is at ground types. -/
@[expose] def groundInstantiationsB (F : Lambda.Factory CoreLParams) (p : Program) : Bool :=
  (p.decls.all fun d =>
    match d with
    | .ax a _ => opAnnotsWithin [] a.e
    | .lemma l _ => opAnnotsWithin [] l.e
    | .distinct _ es _ => es.all (opAnnotsWithin [])
    | .func f _ => fnAnnotsWithin f.toLFunc
    | .recFuncBlock fs _ => fs.all fun f => fnAnnotsWithin f.toLFunc
    | _ => true) &&
  F.toArray.toList.all fnAnnotsWithin

/-- Every type parameter of `f` occurs in its signature. The pass reads a call's instantiation
    off the signature, so a parameter outside it would be left a type variable. -/
@[expose] def sigVarsB (f : LFunc CoreLParams) : Bool :=
  f.typeArgs.all fun ta => decide (ta ∈ (LMonoTy.mkArrow' f.output (f.inputs.map
      Prod.snd)).freeVars)

/-- **Every type parameter of a function occurs in its signature**, for every function `p`
    declares and every function of the factory `F`. -/
@[expose] def sigTypeArgsB (F : Lambda.Factory CoreLParams) (p : Program) : Bool :=
  (p.decls.all fun d =>
    match d with
    | .func f _ => sigVarsB f.toLFunc
    | .recFuncBlock fs _ => fs.all fun f => sigVarsB f.toLFunc
    | _ => true) &&
  F.toArray.toList.all sigVarsB

/-- `c` can name a type constructor in a mangled name: no `#`, not a numeral, not `$bv`. -/
@[expose] def plainNameB (c : String) : Bool :=
  !c.toList.contains '#' && !(!c.toList.isEmpty && c.toList.all Char.isDigit) && c != "$bv"

/-- Every type constructor in an operator annotation of `e` has a plain name. -/
@[expose] def annotsPlainB (e : Expression.Expr) : Bool :=
  e.opAnnots.all fun a => (Core.NameMangling.tconsNames a.2).all plainNameB

/-- Every type constructor in an operator annotation of `f`'s expressions has a plain name. -/
@[expose] def fnAnnotsPlainB (f : LFunc CoreLParams) : Bool :=
  f.toFunc.exprs.all annotsPlainB

/-- **Every type constructor the pass can put into a mangled name has a plain name**: those in
    the operator annotations of `p`'s lemmas, axioms, `distinct` declarations and functions,
    and of the functions of the factory `F`. The pass names a copy after the type constructors
    of its instantiation, which it reads off these annotations. -/
@[expose] def plainAnnotsB (F : Lambda.Factory CoreLParams) (p : Program) : Bool :=
  (p.decls.all fun d =>
    match d with
    | .ax a _ => annotsPlainB a.e
    | .lemma l _ => annotsPlainB l.e
    | .distinct _ es _ => es.all annotsPlainB
    | .func f _ => fnAnnotsPlainB f.toLFunc
    | .recFuncBlock fs _ => fs.all fun f => fnAnnotsPlainB f.toLFunc
    | _ => true) &&
  F.toArray.toList.all fnAnnotsPlainB

end MonomorphizeFunctions

/-- Short, human-readable name for each fact. Used in diagnostic
    messages produced by the pipeline-composition check and by
    `canon_fact_set`. -/
def ProgramFact.name : ProgramFact → String
  | .wellFormedCalls => "wellFormedCalls"
  | .noCFGBodies => "noCFGBodies"
  | .noCalls => "noCalls"
  | .noLoops => "noLoops"
  | .noLoopInvariants => "noLoopInvariants"
  | .noLoopMeasures => "noLoopMeasures"
  | .uniqueInits => "uniqueInits"
  | .loopBodyNoInits => "loopBodyNoInits"
  | .staticSingleAssignment => "staticSingleAssignment"
  | .noBetaRedexes => "noBetaRedexes"
  | .noPrecondsFromFuncs => "noPrecondsFromFuncs"
  | .noNondetGuards => "noNondetGuards"
  | .hasObligationForm => "hasObligationForm"
  | .noProcedureContracts => "noProcedureContracts"
  | .noPolymorphicProcedures => "noPolymorphicProcedures"
  | .noPolymorphicFunctions => "noPolymorphicFunctions"
  | .typeAnnotated => "typeAnnotated"
  | .noInits => "noInits"
  | .treeForm => "treeForm"
  | .exitsCovered => "exitsCovered"
  | .armsHaveObligations => "armsHaveObligations"

/-- All known facts, in the order that defines canonical form. Verified
    complete by `ProgramFact.all_complete` and duplicate-free by
    `ProgramFact.all_nodup`.

    Marked `@[expose]` so that `FactsCanonical` — and hence every fact
    set's proof obligation — reduces in importing modules, which is what
    lets `canon_facts` discharge it statically. -/
@[expose] def ProgramFact.all : List ProgramFact :=
  [.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
   .noLoopMeasures, .uniqueInits, .loopBodyNoInits, .staticSingleAssignment,
   .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
   .noProcedureContracts, .noPolymorphicProcedures, .noPolymorphicFunctions,
   .typeAnnotated, .noInits, .treeForm, .exitsCovered, .armsHaveObligations]

/-- `ProgramFact` is a fact vocabulary: a closed enumeration with names, which
    is all the language-neutral pipeline machinery needs of it. Completeness and
    duplicate-freeness are `by decide` over the constructors. -/
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
  | .wellFormedCalls  => some fun p => (illFormedCalls p).isEmpty
  | .noCFGBodies      => some Program.allStructured
  | .noCalls          => some (Program.allStatements Statements.noCalls)
  | .noLoops          => some (Program.allStatements Imperative.Block.noLoops)
  | .noLoopInvariants => some (Program.allStatements Imperative.Block.loopHasNoInvariants)
  | .noLoopMeasures   =>
    some (Program.allStatements Imperative.Block.noMeasureLoops)
  | .uniqueInits      =>
    some (Program.allStatements fun ss =>
      (Imperative.Block.initVars (C := Command) ss).eraseDups ==
        Imperative.Block.initVars (C := Command) ss)
  | .loopBodyNoInits  =>
    some (Program.allStatements Imperative.Block.loopBodyNoInits)
  | .staticSingleAssignment =>
    some (Program.allStatements Statements.staticSingleAssignment)
  | .noBetaRedexes    => some (Program.allExprs Lambda.LExpr.noBetaRedex)
  | .noPrecondsFromFuncs => some Program.noFuncPreconditions
  | .noNondetGuards => some (Program.allStatements Imperative.Block.noNondetGuards)
  | .hasObligationForm => some (Program.allStatements Statements.hasObligationForm)
  | .noProcedureContracts => some Program.noProcedureContracts
  | .noPolymorphicProcedures => some Program.noPolymorphicProcedures
  | .noPolymorphicFunctions => some Program.noPolymorphicFunctions
  | .typeAnnotated => none
  | .noInits => some (Program.allStatements Statements.noInits)
  | .treeForm => some (Program.allStatements Statements.treeForm)
  | .exitsCovered => some (Program.allStatements (Imperative.Block.checkExitsCoveredByBlocks []))
  | .armsHaveObligations => some (Program.allStatements Imperative.Block.armsHaveChecks)

/-- What a fact asserts about a program: the `Prop` that a phase claiming
    the fact will have to prove of its output. -/
@[expose] def ProgramFact.holds : ProgramFact → Program → Prop
  | .wellFormedCalls  => Program.callsWellFormed
  | .noCFGBodies      => fun p => Program.allStructured p = true
  | .noCalls          => fun p => Program.allStatements Statements.noCalls p = true
  | .noLoops          => fun p => Program.allStatements Imperative.Block.noLoops p = true
  | .noLoopInvariants =>
    fun p => Program.allStatements Imperative.Block.loopHasNoInvariants p = true
  | .noLoopMeasures   =>
    fun p => Program.allStatements Imperative.Block.noMeasureLoops p = true
  | .uniqueInits      =>
    fun p => Program.allStatements (fun ss =>
      (Imperative.Block.initVars (C := Command) ss).eraseDups ==
        Imperative.Block.initVars (C := Command) ss) p = true
  | .loopBodyNoInits  =>
    fun p => Program.allStatements Imperative.Block.loopBodyNoInits p = true
  | .staticSingleAssignment =>
    fun p => Program.allStatements Statements.staticSingleAssignment p = true
  | .noBetaRedexes    => fun p => Program.allExprs Lambda.LExpr.noBetaRedex p = true
  | .noPrecondsFromFuncs => fun p => Program.noFuncPreconditions p = true
  | .noNondetGuards =>
    fun p => Program.allStatements Imperative.Block.noNondetGuards p = true
  | .hasObligationForm =>
    fun p => Program.allStatements Statements.hasObligationForm p = true
  | .noProcedureContracts => fun p => Program.noProcedureContracts p = true
  | .noPolymorphicProcedures => fun p => Program.noPolymorphicProcedures p = true
  | .noPolymorphicFunctions => fun p => Program.noPolymorphicFunctions p = true
  | .typeAnnotated => fun p => Program.allExprs Lambda.LExpr.fullyAnnotated p = true
  | .noInits => fun p => Program.allStatements Statements.noInits p = true
  | .treeForm => fun p => Program.allStatements Statements.treeForm p = true
  | .exitsCovered =>
    fun p => Program.allStatements (Imperative.Block.checkExitsCoveredByBlocks []) p = true
  | .armsHaveObligations =>
    fun p => Program.allStatements Imperative.Block.armsHaveChecks p = true

end -- public section

end Core

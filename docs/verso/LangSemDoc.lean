/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdTrace
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.KleeneStmt
import Strata.DL.Imperative.KleeneStmtSemantics
import Strata.DL.Imperative.CFGSemantics
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprResolveAnnotated
import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Program
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.CommandTypeSpec
import Strata.Languages.Core.DatatypeTypeSpec
import Strata.Languages.Core.FunctionTypeSpec
import Strata.Languages.Core.ProcedureTypeSpec
import Strata.Languages.Core.ProgramTypeSpec
import Strata.DL.Imperative.Logic.LangDef
import Strata.DL.Imperative.Logic.TraceInterp
import Strata.DL.Imperative.Logic.TraceInterpProps
import Strata.Transform.Specification
import Strata.Transform.CoreSpecification
import Strata.Transform.SpecHoareConnection
import Strata.Transform.SpecificationProps
import Strata.Languages.Core.Logic.LangDef

open Lambda
open Imperative
open Core

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.docstring.allowMissing false

#doc (Manual) "The Strata Core Language Semantics" =>
%%%
shortTitle := "Strata Core Semantics"
%%%

# Formal Semantics of Lambda

This section describes the formal semantics of the Strata Core building blocks.
The layers compose: `Lambda` expressions are reduced via small-step reduction
or interpreted via a denotational semantics. Commands use an expression
evaluator over a variable store. Statements thread configurations through
commands, managing control flow.

## Operational Semantics

The operational semantics of the {name LExpr}`LExpr` type are specified using
the small-step inductive relation {name Lambda.Step}`Lambda.Step`.
This relation is parameterized by a `Factory`, which describes built-in
functions via an optional body and/or evaluation function.

{docstring Lambda.Step}

Typically we will want to talk about arbitrarily long sequences of steps, such
as from an initial expression to a value. The
{name Lambda.StepStar}`Lambda.StepStar` relation describes the reflexive,
transitive closure of the {name Lambda.Step}`Lambda.Step` relation.

{docstring Lambda.StepStar}

The predicate {name Lambda.LExpr.isCanonicalValue}`isCanonicalValue` returns
`true` for `LExpr` that is a value: constants, closed abstractions and quantifiers,
etc.

{docstring Lambda.LExpr.isCanonicalValue}

The theorem {name Lambda.canonical_value_not_step}`canonical_value_not_step`
confirms the intended relationship between the two notions: canonical values are
precisely the normal forms of {name Lambda.Step}`Step`, so no reduction rule can
fire on them.

### Soundness of Partial Evaluator of Lambda

Alongside the relational semantics, `Lambda` provides an executable partial
evaluator, {name Lambda.LExpr.eval}`LExpr.eval`. It takes a fuel bound `n` and
reduces an expression as far as that fuel allows, returning the resulting
expression together with an `EvalResult` that classifies the outcome as
`outOfFuel`, a canonical `value`, or a `nonvalue`.

The theorem {name Lambda.eval_StepStar}`eval_StepStar` states the soundness of
evaluator with respect to the operational semantics. For every fuel
bound `n`, the expression `LExpr.eval n F env e` is reachable from `e` by zero
or more {name Lambda.Step}`Step`s (up to metadata — see below).

### Invariance under Metadata

The theorem {name Lambda.eval_eraseMetadata_invariant}`eval_eraseMetadata_invariant`
srates that expressions that agree up to metadata evaluate under
{name Lambda.LExpr.eval}`LExpr.eval` to results that again agree up to
metadata. This guarantees that the concrete metadata a front end chooses to
record can never change the computed value.

## Denotational Semantics

In addition to the operational semantics, Strata provides a denotational
semantics for `Lambda` (`LExpr.denote`) that interprets well-typed expressions
as Lean values. This enables reasoning about program meaning without stepping
through individual reductions.

The denotation maps monomorphic types to Lean types via _sorts_. A
{name Lambda.LSort}`LSort` is a ground monomorphic type — an `LMonoTy` with no
free type variables. The {name Lambda.SortDenote}`SortDenote` function interprets
sorts into Lean types: built-in sorts (bool, int, real, string, bitvec, arrow)
are mapped to their Lean counterparts, and all others are delegated to a
user-provided type constructor interpretation
({name Lambda.TyConstrInterp}`TyConstrInterp`).

The denotational style has three practical advantages over the small-step relation.
First, the substitution algorithm is not in the trusted base.
Second, `LExpr.denote` produces ordinary Lean terms, so proofs can work over
native Lean values instead of `LExpr` syntax, which can be quite verbose to
manipulate (the operational semantics always operates on `LExpr`).
Third, it gives a natural account of the `forall`/`exists` quantifiers: a quantified Lambda
expression is denoted directly by the corresponding Lean quantifier
(currently the rules in operational semantics are confined to computable expressions only).
The small-step semantics, in turn, doesn't require the expression to be type-annotated, and
remains the better tool for describing traditional programming-language concepts -
such as type safety and what counts as a value - which are naturally phrased in terms
of reduction and normal forms.

{docstring Lambda.LSort}

{docstring Lambda.SortDenote}

The denotation function `LExpr.denote` interprets a well-typed annotated
expression into a Lean value of the appropriate type. It is parameterized by
interpretations for type constructors, operators, and free variables. Each
Lambda construct is denoted into the corresponding Lean one; for example, an
if-then-else becomes a Lean if-then-else, a `forall` quantifier becomes a Lean
`forall`, and so on. Since Lambda allows unbounded quantification and equality
over arbitrary types, this denotation can be used only for reasoning, not for
computation. Validity of a Lambda expression means that `LExpr.denote` evaluates
to `true` under all possible interpretations.

### Consistency with Operational Semantics

The theorem `Step.denote_preserved` states that a single evaluation step
preserves the denotation of an expression. `StepStar.denote_preserved` lifts
this to `StepStar`, showing that denotation is preserved across arbitrary
reduction sequences.

## Type System

The syntax document introduces `Lambda`'s polymorphic, Hindley-Milner typing
relation {name Lambda.LExpr.HasType}`HasType`, which assigns type schemes
({name Lambda.LTy}`LTy`) under an `LContext` and a `TContext`. For the semantics,
the relevant relation is its annotated counterpart,
{name Lambda.LExpr.HasTypeA}`HasTypeA`.

In an annotated expression, every operator, free variable, and
abstraction/quantifier binder carries an explicit {name Lambda.LMonoTy}`LMonoTy`,
and `HasTypeA Δ e τ` checks that those annotations are mutually consistent — with
`Δ` the de Bruijn context giving the types of the enclosing bound variables.
Because the annotations already pin down every choice, the relation is
deterministic: a well-annotated expression has a unique - hence principal - type.
Equivalently, `HasTypeA` is the declarative counterpart of the decidable checker
`LExpr.typeCheck`, and the two are proved equivalent.

Type inference is implemented by `LExpr.resolve`, which elaborates a raw
expression — inferring types and filling in the annotations that `HasTypeA`
reads. The implementation is verified against *both* typing relations:

- `resolve_HasType` (in `LExprTypeSpec.lean`) shows that a successful
  type inference (`LExpr.resolve`) implies the input expression has the
  inferenced type under the `HasType` relation.
- `resolve_HasTypeA` (in `LExprResolveAnnotated.lean`) shows that the
  output expression has the inferenced type under `HasTypeA`.

The `HasTypeA` guarantee is the one that feeds the denotational semantics: it is
exactly the hypothesis `LExpr.denote` requires, so every expression that passes
the checker can be given a well-defined denotation.
Also, `Step.type_preserved` proves the type preservation of `Step` with respect
to `HasTypeA`.

# Formal Semantics of Imperative

## Command Semantics

The semantics of commands are specified in terms of how they interact with a
program state.

{docstring Imperative.Env}

Given a state, the {name InitState}`InitState` relation describes how a
variable obtains its initial value, and the
{name UpdateState}`UpdateState` relation describes how a variable's value can
change.

{docstring Imperative.InitState}

{docstring Imperative.UpdateState}

Given these state relations, the semantics of each command is specified in
a standard way.

{docstring Imperative.EvalCmd}

### Event-Producing Command Semantics

The legacy command relation reports one cumulative failure bit. The alternative
{name Imperative.EvalCmdE}`EvalCmdE` relation instead emits a chronological list
of observations. Each assertion, assumption, or cover captures its condition and
the semantic snapshot where the command was encountered.

{docstring Imperative.EventArg}

{docstring Imperative.Event}

{docstring Imperative.Trace}

The event payload type is a parameter of the command-evaluator interface, so a
custom command language may use its own observation type. The base Imperative
commands instantiate it with {name Imperative.Event}`Event P`.

{docstring Imperative.EvalCmdParamE}

For the base commands, the emitted trace is a deterministic function of the
command, factory, and input store.

{docstring Imperative.Cmd.emittedEvents}

{docstring Imperative.EvalCmdE}

The event-producing relation agrees with that deterministic trace, and every
legacy command execution has a corresponding event execution with the same
resulting store.

{docstring Imperative.EvalCmdE.emitted_eq}

{docstring Imperative.EvalCmd.toEvalCmdE}

## Structured Statement Semantics

The semantics of the {name Stmt}`Stmt` type is defined in terms of
*configurations*, represented by the {name Imperative.Config}`Config` type.

{docstring Imperative.Config}

The {name StepStmt}`StepStmt` relation describes how each type of statement
transforms configurations. It is parameterized by a command evaluator (because
statements are parameteric to the list of defined commands) and an
`extendFactory` function (used by `funcDecl` to add new function definitions to
the expression evaluator within a scope).

{docstring Imperative.StepStmt}

The {name StepStmtStar}`Imperative.StepStmtStar` relation describes
the reflexive, transitive closure of the {name StepStmt}`Imperative.StepStmt`
relation.

{docstring Imperative.StepStmtStar}

### Event-Producing Statement Semantics

{name Imperative.StepStmtE}`StepStmtE` labels each statement transition with the
events emitted by its active command. Administrative control-flow transitions
are reused from `StepStmt` with a command evaluator that cannot step; they emit
the empty event list. Sequence and block frames propagate the active inner
step's events unchanged.

{docstring Imperative.noCommandEvalE}

{docstring Imperative.StepStmtE}

The traced reflexive-transitive closure concatenates each step's event list in
execution order.

{docstring ReflTransTrace}

{docstring Imperative.StepStmtStarE}

For base Imperative commands, the active configuration also determines its next
event list. The compatibility theorem normalizes only the legacy target's
cumulative failure flag because event semantics records assertion observations
in the trace instead of updating that bit.

{docstring Imperative.Config.emittedEvents}

{docstring Imperative.Config.withFailure}

{docstring Imperative.StepStmt.toStepStmtE}

## Control-Flow Graph Semantics

The unstructured control-flow graphs introduced in "The Strata Core Language
Syntax" are given a small-step, per-command operational semantics. Execution
state is tracked by a {name Imperative.CFGConfig}`CFGConfig`.

{docstring Imperative.CFGConfig}

The {name Imperative.StepCFG}`StepCFG` relation takes one execution step over a
deterministic CFG.

{docstring Imperative.StepCFG}

{docstring Imperative.StepCFGStar}

## Well-Formedness of the `PureExpr` Evaluator

As described in "The Strata Core Language Syntax", instantiating `Imperative` needs
to provide the expression language `PureExpr`.
On top of it, the well-formedness conditions of the evaluator
`PureExpr.eval` must be provided (bundled as
{name Imperative.WellFormedSemanticEval}`WellFormedSemanticEval`) against its
factory of choice. See
`Strata/Languages/Core/InstWellFormedSemanticsEval.lean` for Strata Core's
discharge of these predicates.

{docstring Imperative.WellFormedSemanticEvalBool}

{docstring Imperative.WellFormedSemanticEvalVal}

{docstring Imperative.WellFormedSemanticEvalVar}

{docstring Imperative.WellFormedSemanticEvalExprCongr}

{docstring Imperative.WellFormedSemanticEvalInt}

{docstring Imperative.WellFormedSemanticEvalMono}

{docstring Imperative.WellFormedSemanticEvalRename}

{docstring Imperative.WellFormedSemanticEval}


# Formal Semantics of Core

Strata Core's expressions are `Lambda` expressions and its statements are
`Imperative` statements, so a Core program is evaluated by the `Lambda` and
`Imperative` semantics above, instantiated at Core's expression and command types.

## Type System

Core's well-typedness is specified declaratively, with one judgment per
syntactic category. Every judgment is parameterized by the `ExprTypingSpec`
typeclass, so each instantiates to both the polymorphic `HasType` and the
annotated `HasTypeA` expression relations of the Lambda type system above. The
judgments layer up from commands to the whole program.

### Commands

Core's commands are the imperative commands plus a procedure `call`, typed by
{name Core.TypeSpec.CmdExtHasType'}`CmdExtHasType'`.

{docstring Core.TypeSpec.CmdExtHasType'}

### Datatypes

A mutual datatype block must satisfy {name Core.TypeSpec.MutualADTWF}`MutualADTWF`.

{docstring Core.TypeSpec.MutualADTWF}

### Functions

Function declarations (recursive or not) are governed by
{name Core.TypeSpec.FuncHasType'}`FuncHasType'`.

{docstring Core.TypeSpec.FuncHasType'}

### Procedures

Procedure declarations are governed by {name Core.TypeSpec.ProcHasType'}`ProcHasType'`;
its `bodyTyped` field defers to {name Core.TypeSpec.ProcBodyHasType'}`ProcBodyHasType'`,
which accepts only structured bodies (CFG bodies carry no typing obligation).

{docstring Core.TypeSpec.ProcHasType'}

### Programs

Program typing is layered: a single declaration
({name Core.TypeSpec.DeclHasType'}`DeclHasType'`), the declaration list
({name Core.TypeSpec.DeclsHasType'}`DeclsHasType'`, which threads the context so
each declaration is checked against those before it), and the whole program
({name Core.TypeSpec.ProgramHasType'}`ProgramHasType'`).

{docstring Core.TypeSpec.DeclHasType'}

{docstring Core.TypeSpec.DeclsHasType'}

{docstring Core.TypeSpec.ProgramHasType'}

## Procedure Calls

Core extends the `Imperative` commands with a procedure `call`. A call is
executed by descending into the callee's body
({name EvalCommand.call_sem}`EvalCommand.call_sem`).

1. Evaluate the input and inout argument expressions, and read the current values
   of caller-side `out` actuals.
2. Initialize a fresh callee frame: bind input and inout formals to the evaluated
   argument values, copy the `out` values into output-only formals, and snapshot
   each inout formal as `old g`.
3. Assert each non-free precondition unchanged in the initialized callee frame.
4. Run the callee body in that frame. The `old g` snapshots continue to hold the
   values that the inout formals had immediately before the call.
5. Assert each non-free postcondition unchanged in the final callee frame.
6. Update the caller's state with the final values of the callee output formals.

Concrete execution of the body of procedure is necessary to make the procedure
inlining transform exactly semantics-preserving.
A contract version of call semantics is also defined at
{name EvalCommandContract.call_sem}`EvalCommandContract.call_sem`. It does not
execute the body: after checking preconditions, it havocs all initialized callee
output formals, including inouts, and assumes the postconditions. In this semantics, procedure
inlining becomes an underapproximating transform because it replaces the values
of havoc'ed output variables with concrete values.

## Procedures

A procedure body is verified against its contract by assuming the preconditions
on entry and asserting the postconditions on exit. This is a partial
correctness reading: a procedure is correct when, *if* its body terminates, the
postconditions hold. Termination is not part of the obligation and is not checked
for procedures.

## Programs and Declaration Order

A Core program is a list of declarations, and the order is
significant. When the i-th declaration
is elaborated it can refer only to the declarations that precede it (the 1st
through (i−1)-th). A declaration therefore cannot mention a name introduced later
in the program, unless the referred declaration is in the same `rec` block.


# Formally Reasoning about Imperative and Strata Core

## The Language Bundle (`Strata.Logic.Lang P`)

Strata provides formal definitions for reasoning about Imperative and Strata
Core. The framework is built on a small, language-agnostic abstraction
{name Strata.Logic.Lang}`Strata.Logic.Lang P` bundle
(`P` is a parameter for the pure-expression type `PureExpr`).
It packages exactly what a program logic or a transform specification needs from a
language:

{docstring Strata.Logic.Lang}

The `Lang` structure itself belongs to no dialect, and the definitions in this
chapter quantify over an arbitrary `Lang P`. For the Imperative dialect there are
three instances, in the `Imperative.Logic` namespace:
{name Imperative.Logic.Lang.imperative}`Lang.imperative` (structured
statements), {name Imperative.Logic.Lang.imperativeBlock}`Lang.imperativeBlock`
(block bodies), and {name Imperative.Logic.Lang.cfg}`Lang.cfg` (unstructured
control-flow graphs).

### The Event Language Bundle

Event-trace reasoning uses {name Strata.Logic.EventLang}`EventLang P EventT`.
It replaces unlabeled reachability and syntactic assertion-head detection with a
trace-producing closure whose event alphabet is explicit in the type.

{docstring Strata.Logic.EventLang}

The structured Imperative constructors package `StepStmtE` for individual
statements and statement lists; `EventLang.traceStar` derives its traced closure.
Their command evaluator determines `EventT`.

{docstring Strata.Logic.EventLang.TerminatesAt}

{docstring Strata.Logic.EventLang.Terminates}

{docstring Imperative.Logic.EventLang.imperativeE}

{docstring Imperative.Logic.EventLang.imperativeBlockE}

Strata Core instantiates `Lang.imperative` as well as `Lang.imperativeBlock`, and
defines {name Core.Logic.Lang.core}`Lang.core` /
{name Core.Logic.Lang.coreBlock}`Lang.coreBlock`. The Core's language bundle uses
its own initial-environment well-formedness predicate
{name Core.Logic.InitEnvWF}`InitEnvWF` and
{name Core.Logic.BlockInitEnvWF}`BlockInitEnvWF`.
Core's logic and analysis judgements are mostly all over `Lang.coreBlock` because
it is more convenient than `Lang.core` which is about a single statement
(but still can have nested sub-statements).

## Interpreting Event Traces

Operational semantics records snapshots but does not itself decide whether the
captured conditions hold. A {name Imperative.ConditionInterp}`ConditionInterp`
provides a semantic world shared by the conditions in a trace and a predicate
for interpreting each captured `EventArg` in that world.

{docstring Imperative.ConditionInterp}

The initial implementation delegates condition interpretation to the partial
`PureExpr.eval` evaluator. A denotational interpretation can replace it without
changing the operational transition relation or trace representation.

{docstring Imperative.EvaluatorBasedInterp}

{docstring Imperative.Event.neutral}

Only assumption events constrain the worlds considered later in a trace.

{docstring Imperative.Trace.AssumptionsHold}

A trace is reachable when one shared world satisfies all of its assumptions.

{docstring Imperative.Trace.Reachable}

Assertion validity is a partial-correctness property. Each assertion occurrence
must hold in every world satisfying the assumptions that precede that occurrence;
later assumptions cannot discharge an earlier assertion. The per-identifier
version restricts this check to matching assertion occurrences.

{docstring Imperative.Trace.AssertionsValidFromP}

{docstring Imperative.Trace.AssertionsValidFrom}

{docstring Imperative.Trace.AssertionsValid}

{docstring Imperative.Trace.AssertionValidFrom}

{docstring Imperative.Trace.AssertionValid}

Assertion satisfiability existentially selects one matching occurrence and one
world satisfying both its captured condition and all assumptions preceding that
occurrence.

{docstring Imperative.Trace.AssertionSatisfiableFrom}

{docstring Imperative.Trace.AssertionSatisfiable}

Cover satisfiability is existential rather than universal. For one `CoverId`, a
single trace satisfies the property only if it contains a matching cover
occurrence whose condition is satisfiable with the assumptions preceding that
occurrence. A language-level analysis can account for nondeterministic execution
by existentially selecting a reachable trace and then applying this predicate.

{docstring Imperative.Trace.CoverSatisfiableFrom}

{docstring Imperative.Trace.CoverSatisfiable}

The metatheory includes monotonicity results for changing accumulated
assumptions.

{docstring Imperative.Trace.AssertionValidFrom.mono_assumptions}

{docstring Imperative.Trace.CoverSatisfiableFrom.mono_assumptions}

## Hoare Logic

A partial-correctness Hoare triple `Strata.Logic.Hoare.Triple`
([`Logic/HoareTemplate.lean`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Imperative/Logic/HoareTemplate.lean)),
states that any run of `s` from an initial environment satisfying `Pre` that
reaches a terminal or exiting (like `break` in C/Java) configuration emits an
assertion-valid trace under `EvaluatorBasedInterp`.  If that trace is
`Trace.Reachable`, the final environment also satisfies `Post`.

For Imperative's structured statements, since Imperative doesn't fix command type
and wellformedness of the statement, the structural rules (`consequence`, `seq_append`,
`block`, `ite`, `while_rule`, ...) in `Imperative.Logic.Hoare` carry its
well-formedness side conditions as additional assumptions.

The Hoare rules of Strata Core ([`Core/Logic/Hoare.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Core/Logic/Hoare.lean))
instantiates the Imperative template over its block language `EventLang.coreBlock`
with its own wellformedness conditions `Core.Logic.BlockInitEnvWF` and discharges
the side conditions. Also, a Core procedure can be translated into a Hoare triple.
[`Core/Logic/ContractToHoareTriple.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Core/Logic/ContractToHoareTriple.lean),
`Procedure.contractTriple` reads a `spec { requires ...; ensures ...; }` as a triple
over the body — the `requires` clauses (including `free` ones, which the caller
guarantees) as precondition, and the checked, non-`free` `ensures` clauses as
postcondition (`free` postconditions are assumed at call sites, not proved by the
body) — so that "this procedure meets its contract" is a single Hoare judgement.
`StrataTest/Languages/Core/Tests/Logic/Hoare.lean` has examples of Hoare triples
derived from procedure contracts and their proofs.

## Satisfiability and Validity of Assertions

To reason about assertion commands, Strata has two different notions of
properties: validity and satisfiability.
An assertion is valid ({name Imperative.Specification.AssertValid}`AssertValid`, or
{name Imperative.Specification.AssertValidWhen}`AssertValidWhen` relative to a
precondition) when it holds in every reachable configuration where it is about to
execute. {name Imperative.Specification.AllAssertsValid}`AllAssertsValid` lifts
this to all assertions of a statement. Dually, an assertion is satisfiable
({name Imperative.Specification.AssertSatisfiable}`AssertSatisfiable`) when some
reachable run makes it hold.

The event-trace formulation quantifies directly over traces produced by an
`EventLang`. Assertion validity remains universal over all reachable finite
traces. Assertion satisfiability existentially selects a reachable trace and a
matching occurrence satisfiable under its preceding assumptions; cover
satisfiability follows the same existential trace pattern.

{docstring Imperative.Specification.AssertValidOnTracesWhen}

{docstring Imperative.Specification.AllAssertsValidOnTracesWhen}

{docstring Imperative.Specification.AssertSatisfiableOnTracesWhen}

{docstring Imperative.Specification.AssertSatisfiableOnTraces}

The event Hoare triple validates every completed trace and gates its
postcondition on joint satisfiability of that trace's assumptions.  Trace
validity above quantifies over every finite prefix, so the two notions are
separate unless an additional progress or trace-extension result relates them.

### Soundness and Completeness of Analysis

To formally describe analyses that answer validity and satisfiability,
an abstract notion of analysis is defined over an arbitrary `Lang`:

{docstring Imperative.Specification.Analysis}

{docstring Imperative.Specification.Analysis.Sound}

{docstring Imperative.Specification.Analysis.Complete}

The connection of the definition of analysis to Core's verifier is packaged as {name Core.Specification.Analysis.CoreVerifierModel}`CoreVerifierModel`:

{docstring Core.Specification.Analysis.CoreVerifierModel}

Its desirable property is selected by the `VerificationMode` — deductive mode
requires every entry procedure's assertions to be valid, and bug-finding mode
requires them to be satisfiable.

Fully proving the soundness of Core's verifier is an ongoing work.

## Correctness of Program Transformation

Transformations must not change what the verifier concludes. The definitions in
`Strata/Transform/Specification.lean` can relate different source and target
languages.

The analysis-specific {name Imperative.Specification.Transform.Sound}`Sound`
predicate relates two `EventLang` values under one condition interpretation. It
states that validity of each target assertion on reachable traces implies the
corresponding source validity, so a verified output certifies the input.

The operational definitions are more general across analyses and support
horizontal and vertical composition. They are the primary specifications for
program transformations.

- The `Overapproximates` family states this operationally. Plain
  {name Imperative.Specification.Transform.Overapproximates}`Overapproximates` requires that every terminal or exiting state reachable in
  the source is reachable in the target, and that any source assertion failure is
  reproduced in the target. The variants generalize it: {name Imperative.Specification.Transform.OverapproximatesWhen}`OverapproximatesWhen` adds
  a precondition; `OverapproximatesUpto(When)` relates source and target states
  up to input/output relations (needed when a transform renames or generates
  variables); and the `...Aggressively...` variants permit the target to fail
  spuriously (needed when a transform prunes paths).
- {name Imperative.Specification.Transform.Underapproximates}`Underapproximates` is the dual — every terminal/exiting state reachable in the
  target is reachable in the source, and target failures are reflected back —
  which is what bug-finding soundness needs.
- {name Imperative.Specification.Transform.SemanticallyEquivalent}`SemanticallyEquivalent` is their conjunction: source and target reach exactly
  the same terminal/exiting states and fail on exactly the same initial states.

For `EventLang`, the `OverapproximatesTraces` family additionally relates the
chronological event lists produced by source and target executions. The most
general member carries separate input/output environment relations and simulates
all finite prefixes as well as terminal and exiting runs.

{docstring Imperative.Specification.Transform.OverapproximatesTracesUptoWhen}

{docstring Imperative.Specification.Transform.OverapproximatesTracesWhen}

{docstring Imperative.Specification.Transform.OverapproximatesTraces}

Trace overapproximation connects back to the event logic through
{name Imperative.Specification.Transform.overapproximatesTraces_triple}`overapproximatesTraces_triple`
(in `SpecHoareConnection.lean`): with equality as the trace relation, if a Hoare
triple holds on the target `T(st)`, the same triple holds on the source `st`.
The terminal or exiting simulation supplies the identical event trace and final
environment required by the target triple.

Strata proves that sequentially chaining multiple transformations is correct through
(vertical composition),
{name Imperative.Specification.Transform.overapproximates_comp}`overapproximates_comp`
which turns overapproximations `L₁ → L₂` and `L₂ → L₃` into one `L₁ → L₃`.
{name Imperative.Specification.Transform.overapproximatesUpto_comp}`overapproximatesUpto_comp`
does the same for the up-to-relation form, composing the two state relations with
relation composition (`RComp`); and
{name Imperative.Specification.Transform.overapproximatesAggressively_comp}`overapproximatesAggressively_comp`
composes the assertion-failure-relaxed variant.

Trace overapproximations compose their trace relations explicitly. The general
composition theorem produces relational composition, while the shared-start
up-to theorem accepts stage-specific trace relations and a transitive output
state relation.

{docstring Imperative.Specification.Transform.OverapproximatesTraces.rel_comp}

{docstring Imperative.Specification.Transform.OverapproximatesTracesUptoWhen.comp_trans_eq}

Composition across a statement list (horizontal composition):
{name Imperative.Specification.Transform.overapproximates_stmts}`overapproximates_stmts`
and {name Imperative.Specification.Transform.overapproximatesUpto_stmts}`overapproximatesUpto_stmts`
lift a per-statement overapproximation to the whole block (`fun ss => ss.mapM T`).
Like the Hoare rules above, these carry well-formedness side conditions: the
lift needs an environment invariant that holds at block entry, is preserved as
each statement runs, and implies the per-statement source well-formedness. When no
such statement-independent invariant exists, the block-level result has to be
proved directly instead.

The trace-aware counterpart, {name Imperative.Specification.Transform.overapproximatesTraces_stmts}`overapproximatesTraces_stmts`, additionally requires the trace relation to relate empty traces and respect chronological append. It simulates arbitrary finite prefixes as well as terminal and exiting runs.

{docstring Imperative.Specification.Transform.overapproximatesTraces_stmts}

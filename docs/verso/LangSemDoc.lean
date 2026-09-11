/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
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

# Formal Semanatics of Imperative

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

1. Evaluate the argument expressions `e₁, ..., eₙ`.
2. Assert each (non-free) precondition, substituting actuals for formals.
3. Havoc the output variables `y₁, ..., yₘ`.
4. Run the body of the callee procedure, with the actuals substituted for
   formals and binding `old v` to the value of `v` immediately before the call.
5. Assert each (non-free) postcondition, substituting actuals for formals.
6. Update the caller's state with the new values of the output variables.

Concrete execution of the body of procedure is necessary to make the procedure
inlining transform exactly semantics-preserving.
A contract version of call semantics is also defined at
{name EvalCommandContract.call_sem}`EvalCommandContract.call_sem`.
In this semantics, procedure inlining becomes an underapproximating transform
because it replaces the values of havoc'ed output variables with concrete
values.

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

Strata Core instantiates `Lang.imperative` as well as `Lang.imperativeBlock`, and
defines {name Core.Logic.Lang.core}`Lang.core` /
{name Core.Logic.Lang.coreBlock}`Lang.coreBlock`. The Core's language bundle uses
its own initial-environment well-formedness predicate
{name Core.Logic.InitEnvWF}`InitEnvWF` and
{name Core.Logic.BlockInitEnvWF}`BlockInitEnvWF`.
Core's logic and analysis judgements are mostly all over `Lang.coreBlock` because
it is more convenient than `Lang.core` which is about a single statement
(but still can have nested sub-statements).

## Hoare Logic

A partial-correctness Hoare triple `Strata.Logic.Hoare.Triple`
([`Logic/HoareTemplate.lean`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Imperative/Logic/HoareTemplate.lean)),
states that any run of `s` from an initial environment satisfying `Pre` that
reaches a terminal or exiting (like `break` in C/Java) configuration ends in a
state satisfying `Post` with no failed assertion.

For Imperative's structured statements, since Imperative doesn't fix command type
and wellformedness of the statement, the structural rules (`consequence`, `seq_append`,
`block`, `ite`, `while_rule`, ...) in `Imperative.Logic.Hoare` carry its
well-formedness side conditions as additional assumptions.

The Hoare rules of Strata Core ([`Core/Logic/Hoare.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Core/Logic/Hoare.lean))
instantiates the Imperative template over its block language `Lang.coreBlock`
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

The validity notion coincides with the Hoare triple. The two are bridged in
[`SpecHoareConnection.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/SpecHoareConnection.lean)
by `hoareTriple_implies_assertValid` and `allAssertsValid_implies_hoareTriple`.

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

Transformations must not change what the verifier concludes.
In `Strata/Transform/Specification.lean`, a desirable property of a
program transformation is defined on two different languages (`Lang`):
the source `L₁` and target `L₂`.

There are two different classes of definition of transform correctness.
The first one is an analysis-specific. {name Imperative.Specification.Transform.Sound}`Sound` states that a transformation `T` is sound
when validity of the target's assertions implies validity of the source's, so a verified output certifies the
input.

The second type of definitions is more general, possibly can be used across different analyses,
and horizontally/vertically compositional (`Sound` is not horizontally composable).
This is more heavily used as specifications for program transformations.

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

Overapproximation is the workhorse that connects back to the logic. The bridge is
{name Imperative.Specification.Transform.overapproximates_triple}`overapproximates_triple`
(in `SpecHoareConnection.lean`): if `T` overapproximates and a Hoare triple holds
on the target `T(st)`, then the same triple holds on the source `st` — the triple
is transported backwards across the transform. Since a triple is equivalent to
assertion validity, an over-approximating transform preserves validity, and hence
is `Sound`.

Strata proves that sequentially chaining multiple transformations is correct through
(vertical composition),
{name Imperative.Specification.Transform.overapproximates_comp}`overapproximates_comp`
which turns overapproximations `L₁ → L₂` and `L₂ → L₃` into one `L₁ → L₃`.
{name Imperative.Specification.Transform.overapproximatesUpto_comp}`overapproximatesUpto_comp`
does the same for the up-to-relation form, composing the two state relations with
relation composition (`RComp`); and
{name Imperative.Specification.Transform.overapproximatesAggressively_comp}`overapproximatesAggressively_comp`
composes the assertion-failure-relaxed variant.

Composition across a statement list (horizontal composition):
{name Imperative.Specification.Transform.overapproximates_stmts}`overapproximates_stmts`
and {name Imperative.Specification.Transform.overapproximatesUpto_stmts}`overapproximatesUpto_stmts`
lift a per-statement overapproximation to the whole block (`fun ss => ss.mapM T`).
Like the Hoare rules above, these carry well-formedness side conditions: the
lift needs an environment invariant that holds at block entry, is preserved as
each statement runs, and implies the per-statement source well-formedness. When no
such statement-independent invariant exists, the block-level result has to be
proved directly instead.

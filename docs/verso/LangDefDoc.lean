/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.DL.Imperative.NondetStmt
import Strata.DL.Imperative.NondetStmtSemantics
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.LExprTypeSpec

open Lambda
open Imperative

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.docstring.allowMissing false

#doc (Manual) "The Strata Core Language Definition" =>
%%%
shortTitle := "The Strata Core Language"
%%%

# Introduction

Strata aims to provide a foundation for representing the semantics of programs,
specifications, protocols, architectures, and other aspects of large-scale
distributed systems and their components. It achieves this through languages of
two types. The first type, consisting of the single Strata Core language,
provides a central hub that can serve as a connection point between multiple
types of input artifact and multiple types of analysis, reducing the cost of
implementing N analyses for M languages from N\*M to N+M.

The second type consists of numerous Strata _dialects_.  The Dialect Definition
Mechanism, described
[here](https://github.com/strata-org/Strata/tree/main/docs/verso/DDMDoc.lean),
provides a way to define the syntax and a simple type system for a dialect.  At
the moment, dialects do not directly have semantics (though we may add a
mechanism for defining their semantics in the future) but instead are defined by
translation to or from Strata Core. Said another way, each of these dialects is
a different concrete way to write Strata programs, but all of these dialects are
ultimately represented internally using the same Core language.

Dialects are used to describe both the initial artifacts being analyzed by
Strata and more low-level representations of those artifacts used to communicate
with external reasoning tools such as model checkers or SMT solvers. In both
situations, Strata uses dialects as a mechanism for communicating with external
tools (either language front ends or generic automated reasoning tools like SMT
solvers).

The following "hourglass" diagram illustrates how various existing (blue) or
potential (gray) input dialects could be translated into Strata Core and then
into the input language for various back end tools. Solid lines indicate
translation paths that exist (though experimentally in the connection between
Strata Core and CBMC), and dotted lines indicate translations that illustrate
the sorts of use cases we expect Strata to support but that haven't yet been
implemented.

![Strata hourglass diagram](strata-hourglass.png)

The Strata Core language is constructed using a few building blocks that can be
combined in different ways. This allows concrete dialects to systematically use
different combinations that still share the majority of their implementation. In
Lean (and in principle in most other source languages that could be used to
process Strata programs), the type system can enforce various structural
constraints, ensuring that only expected language constructs show up. The Strata
Core language itself consists of an imperative statement type parameterized by
an expression type, with various more fine-grained adjustments of other
parameters.

The two fundamental building blocks of Strata Core are a representation of
functional programs (`Lambda`), and a representation of imperative programs
(`Imperative`). The `Lambda` language is parameterized by a type system and a
set of built-in types and functions. The `Imperative` language is then
parameterized by the type of expressions it allows in conditions, assignments,
and so on. Currently, those expressions will almost always be some
instantiation of `Lambda`. Both Core building blocks are parameterized by a
metadata type, which by default is instantiated with a map from keys to
structured values that can contain expressions (typically from `Lambda`).

The remainder of this document describes the current abstract syntax and
semantics of `Lambda` and `Imperative` in detail, with direct reference to the
Lean source code that defines these languages. We do not consider the Core
language set in stone. It may evolve over time, particularly to add new
fundamental constructs, and this document will be updated as it does. We intend
for Strata Core to be close to a superset of [B3](https://b3-lang.org/), but it
may at times make different choices to support its goal of being useful for a
wide range of analyses, rather than being optimized for deductive verification.
In particular, Strata aims to make it possible to encode most input artifacts
without the need for axioms.

# Lambda

The `Lambda` language is a standard but generic implementation of the lambda
calculus. It is parameterized by a type for metadata and the type of types
(which may be `Unit`, to describe the untyped lambda calculus). It includes the
standard constructs for constants, free and bound variables, abstractions, and
applications. In addition, it includes a special type of constant, an operator,
to represent built-in functions. It extends the standard lambda calculus by
allowing quantifiers (since a key use of the language is to write logical
predicates) and includes a constructor for if-then-else to allow it to have lazy
semantics.

Although `Lambda` can be parameterized by an arbitrary type system, the Strata
code base includes a
[formalization](https://github.com/strata-org/Strata/blob/main/Strata/DL/Lambda/LExprTypeSpec.lean)
of a polymorphic Hindley-Milner type system and an
[implementation](https://github.com/strata-org/Strata/blob/main/Strata/DL/Lambda/LTyUnify.lean)
of an inference algorithm over the type `LTy` (described below). This allows
universal quantification over types and the use of arbitrary named type
constructors (as well as special support for bit vector types, to allow them to
be parameterized by size).

## Syntax

The syntax of lambda expressions is provided by the {name LExpr}`LExpr` type.

{docstring Lambda.LExpr}

Identifiers in lambda expressions, using the {name Identifier}`Identifier` type,
can be annotated with metadata.

{docstring Lambda.Identifier}

Specific constructors exist for constants of various scalar types, including
booleans, bit vectors, integers, reals, and strings.

{docstring Lambda.LConst}

The {name LExpr}`LExpr` type can be parameterized by the type used to represent
normal metadata and the type used to represent identifier metadata, as well as
the type of types.

{docstring Lambda.LExprParams}

{docstring Lambda.LExprParamsT}

## Type System

Although {name LExpr}`LExpr` can be parameterized by an arbitrary type system,
Strata currently implements one, based on the types {name LMonoTy}`LMonoTy` and
{name LTy}`LTy`.

The first, {name LMonoTy}`LMonoTy`, represents monomorphic types. It's a
separate type because some contexts allow only monomorphic types.

{docstring Lambda.LMonoTy}

Type variables in {name LMonoTy}`LMonoTy` use the {name TyIdentifier}`TyIdentifier` type.

{docstring Lambda.TyIdentifier}

The {name LTy}`LTy` type allows monomorphic types to be wrapped in universal type
quantifiers that bind these type variables, creating polymorphic types.

{docstring Lambda.LTy}

An expression {name LExpr}`LExpr` parameterized by {name LTy}`LTy` is
well-typed according to the {name LExpr.HasType}`HasType` relation.
This relation depends on two types of context.

The first of these, {name LContext}`LContext`, contains information that does
not change throughout the type checking process. This includes information about
built-in functions, using the {name Factory}`Factory` type, and built-in types,
using the {name TypeFactory}`TypeFactory` type. Built-in functions optionally
include concrete evaluation functions, which can be used in the operational
semantics described below.

{docstring Lambda.LContext}

The second context includes two pieces of data that change throughout the type
checking process: a map from free variables in expressions to types, and a list
of type aliases including the name and definition of each alias.

{docstring Lambda.TContext}

Given these two pieces of context, the {name LExpr.HasType}`HasType` relation
describes the valid type of each expression form.

{docstring Lambda.LExpr.HasType}

## Operational Semantics

The semantics of the {name LExpr}`LExpr` type are specified in a standard way
using the small-step inductive relation {name Lambda.Step}`Lambda.Step`.
This relation is parameterized by a `Factory`, which describes built-in
functions via an optional body and/or evaluation function.

{docstring Lambda.Step}

Typically we will want to talk about arbitrarily long sequences of steps, such
as from an initial expression to a value. The
{name Lambda.StepStar}`Lambda.StepStar` relation describes the reflexive,
transitive closure of the {name Lambda.Step}`Lambda.Step` relation.

{docstring Lambda.StepStar}

# Imperative

The `Imperative` language is a standard core imperative calculus, parameterized
by a type of expressions and divided into two pieces: commands and statements.
Commands represent atomic operations that do not induce control flow (except
possibly in the form of procedure calls that follow a stack discipline, though
the current core set of commands does not include calls). Statements are
parameterized by a command type and describe the control flow surrounding those
commands. Currently, `Imperative` has structured, deterministic statements, each
of which can be: a command, a sequence of statements in a block, a deterministic
conditional, a deterministic loop with a condition, or a forward `goto`
statement. (Note: we plan to replace `goto` with a block exit statement, and
have a separate unstructured CFG representation.)

We plan to add non-deterministic statements, as in [Kleene Algebra with
Tests](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf), and support a
translation from structured deterministic statements into structured
non-deterministic statements.

We also expect to add unstructured control-flow graphs where each basic block
consists of a sequence of commands followed by a terminator command. A
terminator command can be: a conditional jump to one of two blocks, termination
of execution, or a non-deterministic jump to any one of an arbitrary number of
successor blocks.

## Command Syntax

The core built-in set of commands includes variable initializations,
deterministic assignments, non-deterministic assignments ("havoc"), assertions,
and assumptions.

{docstring Imperative.Cmd}

## Command Operational Semantics

The semantics of commands are specified in terms of how they interact with a
program state, written `σ`. A state can be applied to a variable to obtain its
current value. And an expression `e` can be evaluated using the evaluation
function in a given state: `δ σ e` gives the result of evaluating `e` in state
`σ`. This generic description allows the details of the program state
representation to vary, as long as it supports these operations.

Given a state `σ`, the {name InitState}`InitState` relation describes how a
variable obtains its initial value.

{docstring Imperative.InitState}

The {name UpdateState}`UpdateState` relation then describes how a variable's
value can change.

{docstring Imperative.UpdateState}

Given these two state relations, the semantics of each command is specified in
a standard way.

{docstring Imperative.EvalCmd}

## Structured Deterministic Statement Syntax

Statements allow commands to be organized into standard control flow
arrangements, including sequencing, alternation, and iteration. Sequencing
statements occurs by grouping them into blocks. Loops can be annotated with
optional invariants and decreasing measures, which can be used for deductive
verification.

{docstring Imperative.Stmt}

{docstring Imperative.Block}

## Structured Deterministic Statement Operational Semantics

The semantics of the {name Stmt}`Stmt` type is defined in terms of
*configurations*, represented by the {name Imperative.Config}`Config` type. A
configuration pairs the statement(s) remaining to be executed with a state, and
each step of execution goes from an initial configuration to a final configuration.

{docstring Imperative.Config}

The {name StepStmt}`StepStmt` type describes how each type of statement
transforms configurations. Like with the other components of Strata, the rules
follow standard conventions.

{docstring Imperative.StepStmt}

Like with `Lambda`, we typically want to talk about arbitrarily long sequences
of steps.  The {name StepStmtStar}`Imperative.StepStmtStar` relation describes
the reflexive, transitive closure of the {name StepStmt}`Imperative.StepStmt`
relation.

{docstring Imperative.StepStmtStar}

# Metadata

Metadata allows additional information to be attached to nodes in the Strata
AST. This may include information such as the provenance of specific AST nodes
(_e.g._, the locations in source code that gave rise to them), facts inferred by
specific analyses, or indications of the goal of a specific analysis, among many
other possibilities.

Each metadata element maps a field to a value. A field can be named with a
variable or an arbitrary string.

{docstring Imperative.MetaDataElem.Field}

A value can take the form of an expression or an arbitrary string.

{docstring Imperative.MetaDataElem.Value}

A metadata element pairs a field with a value.

{docstring Imperative.MetaDataElem}

And, finally, the metadata attached to an AST node consists of an array of
metadata elements.

{docstring Imperative.MetaData}

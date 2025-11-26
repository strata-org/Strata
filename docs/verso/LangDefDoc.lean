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
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.LExprTypeSpec

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "The Strata Language Definition" =>
%%%
shortTitle := "The Strata Language"
%%%

# Introduction

Strata aims to provide the foundation for representing the semantics of
programs, specifications, protocols, architectures, and other aspects of
large-scale distributed systems and their components. It achieves this through
languages of two types. The Dialect Definition Mechanism, described
[here](https://github.com/strata-org/Strata/tree/main/docs/verso/DDMDoc.lean),
provides a way to define the syntax and a simple type system for what we call a
dialect of Strata. At the moment, these dialects do not directly have semantics
(though we may add a mechanism for defining their semantics in the future) but
instead are defined by translation to or from the second notion of language,
Strata’s Core languages. Said another way, each of these dialects is a different
concrete way to write Strata programs, but all of these dialects are ultimately
represented internally using the same Core languages.

Dialects are used to describe both the initial artifacts being analyzed by
Strata and more low-level representations of those artifacts used to communicate
with external reasoning tools. In both situations, Stata uses dialects as a
mechanism for communicating with external tools (either language front ends or
generic automated reasoning tools like SMT solvers).

(TODO: funnel diagram showing various dialects in relation to Strata Core)

The Strata Core languages consist of a few building blocks that can be combined
in different ways. This allows concrete dialects to systematically use different
combinations that still share the majority of their implementation. In Lean (and
in principle in most other source languages that could be used to process Strata
programs), the type system can enforce various structural constraints, ensuring
that only expected language constructs show up. The most common use of the
Strata Core languages is in combination: with an imperative statement type
parameterized by an expression type, and with various more fine-grained
adjustments of other parameters. Because these building blocks are typically
used together, it’s reasonable to think of Strata Core as a single language that
can be configured in various ways for different use cases.

The two fundamental building blocks of Strata Core are a representation of
functional programs called `Lambda`, and a representation of imperative programs
called `Imperative`. The `Lambda` language is parameterized by a type system
(TODO: and can be constrained to allow or disallow complex features such as
lambda abstractions and quantifiers). `Lambda` is also parameterized by a set of
built-in types and functions. The `Imperative` language is then parameterized by
the type of expressions allowed. Currently, those expressions will almost always
be some instantiation of `Lambda`, but they may be restricted in some way, such
as disallowing quantifiers. Both Core building blocks are parameterized by a
metadata type, which by default is instantiated with a map from keys to
structured values that can contain expressions (typically from `Lambda`).

The remainder of this document describes the current abstract syntax and
semantics of `Lambda` and `Imperative` in detail, with direct reference to the
Lean source code that defines these languages. We do not consider the Core
language set in stone. It may evolve over time, particularly to add new
fundamental constructs, and this document will be updated as it does.

# Lambda

The `Lambda` language is a standard but generic implementation of the lambda
calculus. It is parameterized by a type for metadata and the type of types
(which may be `Unit`). It includes the standard constructs for constants, free
and bound variables, abstractions, and applications. In addition, it includes a
special type of constant, an operator, to represent built-in functions. It
extends the standard lambda calculus by allowing quantifiers (since a key use of
the language is to write logical predicates) and includes constructors for
if-then-else and equality functions, since those are so commonly used.

Although `Lambda` can be parameterized by an arbitrary type system, the Strata
code base includes an implementation of a polymorphic Hindley-Milner type system
(TODO: link) and inference algorithm (TODO: link) over the type `LTy`. This
allows universal quantification over types and the use of arbitrary named type
constructors (as well as special support for bit vector types, to allow them to
be parameterized by size).

Type inference and checking with this type system takes as input expressions
parameterized by `Unit` as the type of types, and produces expressions
parameterized by `LTy` as output.

## Syntax

The syntax of lambda expressions is provided by the `LExpr` type.

{docstring Lambda.LExpr}

## Type System

Although `LExpr` can be parameterized by an arbitrary type system, Strata
currently implements one, based on the types `LMonoTy` and `LTy`.

The first, `LMonoTy` represents monomorphic types. It's a separate type because
some contexts allow only monomorphic types.

{docstring Lambda.LMonoTy}

The `LTy` type allows monomorphic types to be wrapped in universal type
quantifiers, creating polymorphic types.

{docstring Lambda.LTy}

The relationshp between `LExpr` and `LTy` is expressed by the
`Lambda.LExpr.HasType` relation.

{docstring Lambda.LExpr.HasType}

(TODO: talk about the type inference implementation?)

## Operational Semantics

The semantics of the `LExpr` type are specified using the small-step inductive
relation `Lambda.Step`.

{docstring Lambda.Step}

Typically we will want to talk about arbitrarily long sequences of steps, from
an initial expression to a value. The `Lambda.StepStar` relation describes the
reflexive, transitive closure of the `Lambda.Step` relation.

{docstring Lambda.StepStar}

(TODO: can we use a generic construct for the reflexive, transitive closure of
an arbitrary relation? Both here and for statements?)

# Imperative

The `Imperative` language is a standard core imperative calculus, parameterized
by a type of expressions and divided into two pieces: commands and statements.
Commands represent atomic operations that do not induce control flow (except
possibly in the form of procedure calls that follow a stack discipline).
Statements are parameterized by a command type and describe the control flow
surrounding those commands. Statements exist in three forms, corresponding to
the most common alternative representations. These forms are:

* Structured deterministic statements, each of which can be: a command, a
  sequence of statements in a block, a deterministic conditional, a
  deterministic loop with a condition, or a block exit statement.

* Structured non-deterministic statements, each of which can be: a command, a
  sequence of two statements, an arbitrary choice between two statements, or an
  iteration of a statement an arbitrary number of times.

* Unstructured control-flow graphs where each basic block consists of a sequence
  of commands followed by a terminator command. A terminator command can be: a
  conditional jump to one of two blocks, termination of execution, or a
  non-deterministic jump to any one of an arbitrary number of successor blocks.

Translations exist from structured deterministic statements into either
structured non-deterministic statements or unstructured control-flow graphs.

## Command Syntax

The core built-in set of commands includes variable initializations,
deterministic assignments, non-deterministic assignments ("havoc"), assertions,
and assumptions.

{docstring Imperative.Cmd}

## Command Operational Semantics

The semantics of commands are specified in terms of how they interact with a
program state, written `σ`. A state can be applied to a variable to obtain its
current value. And an expression `e` can be evaluated using the evaluation
functin in a given state: `δ σ e` gives the result of evaluating `e` in state
`σ`. This generic description allows the details of the program state
representation to vary, as long as it supports these operations.

Given a state `σ`, the `InitState` relation describes how a variable obtains its
initial value.

{docstring Imperative.InitState}

The `UpdateState` relation then describes how a variable's value can change.

{docstring Imperative.UpdateState}

Given these two state relations, the semantics of each command is specified in
the standard way.

{docstring Imperative.EvalCmd}

## Structured Deterministic Statement Syntax

Statements allow commands to be organized into standard control flow
arrangements, including sequencing, alternation, and iteration.

{docstring Imperative.Stmt}

{docstring Imperative.Block}

## Structured Deterministic Statement Operational Semantics

{docstring Imperative.Config}

{docstring Imperative.StepStmt}

{docstring Imperative.StepStmtStar}

## Structured Non-Deterministic Statement Syntax

{docstring Imperative.NondetStmt}

## Structured Non-Deterministic Statement Operational Semantics

{docstring Imperative.EvalNondetStmt}

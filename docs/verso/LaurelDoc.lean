/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LiftExpressionAssignments
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.CorePrelude

open Strata.Laurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Laurel Language" =>
%%%
shortTitle := "Laurel"
%%%

# Introduction

Laurel is an intermediate verification language designed to serve as a common
representation for front-end languages such as Java, Python, and JavaScript.
Rather than translating each source language directly to Strata Core, Laurel
provides a higher-level abstraction that captures the shared concepts of these
languages — object-oriented types, mutable heap state, and structured control
flow — and then translates uniformly to Core for verification.

Laurel supports several forms of analysis:

- Deductive verification (via translation to Strata Core and SMT solving)
- Property-based testing
- Data-flow analysis

## Key Design Choices

Laurel makes several deliberate design choices:

- Pure contracts: contracts may only contain pure code that does not modify the
  heap.
- Procedures: instead of separate functions and methods, Laurel has a single
  general concept called a *procedure*.
- Determinism: procedures can be marked as deterministic or nondeterministic.
  For deterministic procedures with a non-empty reads clause, the result can be
  assumed unchanged if the read references are the same.
- Opacity: procedures can have a body that is transparent or opaque. Only an
  opaque body may declare a postcondition.
- Unified StmtExpr: statements and expressions share a single type, reducing
  duplication for constructs like conditionals and variable declarations.
- Loops: the only loop construct is `while`, which can encode `do-while` and
  `for` loops.
- Labelled exits: instead of `break` and `continue`, Laurel provides labelled
  blocks with an `exit` statement, which can model both.

# Types

Laurel's type system includes primitive types, collection types, and
user-defined types.

## Primitive Types

{docstring Strata.Laurel.HighType}

## User-Defined Types

User-defined types come in two categories: composite types and constrained
types.

Composite types have fields and procedures, and may extend other composite
types. Fields declare whether they are mutable and specify their type.

{docstring Strata.Laurel.CompositeType}

{docstring Strata.Laurel.Field}

Constrained types are defined by a base type and a constraint over that type.
Algebraic datatypes can be encoded using composite and constrained types.

{docstring Strata.Laurel.ConstrainedType}

{docstring Strata.Laurel.TypeDefinition}

# Expressions and Statements

Laurel uses a unified `StmtExpr` type that contains both expression-like and
statement-like constructs. This avoids duplication of shared concepts such as
conditionals and variable declarations.

## Operations

{docstring Strata.Laurel.Operation}

## The StmtExpr Type

{docstring Strata.Laurel.StmtExpr}

## Metadata

All AST nodes can carry metadata via the `WithMetadata` wrapper.

{docstring Strata.Laurel.WithMetadata}

# Procedures

Procedures are the main unit of specification and verification in Laurel.

{docstring Strata.Laurel.Procedure}

{docstring Strata.Laurel.Parameter}

{docstring Strata.Laurel.Determinism}

{docstring Strata.Laurel.Body}

# Programs

A Laurel program consists of static procedures, static fields, type
definitions, and constants.

{docstring Strata.Laurel.Program}

# Translation Pipeline

Laurel programs are verified by translating them to Strata Core and then
invoking the Core verification pipeline. The translation involves several
passes, each transforming the Laurel program before the final conversion to
Core.

## Heap Parameterization

The heap parameterization pass transforms procedures that interact with the
heap by adding explicit heap parameters. The heap is modeled as
`Map Composite (Map Field Box)`, where `Box` is a tagged union with
constructors for each primitive type.

Procedures that write the heap receive both an input and output heap parameter.
Procedures that only read the heap receive an input heap parameter. Field reads
and writes are rewritten to use `readField` and `updateField` functions.

## Modifies Clauses

The modifies clause transformation generates frame conditions for procedures
with modifies clauses. For each field constant, it generates a universally
quantified assertion that objects not mentioned in the modifies clause have
their field values preserved between the input and output heaps.

## Lifting Expression Assignments

The expression assignment lifting pass transforms assignments that appear in
expression contexts into preceding statements. This is necessary because Strata
Core does not support assignments within expressions.

## Translation to Core

The final translation converts Laurel types, expressions, statements, and
procedures into their Strata Core equivalents. Pure procedures with transparent
bodies are translated as Core functions, while other procedures become Core
procedures with specifications.

## Core Prelude

The Laurel translator prepends a Core prelude that defines the heap model types
and operations: `Composite`, `Field`, `Box`, `readField`, and `updateField`.

{docstring Strata.Laurel.corePreludeDDM}

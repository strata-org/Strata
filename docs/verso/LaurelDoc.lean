/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ModifiesClauses

open Strata.Laurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Laurel Language" =>
%%%
shortTitle := "Laurel"
%%%

# Introduction

Laurel is an intermediate verification language designed to serve as a target for popular
garbage-collected languages that include imperative features, such as Java, Python, and
JavaScript. Laurel tries to include any features that are common to those three languages.

Laurel enables doing various forms of verification:
- Deductive verification
- (WIP) Model checking
- (WIP) Property based testing
- (WIP) Data-flow analysis

Here are some Laurel language features that are shared between the source languages:
- Statements such as loops and return statements
- Mutation of variables, including in expressions
- Reading and writing of fields of references
- Object oriented concepts such as inheritance, type checking, up and down casting and
  dynamic dispatch
- (WIP) Error handling via exceptions
- (WIP) Higher-order procedures and procedure types
- (WIP) Parametric polymorphism

On top of the above features, Laurel adds features that are useful specifically for verification:
- Assert and assume statements
- Loop invariants
- Pre and postconditions for procedures
- Modifies and reads clauses for procedures
- (WIP) Decreases clauses for procedures and loops
- (WIP) Immutable fields and constructors that support assigning to them
- (WIP) Constrained types
- (WIP) Type invariants
- Forall and exists expressions
- (WIP) Old and fresh expressions
- Unbounded integer and real types
- To be designed constructs for supporting proof writing

A peculiar choice of Laurel is that it does not require imperative code to be encapsulated
using a functional specification. A reason for this is that sometimes the imperative code is
as readable as the functional specification. For example:
```
procedure increment(counter: Counter)
  // In Laurel, this ensures clause can be left out
  ensures counter.value == old(counter.value) + 1
{
  counter.value := counter.value + 1;
};
```

## Implementation Choices

A design choice that impacts the implementation of Laurel is that statements and expressions
share a single implementation type, the StmtExpr. This reduces duplication for constructs
like conditionals and variable declarations. Each StmtExpr has a user facing type, which for
statement-like constructs could be void.

# Types

Laurel's type system includes primitive types, collection types, and user-defined types.

## Primitive Types

{docstring Strata.Laurel.HighType}

## User-Defined Types

User-defined types come in two categories: composite types and constrained types.

Composite types have fields and procedures, and may extend other composite types. Fields
declare whether they are mutable and specify their type.

{docstring Strata.Laurel.CompositeType}

{docstring Strata.Laurel.Field}

Constrained types are defined by a base type and a constraint over the values of the base
type. Algebraic datatypes can be encoded using composite and constrained types.

{docstring Strata.Laurel.ConstrainedType}

{docstring Strata.Laurel.TypeDefinition}

# Sequences and Arrays

Laurel provides two collection types that share a subscript syntax but differ in their
semantics:

- `Seq<T>` — immutable value sequences. Operations like functional update produce new
  sequences, leaving the input unchanged. Variables of type `Seq<T>` are compared by value.
- `Array<T>` — mutable heap-backed arrays. Assigning an array to a new variable creates an
  alias; mutations through one reference are visible through all others.

Currently `Array<T>` is supported only for `T = int`; other element types are
rejected by the pre-pass validator. `Seq<T>` supports any element type.

## Sequence literals

Square-bracket literals construct a `Seq<T>`:

```
var s: Seq<int> := [1, 2, 3];
```

The empty literal `[]` produces `Sequence.empty()`.

## Subscript syntax

The expression `s[i]` reads the element at index `i`:

```
assert s[0] == 1;
```

On a `Seq<T>`, `s[i := v]` produces a new sequence with index `i` set to `v`:

```
var t: Seq<int> := s[0 := 99];  // t differs from s at index 0
```

On an `Array<T>`, `a[i] := v` updates the array in place:

```
var a: Array<int> := [1, 2, 3];
a[0] := 42;
assert a[0] == 42;
```

Out-of-bounds access is a verification obligation. `Sequence.select`,
`Sequence.update`, `Sequence.take`, and `Sequence.drop` carry preconditions
that the index or length argument is in range; the subscript sugar inherits
them. The solver will emit a proof obligation at each subscript site — both
in imperative code and in pure positions like `requires`/`ensures` clauses,
quantifier bodies, and function bodies. If the index cannot be shown to be
in bounds, verification fails with an `outOfBoundsAccess` diagnostic. This
matches how division by zero is checked.

## Sequence operations

The `Sequence` namespace exposes the following operations:

- `Sequence.empty()` — the empty sequence
- `Sequence.build(s, v)` — append `v` to the end of `s`
- `Sequence.select(s, i)` — read index `i`; equivalent to `s[i]`
- `Sequence.update(s, i, v)` — functional update; equivalent to `s[i := v]`
- `Sequence.length(s)` — length
- `Sequence.append(s1, s2)` — concatenate two sequences
- `Sequence.contains(s, v)` — membership test
- `Sequence.take(s, n)` — prefix of length `n`
- `Sequence.drop(s, n)` — suffix after the first `n` elements

## Array length

`Array.length(a)` returns the length of an array. It is internally desugared to
`Sequence.length(a#$data)` and requires its argument to be of type `Array<T>`.

## Array to sequence conversion

`Sequence.fromArray(a)` returns a `Seq<T>` snapshot of an `Array<T>`'s current
contents. The snapshot is independent: subsequent mutations to the array are
not reflected in the returned sequence.

```
var a: Array<int> := [1, 2, 3];
var s: Seq<int> := Sequence.fromArray(a);
a[0] := 99;
assert s[0] == 1;   // the snapshot still holds the original value
assert a[0] == 99;
```

This is the supported idiom for extracting values out of an array. Laurel does
not support implicit `Array<T>` → `Seq<T>` conversion. There is no corresponding
`Seq<T>` → `Array<T>` conversion; constructing an array from a literal or from
another array requires `new`.

## Common mistakes

A pre-pass validator flags five common misuses with helpful messages:

- Using `a[i := v]` (functional update) on an `Array<T>`:

  ```
  var a: Array<int> := [1, 2, 3];
  var b: Array<int> := a[0 := 99];
  //                   ~~~~~~~~~~
  // error: `a[i := v]` is not supported on `Array<T>`: arrays are mutable.
  ```

- Using `s[i] := v` (destructive update) on a `Seq<T>`:

  ```
  var s: Seq<int> := [1, 2, 3];
  s[0] := 42;
  // ~~~~
  // error: `s[i] := v` is not allowed: sequences (`Seq<T>`) are immutable.
  ```

- Calling `Array.length` on something that is not an `Array<T>`:

  ```
  var s: Seq<int> := [1, 2, 3];
  assert Array.length(s) == 3;
  //     ~~~~~~~~~~~~~~~
  // error: `Array.length` requires an argument of type `Array<T>`, got `Seq<int>`.
  ```

- Calling `Sequence.fromArray` on something that is not an `Array<T>`:

  ```
  var s: Seq<int> := [1, 2, 3];
  var t: Seq<int> := Sequence.fromArray(s);
  //                 ~~~~~~~~~~~~~~~~~~~~~
  // error: `Sequence.fromArray` requires an argument of type `Array<T>`,
  //        got `Seq<int>`.
  ```

- Declaring `Array<T>` with a `T` other than `int` (current SMT limitation):

  ```
  var a: Array<bool> := [true, false];
  //     ~~~~~~~~~~~
  // error: `Array<T>` is currently only supported for `T = int`.
  ```

## Internal representation

Arrays are represented internally by a synthetic `$Array` composite with a single
`$data: Seq<int>` field (the `int` element type matches the current
`Array<int>`-only restriction). The `$` prefix is a naming convention used for
compiler-internal names to avoid collisions with user-declared types. The
`$Array` composite is only injected into programs that actually use `Array<T>`.

# Expressions and Statements

Laurel uses a unified `StmtExpr` type that contains both expression-like and statement-like
constructs. This avoids duplication of shared concepts such as conditionals and variable
declarations.

## Operations

{docstring Strata.Laurel.Operation}

## The StmtExpr Type

{docstring Strata.Laurel.StmtExpr}

## Metadata

All AST nodes can carry metadata via the `AstNode` wrapper.

{docstring Strata.Laurel.AstNode}

# Procedures

Procedures are the main unit of specification and verification in Laurel.

{docstring Strata.Laurel.Procedure}

{docstring Strata.Laurel.Parameter}

{docstring Strata.Laurel.Body}

# Programs

A Laurel program consists of procedures, global variables, type definitions, and constants.

{docstring Strata.Laurel.Program}

# Translation Pipeline

Laurel programs are verified by translating them to Strata Core and then invoking the Core
verification pipeline. The translation involves several passes, each transforming the Laurel
program before the final conversion to Core.

## Heap Parameterization

The heap parameterization pass transforms procedures that interact with the heap by adding
explicit heap parameters. The heap is modeled as `Map Composite (Map Field Box)`, where
`Box` is a tagged union with constructors for each primitive type.

Procedures that write the heap receive both an input and output heap parameter. Procedures
that only read the heap receive an input heap parameter. Field reads and writes are rewritten
to use `readField` and `updateField` functions.

## Modifies Clauses

The modifies clause transformation translates modifies clauses into additional ensures
clauses. The modifies clause of a procedure is translated into a quantified assertion that
states that objects not mentioned in the modifies clause have their field values preserved
between the input and output heap.

## Lifting Expression Assignments

The expression assignment lifting pass transforms assignments that appear in expression
contexts into preceding statements. This is necessary because Strata Core does not support
assignments within expressions.

## Translation to Core

The final translation converts Laurel types, expressions, statements, and procedures into
their Strata Core equivalents. Procedures with bodies that only have constructs supported by
Core expressions are translated to a Core function, while other procedures become Core
procedures.

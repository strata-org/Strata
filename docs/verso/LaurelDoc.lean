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

# Design Principles

These principles recur in design discussions on Laurel pull requests and issues. Proposed
features or refactorings that violate them tend to be pushed back.

## Shared between source languages, or don't add it

The defining criterion for a Laurel feature is that it is "useful for Java and something
else". Features that make sense only for one source language (for example, nominal
subtyping specifically for Java generics, or Python's `__getattr__`) belong in the
source-language translator, not in Laurel. Front-ends are expected to encode
language-specific constructs using Laurel's primitives.

Concrete instances of the principle:

- Inheritance is in Laurel because Java, Python and TypeScript all use it.
- Closures and thunks are not first-class in Laurel; they are modelled through the dynamic
  dispatch mechanism — a caller can encode a closure as a composite with a named method and
  use `InstanceCall`.
- Manual memory management is out of scope in the short term.

## Imperative code need not hide behind a functional specification

Laurel does not require imperative code to be encapsulated using a functional specification.
Sometimes the imperative code is as readable as, or more readable than, a functional
specification would be.

Consequences of this decision:

- A Laurel procedure body may be transparent to its callers. There is no requirement that a
  caller only see an `ensures` clause; if the body has no postcondition the caller can see
  (and reason about) the implementation. This is the origin of the transparent / opaque /
  `Body.External` distinction.
- Statements are allowed in expression positions in principle. The compilation pipeline has
  to lift them out eventually (see Lifting Expression Assignments below), but the AST
  admits programs in which an assignment appears as part of an expression. The fact that
  Core cannot represent such programs is not Laurel's problem.

## One AST for statements and expressions

Laurel has a single algebraic type `StmtExpr` that mixes statement-like (`Assign`, `While`,
`Return`, …) and expression-like (`LiteralInt`, `PrimitiveOp`, `IfThenElse`, …)
constructors. Every `StmtExpr` has a user-facing type which, for statement-like
constructors, is `void`. A conditional therefore only needs to be defined once, instead of
once for the expression language and once for the statement language.

The same choice drives why blocks can occur inside expressions: the machinery that handles
a block of statements is exactly the machinery that handles a block used as an
expression-with-side-effects.

## One AST node, many back-ends

Because Laurel targets multiple analyses — deductive verification, and in the future model
checking, property-based testing, and data-flow analysis — semantic features that are
specific to one discharge strategy must not leak into the AST. Opacity, for example, is a
concept connected to deductive verification: it is about how to generate VCs that don't
include too much irrelevant information. Analyses other than deductive verification should
not need to take opacity into account.

## Constructs are not defined by their Core encoding

Laurel features are designed in terms of user expressivity, not in terms of how they lower
to Core. The Core encoding of a Laurel construct can change, and has changed (the heap
encoding was rewritten to use datatypes instead of axioms), without altering the meaning of
the construct in Laurel.

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

# Conventions and Invariants

## Holes are the uniform "unknown" marker

The `.Hole` constructor of `StmtExpr` is Laurel's single representation for an expression
whose identity is not yet known. The `StmtExpr` documentation above describes when
front-ends and error-recovery paths emit one.

`InferHoleTypes` labels every hole with the type its context demands. `EliminateHoles` then
replaces deterministic holes with calls to freshly generated uninterpreted functions.
Non-deterministic holes are preserved by `EliminateHoles` and lowered to havoced variables
later, by `LiftExpressionAssignments`.

A deterministic hole that survives past `EliminateHoles` indicates a pipeline bug — usually
a new translator case that emits a hole inside a constructor the elimination pass does not
traverse (see issue #1176).

## Reserved identifier prefixes

Laurel programs are usually built by deserialization rather than by the Laurel parser, so
the parser itself does not need to police reserved names. Nevertheless, the following
prefixes are reserved for translator-generated identifiers and user programs must not use
them:

- `$heap` — the current heap value inside a procedure body.
- `$heap_in` — the input heap of a heap-mutating procedure.
- `$hole_N` — a freshly generated uninterpreted function replacing a deterministic hole.
- `$__ty_unused_N` — a fresh type variable used as an "unknown type" placeholder.
- `$` prefix in general — reserved for translator-generated names.

## Identifier resolution by unique ID

After the Resolution pass, every identifier reference carries a `uniqueId : Option Nat`
that matches some declaration. Passes must not resolve identifiers by looking at textual
names; post-resolution, the `uniqueId` is authoritative. If a pass needs to know the owning
type of a field, it should use the field's `uniqueId` to look up its declaration in the
model rather than walking back through the composite type hierarchy.

## Determinism of procedure calls

A procedure modelled as a Core function is deterministic: two calls with the same arguments
produce the same result. A procedure modelled via axiomatic postconditions is
non-deterministic unless explicitly declared otherwise. This is why `Body.External` does
not imply transparency: external bodies can still be non-deterministic.

# Translation Pipeline

Laurel programs are verified by translating them to Strata Core and then invoking the Core
verification pipeline. The translation involves several Laurel-to-Laurel lowering passes,
each annotated with whether it invalidates resolution (and therefore causes a re-run of the
resolver), followed by an ordering step and a final "dumb" translation to Core.

After the initial `resolve`, `TypeAliasElim` replaces every type-alias reference with its
resolved target type. The remaining Laurel-to-Laurel passes then run in this order:

1. `FilterNonCompositeModifies` — strip modifies clauses on non-composite reads.
2. `EliminateValueReturns` — remove `Return` from statement positions where values are
   returned.
3. `HeapParameterization` (invalidates resolution) — add `$heap` and `$heap_in` parameters
   to procedures that read or mutate the heap, and rewrite field reads/writes.
4. `TypeHierarchyTransform` (invalidates resolution) — add a `TypeTag` field to composites
   and emit `extends` facts for the inheritance hierarchy.
5. `ModifiesClausesTransform` (invalidates resolution) — translate modifies clauses into
   ensures clauses.
6. `InferHoleTypes` — assign a type to every `Hole` from its context.
7. `EliminateHoles` — replace deterministic holes with calls to freshly generated
   uninterpreted functions. Non-deterministic holes are preserved here and lowered to
   havocs later, by `LiftExpressionAssignments`.
8. `DesugarShortCircuit` — desugar `&&` and `||` into conditional expressions.
9. `LiftExpressionAssignments` — hoist statement-like `StmtExpr`s out of expression
   positions.
10. `EliminateReturns` (invalidates resolution) — remove `Return` from any remaining
    expression contexts.
11. `ConstrainedTypeElim` (invalidates resolution) — peel constrained types down to their
    base types plus generated axioms.

After these Laurel-to-Laurel passes, `CoreGroupingAndOrdering` groups datatypes and
procedures into strongly-connected components so that mutually-recursive definitions can be
emitted together. The final step, the Laurel-to-Core translator, is a largely one-to-one
mapping because all the heavy lifting has already been done by the passes above.

The pipeline stops early if resolution fails. This is a simple way to avoid duplicate
diagnostics: without the early return, resolution errors reported by Laurel would also be
reported by Core. A better solution that lets some resolution errors from Laurel coexist
with verification errors from Core is imaginable, but would need more design work.

The pipeline is intended to be executable: all passes, including the heap and the hole
elimination, avoid axioms in favour of explicit datatypes so that translated programs can
in principle be run with concrete values.

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

It is called a "dumb" translation because, after all the earlier passes have run, the
remaining work is nearly one-to-one. A transparent Laurel procedure whose body fits in a
Core function becomes a Core function with a body. An opaque or postcondition-bearing
procedure becomes a Core function without a body plus an axiom derived from the
postcondition.

Limitations, each a known work item:

- Postconditions on Laurel functions are rejected because Core functions do not yet
  support postconditions.
- Core procedures are always opaque to callers; a transparent Laurel procedure whose body
  is not a Core function cannot currently retain transparency across the translation.

# Error Correction via Holes

When a front-end translator encounters an error in user code, it does not abort the
compilation. Instead it emits a `.Hole` in place of the problematic sub-expression and
records a diagnostic. The rest of the program continues to compile. This is what permits,
for instance, `pyAnalyzeLaurel` to produce useful output on partially broken input.

An error-correcting parser can turn `3 +` into `3 + ?`, where `?` is a hole; an
error-correcting resolver can turn an ill-typed assignment `var y: bool := x` (with `x :
int`) into `var y: bool := ?`. The pipeline's hole infrastructure then ensures that `?`
does not produce further cascading diagnostics — any interaction with `?` is handled
uniformly.

# Relationship with the Python Front-End

Laurel is used as the compilation target for Strata's Python front-end. Every Python user
value is boxed into the Laurel datatype `Any`, which has constructors for each Python base
type (`from_int`, `from_str`, `from_bool`, …) and for exceptions. All user-visible
variables and procedure inputs/outputs are typed `Any` at the Laurel level. The Python-to-
Laurel translator inserts tag assertions (`Any..isfrom_int(x)`) before unwrapping
(`Any..as_int!(x)`).

Laurel's type system is intentionally not the place where Python's type annotations are
enforced. The Python-to-Laurel translator turns those annotations into tag assertions.
Adding PEP 484-style typing features to Laurel is therefore neither necessary nor
obviously desirable for the Python path. It is, however, useful for the Java path, where
type checking inside Laurel's resolver is on the roadmap.

# Known Limits and Roadmap

Items that come up repeatedly in Laurel design discussions and are shared context for
anyone working on Laurel:

- No flow-sensitive narrowing. The Core type checker is flow-insensitive; constructs like
  Python's `isinstance(x, T)` do not refine the type of `x` in the then-branch. Narrowing
  happens by inserting tag checks, and is the translator's responsibility.
- No first-class closures. Encode via composites with named methods.
- Aliasing is not modelled for pure-value container types. The Python front-end uses
  value-semantics `ListAny` / `DictStrAny`; this is a known latent unsoundness.
- `InstanceCall` is only partially implemented in the translator. The plan is to lower it
  to `StaticCall` in an earlier pass.
- Type checking in Laurel's resolver is work in progress. The intent is for
  `resolveStmtExpr` to return a `HighTypeMd` alongside the resolved expression so that
  each constructor can check its children's types during resolution.
- A Contract-and-Proof pass is planned. It will split Laurel procedures into a function
  (the specification) and a proof (the implementation) before lowering, so that contracts
  are lowered uniformly rather than handled case-by-case in the translator.
- Holes that survive the pipeline are not allowed. A hole must either be typed and
  eliminated, or turned into a diagnostic; the invariant is that nothing reaches Core in
  hole form.

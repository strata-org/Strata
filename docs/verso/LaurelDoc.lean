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

# Type checking

Type checking is woven into the resolution pass: every
{name Strata.Laurel.StmtExpr}`StmtExpr` gets a {name Strata.Laurel.HighType}`HighType`, and
mismatches against the surrounding context become diagnostics. The design is
*bidirectional*: each construct is resolved either in *synthesis* mode — return a type
inferred from the expression — or in *checking* mode — verify that the expression has a
given expected type. The two are different functions on
{name Strata.Laurel.synthStmtExpr}`synthStmtExpr` and
{name Strata.Laurel.checkStmtExpr}`checkStmtExpr`.

This page describes the design choices behind the checker. The implementation is in
`Resolution.lean`.

## The two judgments

There are two operations on expressions, written here in standard bidirectional notation:

```
Γ ⊢ e ⇒ T            -- "e synthesizes T"     (synthStmtExpr)
Γ ⊢ e ⇐ T            -- "e checks against T"  (checkStmtExpr)
```

Each construct picks a mode based on whether its type is determined locally (synth) or by
context (check). Mode assignment is part of the design — see _Mode assignment per construct_
below.

The two judgments are connected by a single change-of-direction rule, *subsumption*:

```
Γ ⊢ e ⇒ A      A <: B
─────────────────────  (sub)
     Γ ⊢ e ⇐ B
```

Subsumption is the *only* place the checker switches from check to synth mode. It fires as a
default fallback in {name Strata.Laurel.checkStmtExpr}`checkStmtExpr` for every construct
without a bespoke check rule: synthesize the expression's type, then verify the result is a
subtype of the expected type. Bespoke check rules push the expected type *into*
subexpressions instead of bouncing through synthesis, which keeps error messages localized
and lets the expected type propagate through nested control flow.

## Subtyping and gradual consistency

The relation `<:` is implemented by two Lean functions — both currently stubs, both
intended to be sharpened:

- `isSubtype` — pure subtyping. The stub is structural
  equality via {name Strata.Laurel.highEq}`highEq`. The eventual real version walks the
  `extending` chain for {name Strata.Laurel.CompositeType}`CompositeType`, unfolds
  {name Strata.Laurel.TypeAlias}`TypeAlias` to its target, and unwraps
  {name Strata.Laurel.ConstrainedType}`ConstrainedType` to its base.
- `isConsistentSubtype` — gradual consistency, in
  the Siek–Taha sense. {name Strata.Laurel.HighType.Unknown}`Unknown` is the dynamic type
  `?` and is consistent with everything in either direction; otherwise the relation
  delegates to `isSubtype`. {name Strata.Laurel.HighType.TCore}`TCore` is bivariantly
  consistent for now, as a clearly-labelled migration escape hatch from the Core language —
  this carve-out is intentionally temporary.

Subsumption (and every bespoke check rule) uses
`isConsistentSubtype`, never raw `isSubtype`. That
single choice is what makes the system *gradual*: an expression of type
{name Strata.Laurel.HighType.Unknown}`Unknown` (a hole, an unresolved name, a `Hole _ none`)
flows freely into any typed slot, and any expression flows freely into a slot of type
{name Strata.Laurel.HighType.Unknown}`Unknown`. Strict checking is applied between
fully-known types only.

## What changed from the synth-only design

A previous iteration was synth-only with three *bivariantly-compatible* wildcards:
{name Strata.Laurel.HighType.Unknown}`Unknown`,
{name Strata.Laurel.HighType.UserDefined}`UserDefined`, and
{name Strata.Laurel.HighType.TCore}`TCore`. The
{name Strata.Laurel.HighType.UserDefined}`UserDefined` carve-out was particularly
load-bearing: it meant that *no* assignment, call argument, or comparison involving a user
type was ever rejected, because subtyping wasn't tracked at all and constrained types
weren't unwrapped — we couldn't tell what was safe.

The bidirectional design replaces that with two cleanly-separated concerns:

- {name Strata.Laurel.HighType.Unknown}`Unknown` keeps wildcard semantics, but now as a
  *real* semantic claim (gradual typing) rather than a workaround.
- {name Strata.Laurel.HighType.UserDefined}`UserDefined` becomes a regular type. Once
  `isSubtype` is implemented properly, `Cat ≤ Animal` will
  pass, `Cat ≤ Dog` will fail, and constrained types will be unwrappable to their base. The
  current stub is conservative (structural equality only); it can be tightened
  incrementally without changing any callers.

## Block and `TVoid`

Statement-position constructs that produce no value synthesize
{name Strata.Laurel.HighType.TVoid}`TVoid`:
{name Strata.Laurel.StmtExpr.Return}`Return`,
{name Strata.Laurel.StmtExpr.Exit}`Exit`,
{name Strata.Laurel.StmtExpr.While}`While`,
{name Strata.Laurel.StmtExpr.Assert}`Assert`,
{name Strata.Laurel.StmtExpr.Assume}`Assume`,
{name Strata.Laurel.Variable.Declare}`Var Declare`, and the opaque/abstract/external bodies.
This makes blocks compose cleanly: control-flow statements don't pollute a block's
synthesized type.

A {name Strata.Laurel.StmtExpr.Block}`Block` is statement chaining `{ s_1; …; s_n }`. The
checker treats it permissively in two ways:

1. *Non-last statements are not required to be {name Strata.Laurel.HighType.TVoid}`TVoid`.*
   In synth mode their types are computed and discarded; in check mode they are still
   synthesized rather than checked against `void`. This matches Java/Python/JavaScript
   expression-statement semantics: `f(x);` where `f` returns a value is normal idiomatic
   code, and forcing an explicit discard would be hostile to the imperative style Laurel
   targets. The cost is that `5;` (a literal in statement position) is silently accepted; if
   we ever want to flag that, it should land as a lint, not a type error.

2. *The last statement is the block's type.* Empty blocks have type
   {name Strata.Laurel.HighType.TVoid}`TVoid`. This is what lets a transparent functional
   procedure body be `{ … some statements …; expr }`.

In check mode, the bespoke `Block` rule pushes the expected type into the *last* statement
rather than checking the block's synthesized type at the boundary. This buys two things:
errors fire at the actual offending sub-expression (e.g. inside a deeply nested
{name Strata.Laurel.StmtExpr.IfThenElse}`if`), and the expected type keeps propagating
through nested {name Strata.Laurel.StmtExpr.Block}`Block` /
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` /
{name Strata.Laurel.StmtExpr.Hole}`Hole` /
{name Strata.Laurel.StmtExpr.Quantifier}`Quantifier`. Empty blocks reduce to subsumption of
{name Strata.Laurel.HighType.TVoid}`TVoid` against the expected type.

## Mode assignment per construct

The intended mode for each construct (some are still being converted to bidirectional in
the implementation):

| Construct | Mode | Notes |
|---|---|---|
| Literals, `Var .Local`, `Var .Field`, `New T`, `IsType`, `ReferenceEquals`, `Quantifier`, `Assigned`, `Fresh`, `Hole _ (some T)`, `StaticCall`, `InstanceCall` | synth | type is determined locally |
| `Var .Declare`, `Exit`, `Return`, `While`, `Assert`, `Assume`, `Assign` | synth ⇒ {name Strata.Laurel.HighType.TVoid}`TVoid` | side-effecting; condition operands checked inward |
| `IfThenElse cond t e_opt` | bespoke check | `cond ⇐ TBool`; `t ⇐ T`; `e ⇐ T` if present |
| `Block` | bespoke check | `s_1..s_{n-1}` synth, `s_n ⇐ T`; synth uses last's synthesized type |
| `Hole _ none` | bespoke check | check mode succeeds with `expected`; synth mode → `Unknown` |
| `AsType e T` | synth ⇒ `T` | the cast is the user's claim; no check on `e` |
| `Old`, `ProveBy v _`, `PureFieldUpdate t _ _` | propagate type of subexpr | unchanged |
| `This`, `Abstract`, `All`, `ContractOf` | synth ⇒ {name Strata.Laurel.HighType.Unknown}`Unknown` | type not tracked |

{name Strata.Laurel.StmtExpr.PrimitiveOp}`PrimitiveOp` operands are checked inward against
the operator's expected operand type ({name Strata.Laurel.HighType.TBool}`TBool` for
logical, numeric for arithmetic and ordering, {name Strata.Laurel.HighType.TString}`TString`
for `StrConcat`). {name Strata.Laurel.Operation.Eq}`Eq`/{name Strata.Laurel.Operation.Neq}`Neq`
synthesize both operands and require consistency in either direction
(`isConsistentSubtype l r ∨ isConsistentSubtype r l`).

Arithmetic ops `Neg`/`Add`/…/`ModT` synthesize *the type of the first argument*. This is how
the checker handles {name Strata.Laurel.HighType.TInt}`TInt` /
{name Strata.Laurel.HighType.TReal}`TReal` / {name Strata.Laurel.HighType.TFloat64}`TFloat64`
without a unification step. A consequence: `int + real` is not flagged today, since each
operand passes the numeric check individually. A real fix would be a numeric-promotion or
unification rule; for now this is a known relaxation.

## Two helpers for resolution sites

Some positions (procedure preconditions, decreases, invariants, postconditions, modifies
clauses, constrained-type witness, etc.) need resolution to run but the type of the
expression is either uninteresting or already known by another path. They use:

- {name Strata.Laurel.synthStmtExpr}`synthStmtExpr` — the full synth API, returning
  `(StmtExprMd × HighTypeMd)`.
- {name Strata.Laurel.checkStmtExpr}`checkStmtExpr` — the check API, returning the resolved
  expression and verifying its type is a consistent subtype of the expected type.
- `resolveStmtExpr` — a thin wrapper that calls
  `synthStmtExpr` and discards the synthesized type. Used at sites where typing is not
  enforced (verification annotations, modifies/reads clauses).

The right principle is: when the position has a known expected type
({name Strata.Laurel.HighType.TBool}`TBool` for conditions, numeric for `decreases`, the
declared output for a constant initializer or a functional body), use
{name Strata.Laurel.checkStmtExpr}`checkStmtExpr`. When it doesn't, use
`resolveStmtExpr`. {name Strata.Laurel.synthStmtExpr}`synthStmtExpr`
itself is mostly an internal interface used by other rules.

## Returns and the expected return type

`Return e` synthesizes {name Strata.Laurel.HighType.TVoid}`TVoid` (the construct itself
produces no value), but the *value being returned* should be checked against the enclosing
procedure's declared output type. The intended design: thread the expected return type
through {name Strata.Laurel.ResolveState}`ResolveState`, set it from `proc.outputs` in
{name Strata.Laurel.resolveProcedure}`resolveProcedure` /
{name Strata.Laurel.resolveInstanceProcedure}`resolveInstanceProcedure` before resolving the
body, and have the `Return` rule push the expected type into its value via
{name Strata.Laurel.checkStmtExpr}`checkStmtExpr`. This closes a soundness gap in the
synth-only design where `return 0` in a `bool`-returning procedure was not caught (because
the body's overall synthesized type was {name Strata.Laurel.HighType.TVoid}`TVoid` and the
body-vs-output check was skipped on `TVoid`).

## What this is, in type-system terms

The checker is:

- *bidirectional*, with a single subsumption rule at the synth↔check boundary,
- with a *gradual* relation (`isConsistentSubtype`)
  rather than a strict one — {name Strata.Laurel.HighType.Unknown}`Unknown` is the dynamic
  type, justified by Laurel's targeting of dynamic source languages,
- over a *nominal-with-stubs* subtype relation
  (`isSubtype`) — currently structural equality, intended to
  walk inheritance chains and unwrap aliases / constrained types,
- with *arity tracking via tuple types*
  ({name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr`) for multi-output
  procedures,
- and *side-effecting expressions modeled as*
  {name Strata.Laurel.HighType.TVoid}`TVoid` so blocks, returns, and loops compose cleanly.

The wildcard carve-out for {name Strata.Laurel.HighType.UserDefined}`UserDefined` from the
previous design is gone — user-defined types are no longer a backdoor through the checker.
The {name Strata.Laurel.HighType.TCore}`TCore` carve-out is preserved for now as a
migration aid and is expected to be removed.

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

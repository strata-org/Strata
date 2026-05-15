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

Type checking runs as part of the resolution pass, in `resolveStmtExpr`. Resolution
synthesizes a {name Strata.Laurel.HighType}`HighType` for every {name Strata.Laurel.StmtExpr}`StmtExpr`
bottom-up and emits diagnostics when the synthesized type clashes with what its context
requires.

## Type system at a glance

The checker is *synthesis-only* (no inference, no subtyping) over a flat type lattice, with
three _wildcard_ types that disable checking:

- {name Strata.Laurel.HighType.Unknown}`Unknown` — synthesized when a name fails to resolve,
  when a {name Strata.Laurel.HighType.UserDefined}`UserDefined` reference resolves to the
  wrong kind, or for constructs whose result type isn't tracked
  ({name Strata.Laurel.StmtExpr.This}`This`,
  {name Strata.Laurel.StmtExpr.Abstract}`Abstract`,
  {name Strata.Laurel.StmtExpr.All}`All`,
  {name Strata.Laurel.StmtExpr.ContractOf}`ContractOf`, untyped
  {name Strata.Laurel.StmtExpr.Hole}`Hole`). It is compatible with everything in both
  directions (acts like _any_).
- {name Strata.Laurel.HighType.UserDefined}`UserDefined _` — also treated bivariantly.
  Subtype/inheritance relationships aren't tracked here, and a
  {name Strata.Laurel.HighType.UserDefined}`UserDefined` may be a constrained type wrapping a
  primitive, so it's accepted wherever a primitive is expected.
- {name Strata.Laurel.HighType.TCore}`TCore _` — pass-through types from the Core language;
  never checked.

Everything else ({name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`,
{name Strata.Laurel.HighType.TBool}`TBool`,
{name Strata.Laurel.HighType.TString}`TString`,
{name Strata.Laurel.HighType.TVoid}`TVoid`,
{name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr [..]`) is compared by
*structural equality* via {name Strata.Laurel.highEq}`highEq`. There is no implicit numeric
promotion: {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`, and
{name Strata.Laurel.HighType.TFloat64}`TFloat64` are siblings, not a chain.

{name Strata.Laurel.HighType.TVoid}`TVoid` marks expressions that produce no value
({name Strata.Laurel.StmtExpr.Return}`Return`,
{name Strata.Laurel.StmtExpr.Exit}`Exit`,
{name Strata.Laurel.StmtExpr.While}`While`,
{name Strata.Laurel.StmtExpr.Assert}`Assert`,
{name Strata.Laurel.StmtExpr.Assume}`Assume`,
{name Strata.Laurel.Variable.Declare}`Var Declare`, opaque/abstract/external bodies).
{name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr tys` models the result of a
procedure call with multiple outputs.

## Checking judgments

Four helper checks fire from context positions:

- `checkBool` — accepts {name Strata.Laurel.HighType.TBool}`TBool`,
  {name Strata.Laurel.HighType.Unknown}`Unknown`, or any
  {name Strata.Laurel.HighType.UserDefined}`UserDefined`. Used by
  {name Strata.Laurel.StmtExpr.IfThenElse}`if`/{name Strata.Laurel.StmtExpr.While}`while`
  conditions, logical primitive ops,
  {name Strata.Laurel.StmtExpr.Assert}`Assert`, and
  {name Strata.Laurel.StmtExpr.Assume}`Assume`.
- `checkNumeric` — accepts {name Strata.Laurel.HighType.TInt}`TInt`,
  {name Strata.Laurel.HighType.TReal}`TReal`,
  {name Strata.Laurel.HighType.TFloat64}`TFloat64`,
  {name Strata.Laurel.HighType.Unknown}`Unknown`, or any
  {name Strata.Laurel.HighType.UserDefined}`UserDefined`. Used by arithmetic and ordering
  primitive ops.
- `checkAssignable expected actual` — accepts equality under
  {name Strata.Laurel.highEq}`highEq`, *or* either side being
  {name Strata.Laurel.HighType.Unknown}`Unknown` /
  {name Strata.Laurel.HighType.UserDefined}`UserDefined` /
  {name Strata.Laurel.HighType.TCore}`TCore`. Used by assignment, call arguments, functional
  body vs. declared output, and constant initializers.
- `checkComparable` — same wildcards as `checkAssignable`, but with a symmetric error message.
  Used for the operands of {name Strata.Laurel.Operation.Eq}`==` and
  {name Strata.Laurel.Operation.Neq}`!=`.

The {name Strata.Laurel.HighType.UserDefined}`UserDefined` carve-out in `checkBool` and
`checkNumeric` is conservative on purpose: a constrained type might wrap a
{name Strata.Laurel.HighType.TBool}`bool` or a numeric type.

## Synthesis rules

Literals synthesize their obvious primitive types: integers give
{name Strata.Laurel.HighType.TInt}`TInt`, booleans
{name Strata.Laurel.HighType.TBool}`TBool`, strings
{name Strata.Laurel.HighType.TString}`TString`, decimals
{name Strata.Laurel.HighType.TReal}`TReal`. Variable and field references take their type
from scope; a {name Strata.Laurel.Variable.Declare}`Var (.Declare p)` synthesizes
{name Strata.Laurel.HighType.TVoid}`TVoid` because it is a declaration statement.

Control flow:
- {name Strata.Laurel.StmtExpr.IfThenElse}`if c then t else e_1; …; e_n` — `c` is checked
  against bool; the result type is the _then_-branch type. Else-branch types are discarded.
- {name Strata.Laurel.StmtExpr.Block}`Block [s_1; …; s_n]` — the type is the last
  statement's type, or {name Strata.Laurel.HighType.TVoid}`TVoid` if empty. This is what makes
  a transparent functional body usable as a value.
- {name Strata.Laurel.StmtExpr.While}`While`,
  {name Strata.Laurel.StmtExpr.Exit}`Exit`,
  {name Strata.Laurel.StmtExpr.Return}`Return _`,
  {name Strata.Laurel.StmtExpr.Assert}`Assert`,
  {name Strata.Laurel.StmtExpr.Assume}`Assume` — all synthesize
  {name Strata.Laurel.HighType.TVoid}`TVoid`. The condition positions of
  {name Strata.Laurel.StmtExpr.While}`While`,
  {name Strata.Laurel.StmtExpr.Assert}`Assert`, and
  {name Strata.Laurel.StmtExpr.Assume}`Assume` enforce `checkBool`.

Calls ({name Strata.Laurel.StmtExpr.StaticCall}`StaticCall`,
{name Strata.Laurel.StmtExpr.InstanceCall}`InstanceCall`) synthesize each argument, then apply
`checkAssignable param arg` pairwise.
{name Strata.Laurel.StmtExpr.InstanceCall}`InstanceCall` drops the first parameter (the
implicit `self`). The return type is determined as follows:
- procedure with one output → that output's type
- procedure with `n ≠ 1` outputs →
  {name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr [t_1, …, t_n]`
- datatype constructor whose name contains `..is` →
  {name Strata.Laurel.HighType.TBool}`TBool` (testers)
- other datatype constructors → {name Strata.Laurel.HighType.UserDefined}`UserDefined T`
- parameters or constants in callee position → their declared type
- anything else → {name Strata.Laurel.HighType.Unknown}`Unknown`

Primitive ops (see {name Strata.Laurel.Operation}`Operation`):
- {name Strata.Laurel.Operation.And}`And`,
  {name Strata.Laurel.Operation.Or}`Or`,
  {name Strata.Laurel.Operation.AndThen}`AndThen`,
  {name Strata.Laurel.Operation.OrElse}`OrElse`,
  {name Strata.Laurel.Operation.Not}`Not`,
  {name Strata.Laurel.Operation.Implies}`Implies` — operands `checkBool`; result
  {name Strata.Laurel.HighType.TBool}`TBool`.
- {name Strata.Laurel.Operation.Lt}`Lt`,
  {name Strata.Laurel.Operation.Leq}`Leq`,
  {name Strata.Laurel.Operation.Gt}`Gt`,
  {name Strata.Laurel.Operation.Geq}`Geq` — operands `checkNumeric`; result
  {name Strata.Laurel.HighType.TBool}`TBool`.
- {name Strata.Laurel.Operation.Eq}`Eq`,
  {name Strata.Laurel.Operation.Neq}`Neq` — `checkComparable lhs rhs` (binary only); result
  {name Strata.Laurel.HighType.TBool}`TBool`.
- {name Strata.Laurel.Operation.Neg}`Neg`,
  {name Strata.Laurel.Operation.Add}`Add`,
  {name Strata.Laurel.Operation.Sub}`Sub`,
  {name Strata.Laurel.Operation.Mul}`Mul`,
  {name Strata.Laurel.Operation.Div}`Div`,
  {name Strata.Laurel.Operation.Mod}`Mod`,
  {name Strata.Laurel.Operation.DivT}`DivT`,
  {name Strata.Laurel.Operation.ModT}`ModT` — operands `checkNumeric`; result is the type of
  the first argument.
- {name Strata.Laurel.Operation.StrConcat}`StrConcat` — no operand check; result
  {name Strata.Laurel.HighType.TString}`TString`.

The _result is the type of the first argument_ rule is how arithmetic handles
{name Strata.Laurel.HighType.TInt}`TInt` / {name Strata.Laurel.HighType.TReal}`TReal` /
{name Strata.Laurel.HighType.TFloat64}`TFloat64` without a unification step. A consequence:
`int + real` will not be flagged, since each operand individually passes `checkNumeric`.

Other forms:
- {name Strata.Laurel.StmtExpr.New}`New T` synthesizes
  {name Strata.Laurel.HighType.UserDefined}`UserDefined T`, falling back to
  {name Strata.Laurel.HighType.Unknown}`Unknown` if `T` resolved to the wrong kind.
- {name Strata.Laurel.StmtExpr.AsType}`AsType e T` synthesizes `T`.
  {name Strata.Laurel.StmtExpr.IsType}`IsType _ _` and
  {name Strata.Laurel.StmtExpr.ReferenceEquals}`ReferenceEquals` synthesize
  {name Strata.Laurel.HighType.TBool}`TBool`.
- {name Strata.Laurel.StmtExpr.Quantifier}`Quantifier`,
  {name Strata.Laurel.StmtExpr.Assigned}`Assigned`,
  {name Strata.Laurel.StmtExpr.Fresh}`Fresh` synthesize
  {name Strata.Laurel.HighType.TBool}`TBool`.
- {name Strata.Laurel.StmtExpr.Old}`Old e` and
  {name Strata.Laurel.StmtExpr.ProveBy}`ProveBy val proof` propagate the type of their first
  sub-expression. {name Strata.Laurel.StmtExpr.PureFieldUpdate}`PureFieldUpdate target …`
  propagates the type of `target`.
- {name Strata.Laurel.StmtExpr.Hole}`Hole _ (some T)` synthesizes `T`.
  {name Strata.Laurel.StmtExpr.Hole}`Hole _ none`,
  {name Strata.Laurel.StmtExpr.This}`This`,
  {name Strata.Laurel.StmtExpr.Abstract}`Abstract`,
  {name Strata.Laurel.StmtExpr.All}`All`, and
  {name Strata.Laurel.StmtExpr.ContractOf}`ContractOf` synthesize
  {name Strata.Laurel.HighType.Unknown}`Unknown`.

## Checking positions

There is no separate checking mode — checking happens by synthesizing and then invoking one of
the four helpers above. The places that check:

1. *Assignment.* Target count must equal RHS arity
   ({name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr` length, else 1), suppressed
   when RHS is {name Strata.Laurel.HighType.TVoid}`TVoid`. When single-target and arities
   match, `checkAssignable target_ty value_ty` runs.
2. *Call arguments.* `checkAssignable param_ty arg_ty` for each pair (instance calls skip
   `self`).
3. *Functional procedure body.* When a {name Strata.Laurel.Procedure}`Procedure` is
   `isFunctional`, has a transparent body, exactly one output, and the body type is not
   {name Strata.Laurel.HighType.TVoid}`TVoid`, `checkAssignable output_ty body_ty` runs.
4. *Constant initializer.* `checkAssignable declared_ty init_ty`, skipped when the
   initializer is {name Strata.Laurel.HighType.TVoid}`TVoid`.

## Summary

In type-system terms, the checker is:

- *monomorphic, structurally-equal, no-subtyping* over primitive types,
- with a *gradual / dynamic escape hatch* — {name Strata.Laurel.HighType.Unknown}`Unknown`,
  {name Strata.Laurel.HighType.UserDefined}`UserDefined`, and
  {name Strata.Laurel.HighType.TCore}`TCore` are bivariantly compatible with everything, so
  unresolved names, user-defined types, and Core types never produce spurious mismatches,
- in *synthesis-only direction* (no contextual checking flowing into expressions),
- with *arity tracking via tuple types*
  ({name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr`) for multi-output
  procedures,
- and *side-effecting expressions modeled as*
  {name Strata.Laurel.HighType.TVoid}`TVoid` so blocks, returns, and loops compose cleanly.

The wildcard carve-outs are the dominant design choice: the checker's behavior on
user-defined and unresolved-kind code is essentially _anything goes_, and strict checking
applies only between the built-in primitive types.

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

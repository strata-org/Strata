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
mismatches against the surrounding context become diagnostics. The implementation is in
`Resolution.lean`.

## Design

### Bidirectional type checking

There are two operations on expressions, written here in standard bidirectional notation:

```
e ⇒ T            -- "e synthesizes T"     (synthStmtExpr)
e ⇐ T            -- "e checks against T"  (checkStmtExpr)
```

Synthesis returns a type inferred from the expression itself; checking verifies that the
expression has a given expected type. Each construct picks a mode based on whether its type
is determined locally (synth) or by context (check). The two judgments are connected by a
single change-of-direction rule, *subsumption*:

```
e ⇒ A      A <: B
─────────────────  (Sub)
     e ⇐ B
```

Subsumption is the *only* place the checker switches from check to synth mode. It fires as
the default fallback in
{name Strata.Laurel.checkStmtExpr}`checkStmtExpr` for every construct without a bespoke
check rule: synthesize the expression's type, then verify the result is a subtype of the
expected type. Bespoke check rules push the expected type *into* subexpressions instead of
bouncing through synthesis, which keeps error messages localized and lets the expected type
propagate through nested control flow.

`synthStmtExpr` and `checkStmtExpr` are mutually recursive: synth rules invoke check on
subexpressions whose expected type is known (e.g. `cond ⇐ TBool` in
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse`), and `checkStmtExpr` falls back to
`synthStmtExpr` via Sub. Termination uses a lexicographic measure `(exprMd, tag)` where the
tag is `0` for synth and `1` for check; any descent into a strict subterm decreases via
`Prod.Lex.left`, while Sub calls synth on the *same* expression and decreases via
`Prod.Lex.right`. This is the standard well-founded encoding for bidirectional systems.

There is also a thin `resolveStmtExpr` wrapper that calls `synthStmtExpr` and discards the
synthesized type. It's used at sites where typing is not enforced (verification annotations,
modifies/reads clauses). The right principle for new call sites is: when the position has a
known expected type ({name Strata.Laurel.HighType.TBool}`TBool` for conditions, numeric for
`decreases`, the declared output for a constant initializer or a functional body), use
`checkStmtExpr`. When it doesn't, use `resolveStmtExpr`. `synthStmtExpr` itself is mostly an
internal interface used by other rules.

### Gradual typing

The relation `<:` is implemented by two Lean functions — both currently stubs, both
intended to be sharpened:

- `isSubtype` — pure subtyping. The stub is structural equality via
  {name Strata.Laurel.highEq}`highEq`. The eventual real version walks the `extending`
  chain for {name Strata.Laurel.CompositeType}`CompositeType`, unfolds
  {name Strata.Laurel.TypeAlias}`TypeAlias` to its target, and unwraps
  {name Strata.Laurel.ConstrainedType}`ConstrainedType` to its base.
- `isConsistentSubtype` — gradual consistency, in the Siek–Taha sense.
  {name Strata.Laurel.HighType.Unknown}`Unknown` is the dynamic type `?` and is consistent
  with everything in either direction; otherwise the relation delegates to `isSubtype`.
  {name Strata.Laurel.HighType.TCore}`TCore` is bivariantly consistent for now, as a
  clearly-labelled migration escape hatch from the Core language — this carve-out is
  intentionally temporary.

Subsumption (and every bespoke check rule) uses `isConsistentSubtype`, never raw
`isSubtype`. That single choice is what makes the system *gradual*: an expression of type
{name Strata.Laurel.HighType.Unknown}`Unknown` (a hole, an unresolved name, a `Hole _ none`)
flows freely into any typed slot, and any expression flows freely into a slot of type
{name Strata.Laurel.HighType.Unknown}`Unknown`. Strict checking is applied between
fully-known types only.

A previous iteration was synth-only with three *bivariantly-compatible* wildcards:
{name Strata.Laurel.HighType.Unknown}`Unknown`,
{name Strata.Laurel.HighType.UserDefined}`UserDefined`, and
{name Strata.Laurel.HighType.TCore}`TCore`. The
{name Strata.Laurel.HighType.UserDefined}`UserDefined` carve-out was load-bearing: no
assignment, call argument, or comparison involving a user type was ever rejected. The
bidirectional design retires that carve-out — user-defined types are now a regular
participant in `<:`, and tightening `isSubtype` (to walk inheritance and unwrap
constrained types) gradually buys real checking on user-defined code without changing
callers.

Side-effecting constructs synthesize {name Strata.Laurel.HighType.TVoid}`TVoid`. This
includes {name Strata.Laurel.StmtExpr.Return}`Return`,
{name Strata.Laurel.StmtExpr.Exit}`Exit`, {name Strata.Laurel.StmtExpr.While}`While`,
{name Strata.Laurel.StmtExpr.Assert}`Assert`, {name Strata.Laurel.StmtExpr.Assume}`Assume`,
{name Strata.Laurel.Variable.Declare}`Var Declare`, and the opaque/abstract/external bodies
— recorded in the rules below.

## Typing rules

Each construct is given as a derivation. `(impl)` = implemented; `(planned)` = intended,
not yet wired in. `(impl-ish)` = implemented but still calls a legacy helper (`checkBool` /
`checkNumeric`/`checkAssignable`) instead of going through `checkStmtExpr`; functionally
equivalent under `<:`.

### Sub (subsumption)

```
e ⇒ A      A <: B
─────────────────  (Sub, impl)
     e ⇐ B
```

Fallback in `checkStmtExpr` whenever no bespoke check rule applies.

### LiteralInt

```
─────────────────────  (Lit-Int, impl)
 LiteralInt n ⇒ TInt
```

### LiteralBool

```
──────────────────────  (Lit-Bool, impl)
 LiteralBool b ⇒ TBool
```

### LiteralString

```
────────────────────────────  (Lit-String, impl)
 LiteralString s ⇒ TString
```

### LiteralDecimal

```
─────────────────────────────  (Lit-Decimal, impl)
 LiteralDecimal d ⇒ TReal
```

### Var (.Local)

```
   Γ(x) = T
──────────────────────  (Var-Local, impl)
 Var (.Local x) ⇒ T
```

### Var (.Field)

```
  e ⇒ _      Γ(f) = T_f
─────────────────────────  (Var-Field, impl)
 Var (.Field e f) ⇒ T_f
```

Resolution looks `f` up against the type of `e` (or the enclosing instance type for
`self.f`); the typing rule itself is path-agnostic.

### Var (.Declare)

```
  Γ(x) ↦ T fresh
──────────────────────────────────  (Var-Declare, impl)
 Var (.Declare ⟨x, T⟩) ⇒ TVoid
```

### IfThenElse

```
cond ⇐ TBool      thenBr ⇒ T
─────────────────────────────────────────  (If-NoElse, impl)
 IfThenElse cond thenBr none ⇒ TVoid


cond ⇐ TBool      thenBr ⇒ T_t      elseBr ⇒ T_e
─────────────────────────────────────────────────  (If-Synth, impl)
 IfThenElse cond thenBr (some elseBr) ⇒ T_t


cond ⇐ TBool      thenBr ⇐ T      elseBr ⇐ T
─────────────────────────────────────────────  (If-Check, planned)
 IfThenElse cond thenBr (some elseBr) ⇐ T
```

If-NoElse uses {name Strata.Laurel.HighType.TVoid}`TVoid` because there is no value when
`cond` is false; without it, `x : int := if c then 5` would type-check spuriously.

If-Synth picks the then-branch arbitrarily and does *not* compare branches: a statement-
position `if` often pairs a value branch with a `return`/`exit`/`assert`. The surrounding
context's `checkAssignable` or Sub provides the actual check downstream.

### Block

```
  s_1 ⇒ _      …      s_{n-1} ⇒ _      s_n ⇒ T
───────────────────────────────────────────────────  (Block-Synth, impl)
 Block [s_1; …; s_n] label ⇒ T


────────────────────────  (Block-Synth-Empty, impl)
 Block [] label ⇒ TVoid


  s_1 ⇒ _      …      s_{n-1} ⇒ _      s_n ⇐ T
───────────────────────────────────────────────────  (Block-Check, impl)
 Block [s_1; …; s_n] label ⇐ T


  TVoid <: T
──────────────────────  (Block-Check-Empty, impl)
 Block [] label ⇐ T
```

Non-last statements are synthesized but their types discarded (the lax rule). This matches
Java/Python/JS where `f(x);` is normal even when `f` returns a value. The trade-off: `5;`
is silently accepted; flagging it belongs to a lint.

Check mode pushes `T` into the *last* statement instead of comparing the block's
synthesized type at the boundary. Errors then fire at the offending subexpression, and `T`
keeps propagating through nested {name Strata.Laurel.StmtExpr.Block}`Block` /
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` /
{name Strata.Laurel.StmtExpr.Hole}`Hole` /
{name Strata.Laurel.StmtExpr.Quantifier}`Quantifier`.

### Exit

```
─────────────────────  (Exit, impl)
 Exit target ⇒ TVoid
```

### Return

```
─────────────────────────  (Return-None, impl)
 Return none ⇒ TVoid


      e ⇒ _
──────────────────────────  (Return-Some, impl)
 Return (some e) ⇒ TVoid


  Γ_proc.outputs = [T]      e ⇐ T
─────────────────────────────────  (Return-Some-Checked, planned)
       Return (some e) ⇒ TVoid
```

`Return-Some` currently throws away the value's type, so `return 0` in a `bool`-returning
procedure isn't caught. The planned rule threads the expected return type through
{name Strata.Laurel.ResolveState}`ResolveState` (set from `proc.outputs` in
{name Strata.Laurel.resolveProcedure}`resolveProcedure` /
{name Strata.Laurel.resolveInstanceProcedure}`resolveInstanceProcedure`).

### While

```
  cond ⇐ TBool      invs_i ⇐ TBool      dec ⇐ ?      body ⇒ _
─────────────────────────────────────────────────────────────  (While, impl-ish)
       While cond invs dec body ⇒ TVoid
```

`dec` (the optional decreases clause) is currently resolved without a type check; the
intended target is a numeric type, not yet enforced.

### Assert

```
     cond ⇐ TBool
──────────────────────────  (Assert, impl-ish)
   Assert cond ⇒ TVoid
```

### Assume

```
    cond ⇐ TBool
─────────────────────  (Assume, impl-ish)
 Assume cond ⇒ TVoid
```

### Assign

```
  Γ(x) = T_x      e ⇒ T_e      T_e <: T_x
─────────────────────────────────────────  (Assign-Single, impl-ish)
       Assign [x] e ⇒ TVoid


  targets ⇒ Ts      e ⇒ MultiValuedExpr Us      |Ts| = |Us|      U_i <: T_i
─────────────────────────────────────────────────────────────────────────────  (Assign-Multi, impl-ish)
                       Assign targets e ⇒ TVoid
```

### StaticCall

```
  callee = static-procedure with inputs Ts and outputs [T]
  args ⇒ Us      U_i <: T_i (pairwise)
────────────────────────────────────────────────────────────  (Static-Call, impl-ish)
              StaticCall callee args ⇒ T


  callee = static-procedure with inputs Ts and outputs [T_1; …; T_n], n ≠ 1
  args ⇒ Us      U_i <: T_i (pairwise)
─────────────────────────────────────────────────────────────────────────────  (Static-Call-Multi, impl-ish)
       StaticCall callee args ⇒ MultiValuedExpr [T_1; …; T_n]
```

### InstanceCall

```
  target ⇒ _      callee = instance-procedure with inputs [self; Ts] and outputs [T]
  args ⇒ Us      U_i <: T_i (pairwise; self is dropped)
─────────────────────────────────────────────────────────────────────────────────────  (Instance-Call, impl-ish)
                       InstanceCall target callee args ⇒ T
```

### PrimitiveOp (logical)

```
  args_i ⇐ TBool                                 op ∈ {And, Or, AndThen, OrElse, Not, Implies}
─────────────────────────────  (Op-Bool, impl-ish)
 PrimitiveOp op args ⇒ TBool
```

### PrimitiveOp (comparison)

```
  args_i ⇐ Numeric                                 op ∈ {Lt, Leq, Gt, Geq}
─────────────────────────────  (Op-Cmp, impl-ish)
 PrimitiveOp op args ⇒ TBool
```

`Numeric` abbreviates "consistent with one of {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`".

### PrimitiveOp (equality)

```
  lhs ⇒ T_l      rhs ⇒ T_r      T_l <: T_r ∨ T_r <: T_l                       op ∈ {Eq, Neq}
──────────────────────────────────────────────────────  (Op-Eq, impl-ish)
       PrimitiveOp op [lhs; rhs] ⇒ TBool
```

### PrimitiveOp (arithmetic)

```
  args_i ⇐ Numeric      args.head ⇒ T                       op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}
──────────────────────────────────────────  (Op-Arith, impl-ish)
       PrimitiveOp op args ⇒ T
```

"Result is the type of the first argument" handles `int + int → int`, `real + real → real`,
etc. without unification. Known relaxation: `int + real` passes (each operand individually
passes `Numeric`); a proper fix needs numeric promotion or unification.

### PrimitiveOp (string concatenation)

```
  args_i ⇐ TString                                 op = StrConcat
─────────────────────────────  (Op-Concat, planned)
 PrimitiveOp op args ⇒ TString
```

Operand check not yet implemented — `StrConcat` accepts any operands today.

### New

```
  ref resolves to a composite or datatype T
─────────────────────────────────────────────  (New-Ok, impl)
            New ref ⇒ UserDefined T


  ref does not resolve to a composite or datatype
─────────────────────────────────────────────────  (New-Fallback, impl)
                  New ref ⇒ Unknown
```

### AsType

```
      target ⇒ _
─────────────────────  (AsType, impl)
 AsType target T ⇒ T
```

`target` is resolved but not checked against `T` — the cast is the user's claim.

### IsType

```
       target ⇒ _
──────────────────────────  (IsType, impl)
 IsType target T ⇒ TBool
```

### ReferenceEquals

```
        lhs ⇒ _      rhs ⇒ _
───────────────────────────────  (RefEq, impl)
 ReferenceEquals lhs rhs ⇒ TBool
```

### Quantifier

```
  body ⇒ _
─────────────────────────────────────────────  (Quantifier, impl)
 Quantifier mode ⟨x, T⟩ trig body ⇒ TBool
```

### Assigned

```
       name ⇒ _
─────────────────────────  (Assigned, impl)
 Assigned name ⇒ TBool
```

### Old

```
   v ⇒ T
─────────────  (Old, impl)
 Old v ⇒ T
```

### Fresh

```
     v ⇒ _
──────────────────  (Fresh, impl)
 Fresh v ⇒ TBool
```

### ProveBy

```
   v ⇒ T      proof ⇒ _
──────────────────────────  (ProveBy, impl)
   ProveBy v proof ⇒ T
```

### PureFieldUpdate

```
       target ⇒ T_t      newVal ⇒ _
─────────────────────────────────────  (PureFieldUpdate, impl)
 PureFieldUpdate target f newVal ⇒ T_t
```

### This

```
─────────────────────  (This, impl)
   This ⇒ Unknown
```

### Abstract / All / ContractOf

```
────────────────────────────────────────  (Abstract / All / ContractOf, impl)
 Abstract / All / ContractOf … ⇒ Unknown
```

### Hole

```
───────────────────────  (Hole-Some, impl)
 Hole d (some T) ⇒ T


─────────────────────────  (Hole-None-Synth, impl)
 Hole d none ⇒ Unknown


  Unknown <: T
──────────────────────  (Hole-None-Check, planned)
 Hole d none ⇐ T
```

In check mode today, `Hole d none ⇐ T` reduces to subsumption (`Unknown <: T`, which always
holds). The planned bespoke rule would record the inferred `T` on the hole node so
downstream passes can see it, instead of leaving `none` until the hole-inference pass.

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

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

## Notation

Typing rules are written in the standard derivation-tree form: premises above the line,
conclusion below, rule name on the right.

```
premise_1   premise_2   …   premise_n
─────────────────────────────────────  (Rule-Name)
              conclusion
```

We use:

- `e ⇒ T` — _e_ synthesizes _T_ (synth mode, `synthStmtExpr`).
- `e ⇐ T` — _e_ checks against _T_ (check mode, `checkStmtExpr`).
- `T <: U` — gradual consistency-subtyping, i.e. `isConsistentSubtype T U`.
- `Γ` for the lexical scope is left implicit — every rule threads it identically.

Side-effecting constructs synthesize {name Strata.Laurel.HighType.TVoid}`TVoid`. This
includes {name Strata.Laurel.StmtExpr.Return}`Return`,
{name Strata.Laurel.StmtExpr.Exit}`Exit`, {name Strata.Laurel.StmtExpr.While}`While`,
{name Strata.Laurel.StmtExpr.Assert}`Assert`, {name Strata.Laurel.StmtExpr.Assume}`Assume`,
{name Strata.Laurel.Variable.Declare}`Var Declare`, and the opaque/abstract/external bodies
— they're recorded in the rules below.

## Subsumption (the synth↔check boundary)

```
e ⇒ A      A <: B
─────────────────  (Sub)
     e ⇐ B
```

Subsumption is the *only* place check switches to synth. It fires as the default fallback
in `checkStmtExpr` for every construct without a bespoke check rule. Bespoke check rules
push the expected type *into* subexpressions, which keeps errors localized.

## Typing rules

Below, each construct is given as a derivation. Rules marked with ✓ in the implementation
column are implemented today; rules marked ✗ are planned. The current implementation has
bespoke check rules for {name Strata.Laurel.StmtExpr.Block}`Block` only; everything else
reaches check mode through Sub. Where a synth rule pushes an expected type into a
subexpression (e.g. `cond ⇐ TBool` in {name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse`),
that's listed as a premise.

### Literals and references

```
                                                          (Lit-Int)  ✓
─────────────                ────────────────                ─────────────────
 LiteralInt n ⇒ TInt          LiteralBool b ⇒ TBool          LiteralString s ⇒ TString

────────────────────────                       Γ(x) = T
 LiteralDecimal d ⇒ TReal                  ─────────────────  (Var-Local)  ✓
                                            Var (.Local x) ⇒ T

  e ⇒ _      Γ(f) = T_f                            Γ(x) ↦ T fresh
─────────────────────────  (Var-Field)  ✓     ─────────────────────────  (Var-Declare)  ✓
   Var (.Field e f) ⇒ T_f                       Var (.Declare ⟨x, T⟩) ⇒ TVoid
```

`Var (.Field e f)` resolves `f` against the type of `e` (or the enclosing instance type for
`self.f`); the typing rule is independent of which path resolution took.

### IfThenElse

```
cond ⇐ TBool      thenBr ⇒ T
─────────────────────────────  (If-NoElse)  ✓
   IfThenElse cond thenBr none ⇒ TVoid

cond ⇐ TBool      thenBr ⇒ T_t      elseBr ⇒ T_e
─────────────────────────────────────────────────  (If-Synth)  ✓
   IfThenElse cond thenBr (some elseBr) ⇒ T_t

cond ⇐ TBool      thenBr ⇐ T      elseBr ⇐ T
─────────────────────────────────────────────  (If-Check)  ✗ (planned)
       IfThenElse cond thenBr (some elseBr) ⇐ T
```

If-Synth picks the then-branch type by convention; the result is always consumed by an
enclosing `checkAssignable` or by Sub, which provides a one-sided check against the
surrounding context. The two branches are deliberately not compared against each other:
statement-position `if`s commonly mix a value branch with a
{name Strata.Laurel.HighType.TVoid}`TVoid` branch (early `return`, `exit`, `assert`, …),
which a strict equality check would reject incorrectly.

If-NoElse synthesizes {name Strata.Laurel.HighType.TVoid}`TVoid` because there is no value
to give back when `cond` is false. This rejects `x : int := if c then 5` at the assignment.

### Block

```
                           none of these statements has a typing premise
                          (their synthesized types are discarded — lax)
                           ───────────────────────────────────────────
                                  s_1 ⇒ _      …      s_{n-1} ⇒ _      s_n ⇒ T
                          ────────────────────────────────────────────────────────  (Block-Synth)  ✓
                                            Block [s_1; …; s_n] label ⇒ T

────────────────────  (Block-Synth-Empty)  ✓
 Block [] label ⇒ TVoid

  s_1 ⇒ _    …    s_{n-1} ⇒ _      s_n ⇐ T
─────────────────────────────────────────────  (Block-Check)  ✓
       Block [s_1; …; s_n] label ⇐ T

  TVoid <: T
─────────────────────  (Block-Check-Empty)  ✓
 Block [] label ⇐ T
```

Block-Synth is lax: non-last statements are synthesized but their types are discarded.
This matches Java/Python/JavaScript expression-statement semantics: `f(x);` where `f`
returns a value is normal idiomatic code. The cost is that `5;` (a literal in statement
position) is silently accepted; flagging it would belong to a lint, not the type checker.

Block-Check pushes the expected type into the *last* statement rather than checking the
block's synthesized type at the boundary. Errors then fire at the offending subexpression
inside `s_n` rather than at the surrounding {name Strata.Laurel.StmtExpr.Block}`Block`, and
the expected type keeps propagating through nested
{name Strata.Laurel.StmtExpr.Block}`Block` /
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` /
{name Strata.Laurel.StmtExpr.Hole}`Hole` /
{name Strata.Laurel.StmtExpr.Quantifier}`Quantifier`. Empty blocks reduce to a subsumption
check of {name Strata.Laurel.HighType.TVoid}`TVoid` against the expected type.

### Statements that synthesize TVoid

```
─────────────────  (Exit)  ✓        cond ⇐ TBool      invs ⇐ TBool      dec ⇐ ?      body ⇒ _
 Exit target ⇒ TVoid           ────────────────────────────────────────────────────────────────  (While)  ✓-ish
                                                  While cond invs dec body ⇒ TVoid


─────────────────────────  (Return-None)  ✓        e ⇒ _
 Return none ⇒ TVoid                       ─────────────────────  (Return-Some)  ✓
                                            Return (some e) ⇒ TVoid


cond ⇐ TBool                          cond ⇐ TBool
──────────────────  (Assert)  ✓-ish   ──────────────  (Assume)  ✓-ish
 Assert cond ⇒ TVoid                   Assume cond ⇒ TVoid


  Γ(x) = T_x      e ⇒ T_e      T_e <: T_x                              targets ⇒ Ts      e ⇒ MultiValuedExpr Us      |Ts| = |Us|     U_i <: T_i
─────────────────────────────────────────  (Assign-Single)  ✓-ish    ───────────────────────────────────────────────────────────────────  (Assign-Multi)  ✓-ish
        Assign [x] e ⇒ TVoid                                                                 Assign targets e ⇒ TVoid
```

✓-ish marks rules that are implemented but still call the legacy `checkBool` /
`checkAssignable` helpers rather than `checkStmtExpr cond TBool`. Functionally equivalent
under the gradual relation `<:` (since `checkBool` accepts the same types as
`isConsistentSubtype _ TBool` modulo the temporary {name Strata.Laurel.HighType.TCore}`TCore`
carve-out); slated to be migrated to `checkStmtExpr`.

The {name Strata.Laurel.StmtExpr.Return}`Return`-with-value rule today only resolves `e`
without checking it against the enclosing procedure's declared output type. The intended
rule is:

```
  Γ_proc.outputs = [T]     e ⇐ T
─────────────────────────────────  (Return-Some-Checked)  ✗ (planned)
       Return (some e) ⇒ TVoid
```

This requires threading the expected return type through `ResolveState`. Without it,
`return 0` in a `bool`-returning procedure goes uncaught.

### Calls and primitive operations

```
  callee resolves to procedure with inputs Ts and outputs [T]
  args ⇒ Us      U_i <: T_i (pairwise)
──────────────────────────────────────────────────────────────  (Static-Call)  ✓-ish
                  StaticCall callee args ⇒ T

  callee resolves to procedure with inputs Ts and outputs [T_1; …; T_n]   (n ≠ 1)
  args ⇒ Us      U_i <: T_i (pairwise)
─────────────────────────────────────────────────────────────────────────────────  (Static-Call-Multi)  ✓-ish
                  StaticCall callee args ⇒ MultiValuedExpr [T_1; …; T_n]

  target ⇒ _      callee resolves with inputs [self; Ts] and outputs [T]
  args ⇒ Us      U_i <: T_i (pairwise; self is dropped)
─────────────────────────────────────────────────────────────────────────  (Instance-Call)  ✓-ish
              InstanceCall target callee args ⇒ T


  args ⇐ TBool (each)
──────────────────────────────  (Op-Bool)  ✓-ish    op ∈ {And, Or, AndThen, OrElse, Not, Implies}
 PrimitiveOp op args ⇒ TBool


  args ⇐ Numeric (each)
─────────────────────────────  (Op-Cmp)  ✓-ish      op ∈ {Lt, Leq, Gt, Geq}
 PrimitiveOp op args ⇒ TBool


  lhs ⇒ T_l      rhs ⇒ T_r      T_l <: T_r ∨ T_r <: T_l
──────────────────────────────────────────────────────────  (Op-Eq)  ✓-ish     op ∈ {Eq, Neq}
              PrimitiveOp op [lhs; rhs] ⇒ TBool


  args ⇐ Numeric (each)      args.head ⇒ T
──────────────────────────────────────────  (Op-Arith)  ✓-ish    op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}
       PrimitiveOp op args ⇒ T


  args ⇐ TString (each)                 — current implementation: no operand check
─────────────────────────────  (Op-Concat)  ✓-ish
 PrimitiveOp op args ⇒ TString
```

`Numeric` abbreviates "consistent with one of
{name Strata.Laurel.HighType.TInt}`TInt`, {name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`". Today this is enforced by `checkNumeric`
rather than a `checkStmtExpr` chain; equivalent under the gradual relation.

Op-Arith's "result is the type of the first argument" rule handles `int + int → int`,
`real + real → real`, etc. without a unification step. A consequence: `int + real` is *not*
flagged because each operand individually passes the numeric check. A real fix would be a
numeric-promotion or unification rule; for now this is a known relaxation.

Op-Concat currently performs no operand check; the rule above describes the intended
behavior.

### Object-related and verification forms

```
  ref resolves to a composite or datatype T
─────────────────────────────────────────────  (New-Ok)  ✓     otherwise New ref ⇒ Unknown
            New ref ⇒ UserDefined T


─────────────────  (This)  ✓                   ────────────────────────────  (Abstract / All / ContractOf)  ✓
 This ⇒ Unknown                                 Abstract / All / ContractOf … ⇒ Unknown


  lhs ⇒ _      rhs ⇒ _
─────────────────────────  (RefEq)  ✓               target ⇒ _
 ReferenceEquals lhs rhs ⇒ TBool                ──────────────────  (AsType)  ✓
                                                 AsType target T ⇒ T


  target ⇒ _                                    body ⇒ _
─────────────────  (IsType)  ✓                ──────────────────────────  (Quantifier)  ✓
 IsType target T ⇒ TBool                       Quantifier mode ⟨x, T⟩ trig body ⇒ TBool


   name ⇒ _                          v ⇒ T                        v ⇒ _
─────────────────  (Assigned)  ✓     ────────────  (Old)  ✓       ──────────────  (Fresh)  ✓
 Assigned name ⇒ TBool                Old v ⇒ T                    Fresh v ⇒ TBool


  v ⇒ T      proof ⇒ _                     target ⇒ T_t      newVal ⇒ _
──────────────────────  (ProveBy)  ✓        ─────────────────────────────────  (PureFieldUpdate)  ✓
 ProveBy v proof ⇒ T                         PureFieldUpdate target f newVal ⇒ T_t
```

### Holes

```
                                                                                    Unknown <: T
─────────────────────  (Hole-Some)  ✓        ─────────────────────  (Hole-None-Synth)  ✓     ─────────────────────  (Hole-None-Check)  ✗ (planned)
 Hole d (some T) ⇒ T                          Hole d none ⇒ Unknown                            Hole d none ⇐ T
```

In check mode, `Hole d none ⇐ T` reduces to subsumption today (`Unknown <: T`, which always
holds). The planned bespoke rule would record the inferred `T` on the hole node so
downstream passes can see it, instead of leaving `none` until the hole-inference pass.

## Mutual recursion and termination

`synthStmtExpr` and `checkStmtExpr` are mutually recursive: the synth rule for
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` invokes check-mode resolution for the
condition, and the check function falls back to synth via Sub.

Termination uses a lexicographic measure `(exprMd, tag)` where the tag is `0` for
`synthStmtExpr` and `1` for `checkStmtExpr`. Any descent into a strict subterm decreases
via `Prod.Lex.left` (first component shrinks); Sub calls synth on the *same* expression,
which decreases via `Prod.Lex.right` (second component goes from 1 to 0). This is the
standard well-founded encoding for bidirectional systems where one direction calls the
other on the same input.

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

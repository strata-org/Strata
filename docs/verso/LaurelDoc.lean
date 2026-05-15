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
Γ ⊢ e ⇒ T            -- "e synthesizes T"     (synthStmtExpr)
Γ ⊢ e ⇐ T            -- "e checks against T"  (checkStmtExpr)
```

Synthesis returns a type inferred from the expression itself; checking verifies that the
expression has a given expected type. Each construct picks a mode based on whether its type
is determined locally (synth) or by context (check). The two judgments are connected by a
single change-of-direction rule, *subsumption*:

```
Γ ⊢ e ⇒ A      A <: B
─────────────────────  (Sub)
     Γ ⊢ e ⇐ B
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

Each construct is given as a derivation. `Γ` is the current lexical scope (see
{name Strata.Laurel.ResolveState}`ResolveState`'s `scope`); it threads identically through
every premise and conclusion unless a rule explicitly extends it (written `Γ, x : T`).
`(impl)` = implemented; `(planned)` = intended, not yet wired in.

### Index

- *Subsumption* — Sub
- *Literals* — Lit-Int, Lit-Bool, Lit-String, Lit-Decimal
- *Variables* — Var-Local, Var-Field, Var-Declare
- *Control flow* — If-NoElse, If-Synth, If-Check (planned); Block-Synth, Block-Synth-Empty,
  Block-Check, Block-Check-Empty; Exit; Return-None, Return-Some, Return-Some-Checked
  (planned); While
- *Verification statements* — Assert, Assume
- *Assignment* — Assign-Single, Assign-Multi
- *Calls* — Static-Call, Static-Call-Multi, Instance-Call
- *Primitive operations* — Op-Bool, Op-Cmp, Op-Eq, Op-Arith, Op-Concat
- *Object forms* — New-Ok, New-Fallback; AsType; IsType; RefEq; PureFieldUpdate
- *Verification expressions* — Quantifier, Assigned, Old, Fresh, ProveBy
- *Self reference* — This-Inside, This-Outside
- *Untyped forms* — Abstract / All / ContractOf
- *Holes* — Hole-Some, Hole-None-Synth, Hole-None-Check (planned)

### Subsumption

```
Γ ⊢ e ⇒ A      A <: B
─────────────────────  (Sub, impl)
     Γ ⊢ e ⇐ B
```

Fallback in `checkStmtExpr` whenever no bespoke check rule applies.

### Literals

```
──────────────────────────  (Lit-Int, impl)
 Γ ⊢ LiteralInt n ⇒ TInt
```

```
───────────────────────────  (Lit-Bool, impl)
 Γ ⊢ LiteralBool b ⇒ TBool
```

```
─────────────────────────────────  (Lit-String, impl)
 Γ ⊢ LiteralString s ⇒ TString
```

```
──────────────────────────────────  (Lit-Decimal, impl)
 Γ ⊢ LiteralDecimal d ⇒ TReal
```

### Variables

```
        Γ(x) = T
───────────────────────────  (Var-Local, impl)
 Γ ⊢ Var (.Local x) ⇒ T
```

```
  Γ ⊢ e ⇒ _      Γ(f) = T_f
──────────────────────────────  (Var-Field, impl)
 Γ ⊢ Var (.Field e f) ⇒ T_f
```

Resolution looks `f` up against the type of `e` (or the enclosing instance type for
`self.f`); the typing rule itself is path-agnostic.

```
  x ∉ dom(Γ)
─────────────────────────────────────────  (Var-Declare, impl)
 Γ ⊢ Var (.Declare ⟨x, T⟩) ⇒ TVoid ⊣ Γ, x : T
```

`⊣ Γ, x : T` records that the surrounding `Γ` is extended with the new binding for the
remainder of the enclosing scope.

### Control flow

```
Γ ⊢ cond ⇐ TBool      Γ ⊢ thenBr ⇒ T
─────────────────────────────────────────────  (If-NoElse, impl)
 Γ ⊢ IfThenElse cond thenBr none ⇒ TVoid
```

The construct synthesizes {name Strata.Laurel.HighType.TVoid}`TVoid` because there is no
value when `cond` is false; without this, `x : int := if c then 5` would type-check
spuriously.

```
Γ ⊢ cond ⇐ TBool      Γ ⊢ thenBr ⇒ T_t      Γ ⊢ elseBr ⇒ T_e
──────────────────────────────────────────────────────────────  (If-Synth, impl)
 Γ ⊢ IfThenElse cond thenBr (some elseBr) ⇒ T_t
```

Picks the then-branch type arbitrarily; the two branches are *not* compared, since a
statement-position `if` often pairs a value branch with a `return`/`exit`/`assert`. The
enclosing context's check (Sub, or a containing `checkSubtype` like an assignment) provides
the actual check downstream.

```
Γ ⊢ cond ⇐ TBool      Γ ⊢ thenBr ⇐ T      Γ ⊢ elseBr ⇐ T
──────────────────────────────────────────────────────────  (If-Check, planned)
 Γ ⊢ IfThenElse cond thenBr (some elseBr) ⇐ T
```

```
Γ_0 = Γ      Γ_{i-1} ⊢ s_i ⇒ _ ⊣ Γ_i  (1 ≤ i < n)      Γ_{n-1} ⊢ s_n ⇒ T
───────────────────────────────────────────────────────────────────────────  (Block-Synth, impl)
 Γ ⊢ Block [s_1; …; s_n] label ⇒ T
```

`Γ_{i-1} ⊢ s_i ⇒ _ ⊣ Γ_i` says each statement is resolved in the scope produced by its
predecessor and may itself extend it (`Var (.Declare …)` does); `s_n` is typed in
`Γ_{n-1}`. Bindings introduced inside the block don't escape — `Γ` is what surrounds the
block.

Non-last statements are synthesized but their types discarded (the lax rule). This matches
Java/Python/JS where `f(x);` is normal even when `f` returns a value. The trade-off: `5;`
is silently accepted; flagging it belongs to a lint.

```
─────────────────────────────  (Block-Synth-Empty, impl)
 Γ ⊢ Block [] label ⇒ TVoid
```

```
Γ_0 = Γ      Γ_{i-1} ⊢ s_i ⇒ _ ⊣ Γ_i  (1 ≤ i < n)      Γ_{n-1} ⊢ s_n ⇐ T
───────────────────────────────────────────────────────────────────────────  (Block-Check, impl)
 Γ ⊢ Block [s_1; …; s_n] label ⇐ T
```

Pushes `T` into the *last* statement rather than comparing the block's synthesized type at
the boundary. Errors fire at the offending subexpression, and `T` keeps propagating through
nested {name Strata.Laurel.StmtExpr.Block}`Block` /
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` /
{name Strata.Laurel.StmtExpr.Hole}`Hole` /
{name Strata.Laurel.StmtExpr.Quantifier}`Quantifier`.

```
  TVoid <: T
─────────────────────────  (Block-Check-Empty, impl)
 Γ ⊢ Block [] label ⇐ T
```

```
────────────────────────  (Exit, impl)
 Γ ⊢ Exit target ⇒ TVoid
```

```
─────────────────────────────  (Return-None, impl)
 Γ ⊢ Return none ⇒ TVoid
```

```
      Γ ⊢ e ⇒ _
──────────────────────────────  (Return-Some, impl)
 Γ ⊢ Return (some e) ⇒ TVoid
```

The value's synthesized type is currently discarded, so `return 0` in a `bool`-returning
procedure isn't caught. Replaced by Return-Some-Checked once the expected return type is
threaded through {name Strata.Laurel.ResolveState}`ResolveState`.

```
  Γ_proc.outputs = [T]      Γ ⊢ e ⇐ T
──────────────────────────────────────  (Return-Some-Checked, planned)
       Γ ⊢ Return (some e) ⇒ TVoid
```

Set from `proc.outputs` in {name Strata.Laurel.resolveProcedure}`resolveProcedure` /
{name Strata.Laurel.resolveInstanceProcedure}`resolveInstanceProcedure`.

```
  Γ ⊢ cond ⇐ TBool      Γ ⊢ invs_i ⇐ TBool      Γ ⊢ dec ⇐ ?      Γ ⊢ body ⇒ _
───────────────────────────────────────────────────────────────────────────────  (While, impl)
                  Γ ⊢ While cond invs dec body ⇒ TVoid
```

`dec` (the optional decreases clause) is resolved without a type check today; the intended
target is a numeric type.

### Verification statements

```
       Γ ⊢ cond ⇐ TBool
──────────────────────────────  (Assert, impl)
   Γ ⊢ Assert cond ⇒ TVoid
```

```
      Γ ⊢ cond ⇐ TBool
─────────────────────────────  (Assume, impl)
 Γ ⊢ Assume cond ⇒ TVoid
```

### Assignment

```
  Γ(x) = T_x      Γ ⊢ e ⇒ T_e      T_e <: T_x
───────────────────────────────────────────────  (Assign-Single, impl)
            Γ ⊢ Assign [x] e ⇒ TVoid
```

```
  Γ ⊢ targets_i = x_i      Γ(x_i) = T_i      Γ ⊢ e ⇒ MultiValuedExpr Us      |Ts| = |Us|      U_i <: T_i
─────────────────────────────────────────────────────────────────────────────────────────────────────────  (Assign-Multi, impl)
                                  Γ ⊢ Assign targets e ⇒ TVoid
```

### Calls

```
  Γ(callee) = static-procedure with inputs Ts and outputs [T]
  Γ ⊢ args ⇒ Us      U_i <: T_i (pairwise)
─────────────────────────────────────────────────────────────  (Static-Call, impl)
              Γ ⊢ StaticCall callee args ⇒ T
```

```
  Γ(callee) = static-procedure with inputs Ts and outputs [T_1; …; T_n], n ≠ 1
  Γ ⊢ args ⇒ Us      U_i <: T_i (pairwise)
──────────────────────────────────────────────────────────────────────────────────  (Static-Call-Multi, impl)
       Γ ⊢ StaticCall callee args ⇒ MultiValuedExpr [T_1; …; T_n]
```

```
  Γ ⊢ target ⇒ _      Γ(callee) = instance-procedure with inputs [self; Ts] and outputs [T]
  Γ ⊢ args ⇒ Us      U_i <: T_i (pairwise; self is dropped)
─────────────────────────────────────────────────────────────────────────────────────────────  (Instance-Call, impl)
                       Γ ⊢ InstanceCall target callee args ⇒ T
```

### Primitive operations

`Numeric` abbreviates "consistent with one of {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`".

```
  Γ ⊢ args_i ⇐ TBool                              op ∈ {And, Or, AndThen, OrElse, Not, Implies}
──────────────────────────────────  (Op-Bool, impl)
 Γ ⊢ PrimitiveOp op args ⇒ TBool
```

```
  Γ ⊢ args_i ⇐ Numeric                            op ∈ {Lt, Leq, Gt, Geq}
─────────────────────────────────  (Op-Cmp, impl)
 Γ ⊢ PrimitiveOp op args ⇒ TBool
```

```
  Γ ⊢ lhs ⇒ T_l      Γ ⊢ rhs ⇒ T_r      T_l <: T_r ∨ T_r <: T_l                op ∈ {Eq, Neq}
─────────────────────────────────────────────────────────────────  (Op-Eq, impl)
            Γ ⊢ PrimitiveOp op [lhs; rhs] ⇒ TBool
```

```
  Γ ⊢ args_i ⇐ Numeric      Γ ⊢ args.head ⇒ T                op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}
──────────────────────────────────────────────────  (Op-Arith, impl)
            Γ ⊢ PrimitiveOp op args ⇒ T
```

"Result is the type of the first argument" handles `int + int → int`, `real + real → real`,
etc. without unification. Known relaxation: `int + real` passes (each operand individually
passes `Numeric`); a proper fix needs numeric promotion or unification.

```
  Γ ⊢ args_i ⇐ TString                            op = StrConcat
─────────────────────────────────────  (Op-Concat, impl)
 Γ ⊢ PrimitiveOp op args ⇒ TString
```

### Object forms

```
  Γ(ref) is a composite or datatype T
──────────────────────────────────────────  (New-Ok, impl)
       Γ ⊢ New ref ⇒ UserDefined T
```

```
  Γ(ref) is not a composite or datatype
─────────────────────────────────────────  (New-Fallback, impl)
        Γ ⊢ New ref ⇒ Unknown
```

```
      Γ ⊢ target ⇒ _
─────────────────────────────  (AsType, impl)
 Γ ⊢ AsType target T ⇒ T
```

`target` is resolved but not checked against `T` — the cast is the user's claim.

```
       Γ ⊢ target ⇒ _
─────────────────────────────────  (IsType, impl)
 Γ ⊢ IsType target T ⇒ TBool
```

```
  Γ ⊢ lhs ⇒ T_l      Γ ⊢ rhs ⇒ T_r      isReference T_l      isReference T_r
─────────────────────────────────────────────────────────────────────────────  (RefEq, impl)
                       Γ ⊢ ReferenceEquals lhs rhs ⇒ TBool
```

`isReference T` holds when `T` is a {name Strata.Laurel.HighType.UserDefined}`UserDefined`,
{name Strata.Laurel.HighType.Unknown}`Unknown`, or {name Strata.Laurel.HighType.TCore}`TCore`
type. Reference equality is meaningless on primitives. Compatibility between `T_l` and
`T_r` (e.g. rejecting `Cat === Dog` for unrelated user-defined types) is delegated to
future tightening of `<:` — today, two distinct user-defined names already mismatch
structurally, so the check would only fire under stronger subtyping.

```
   Γ ⊢ target ⇒ T_t      Γ(f) = T_f      Γ ⊢ newVal ⇐ T_f
─────────────────────────────────────────────────────────────  (PureFieldUpdate, impl)
       Γ ⊢ PureFieldUpdate target f newVal ⇒ T_t
```

`f` is resolved against `T_t` (or the enclosing instance type) and `newVal` is checked
against the field's declared type.

### Verification expressions

```
  Γ, x : T ⊢ body ⇐ TBool
─────────────────────────────────────────────────  (Quantifier, impl)
 Γ ⊢ Quantifier mode ⟨x, T⟩ trig body ⇒ TBool
```

The bound variable `x : T` is introduced in scope only for the body (and trigger). The body
is checked against {name Strata.Laurel.HighType.TBool}`TBool` since a quantifier is a
proposition; without this, `forall x: int :: x + 1` would be silently accepted.

```
       Γ ⊢ name ⇒ _
─────────────────────────────  (Assigned, impl)
 Γ ⊢ Assigned name ⇒ TBool
```

```
   Γ ⊢ v ⇒ T
─────────────────  (Old, impl)
 Γ ⊢ Old v ⇒ T
```

```
  Γ ⊢ v ⇒ T      isReference T
─────────────────────────────────  (Fresh, impl)
       Γ ⊢ Fresh v ⇒ TBool
```

`isReference T` is the same predicate as in {name Strata.Laurel.StmtExpr.ReferenceEquals}`ReferenceEquals`.
{name Strata.Laurel.StmtExpr.Fresh}`Fresh` only makes sense on heap-allocated references;
`fresh(5)` is rejected.

```
   Γ ⊢ v ⇒ T      Γ ⊢ proof ⇒ _
───────────────────────────────────  (ProveBy, impl)
       Γ ⊢ ProveBy v proof ⇒ T
```

### Self reference

```
  Γ.instanceTypeName = some T
──────────────────────────────────  (This-Inside, impl)
 Γ ⊢ This ⇒ UserDefined T


  Γ.instanceTypeName = none
──────────────────────────────  (This-Outside, impl)
   Γ ⊢ This ⇒ Unknown    [emits "'this' is not allowed outside instance methods"]
```

`Γ.instanceTypeName` is the
{name Strata.Laurel.ResolveState}`ResolveState` field set by
{name Strata.Laurel.resolveInstanceProcedure}`resolveInstanceProcedure` for the duration of
an instance method body. With it, `this.field` and instance-method dispatch synthesize real
types instead of being wildcarded through {name Strata.Laurel.HighType.Unknown}`Unknown`.

### Untyped forms

```
─────────────────────────────────────────────  (Abstract / All / ContractOf, impl)
 Γ ⊢ Abstract / All / ContractOf … ⇒ Unknown
```

### Holes

```
────────────────────────────  (Hole-Some, impl)
 Γ ⊢ Hole d (some T) ⇒ T
```

```
─────────────────────────────────  (Hole-None-Synth, impl)
   Γ ⊢ Hole d none ⇒ Unknown
```

```
       Unknown <: T
─────────────────────────  (Hole-None-Check, planned)
 Γ ⊢ Hole d none ⇐ T
```

In check mode today, `Hole d none ⇐ T` reduces to subsumption (`Unknown <: T`, which always
holds). The planned rule would record the inferred `T` on the hole node so downstream
passes can see it, instead of leaving `none` until the hole-inference pass.

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

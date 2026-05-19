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

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

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
`synthStmtExpr` via \[⇐\] Sub. Termination uses a lexicographic measure `(exprMd, tag)`
where the tag is `0` for synth and `1` for check; any descent into a strict subterm
decreases via `Prod.Lex.left`, while \[⇐\] Sub calls synth on the *same* expression and
decreases via
`Prod.Lex.right`. This is the standard well-founded encoding for bidirectional systems.

There is also a thin `resolveStmtExpr` wrapper that calls `synthStmtExpr` and discards the
synthesized type. It's used at sites where typing is not enforced (verification annotations,
modifies/reads clauses). The right principle for new call sites is: when the position has a
known expected type ({name Strata.Laurel.HighType.TBool}`TBool` for conditions, numeric for
`decreases`, the declared output for a constant initializer or a functional body), use
`checkStmtExpr`. When it doesn't, use `resolveStmtExpr`. `synthStmtExpr` itself is mostly an
internal interface used by other rules.

### Gradual typing

The relation `<:` (used in \[⇐\] Sub) is built from three Lean functions:

- `isSubtype` — pure subtyping. Walks the `extending` chain for
  {name Strata.Laurel.CompositeType}`CompositeType` (via
  {name Strata.Laurel.TypeContext.ancestors}`TypeContext.ancestors`), unfolds
  {name Strata.Laurel.TypeAlias}`TypeAlias` to its target, and unwraps
  {name Strata.Laurel.ConstrainedType}`ConstrainedType` to its base (both via
  {name Strata.Laurel.TypeContext.unfold}`TypeContext.unfold`), then falls back to
  structural equality via {name Strata.Laurel.highEq}`highEq`.
- `isConsistent` — the symmetric gradual relation `~` (Siek–Taha):
  {name Strata.Laurel.HighType.Unknown}`Unknown` is the dynamic type and is consistent with
  everything; otherwise structural equality.
- `isConsistentSubtype` — defined as `isConsistent ∨ isSubtype`. For our flat lattice this
  is the standard collapse of `∃R. T ~ R ∧ R <: U`.

\[⇐\] Sub (and every bespoke check rule) uses `isConsistentSubtype`. That single choice is what
makes the system *gradual*: an expression of type
{name Strata.Laurel.HighType.Unknown}`Unknown` (a hole, an unresolved name, a `Hole _ none`)
flows freely into any typed slot, and any expression flows freely into a slot of type
{name Strata.Laurel.HighType.Unknown}`Unknown`. Strict checking is applied between
fully-known types only. The symmetric `isConsistent` is used directly by \[⇒\] Op-Eq, where
the operand types must be mutually consistent (no subtype direction is privileged).

A previous iteration was synth-only with two *bivariantly-compatible* wildcards:
{name Strata.Laurel.HighType.Unknown}`Unknown` and
{name Strata.Laurel.HighType.UserDefined}`UserDefined`. The
{name Strata.Laurel.HighType.UserDefined}`UserDefined` carve-out was load-bearing: no
assignment, call argument, or comparison involving a user type was ever rejected. The
bidirectional design retires that carve-out — user-defined types are now a regular
participant in `<:`, with `isSubtype` walking inheritance chains and unwrapping aliases
and constrained types to deliver real checking on user-defined code.

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

Each rule is tagged with `[⇒]` (synthesis) or `[⇐]` (checking) to make the
direction explicit. When a construct has both modes, the `-Synth` / `-Check`
suffix is dropped in favor of the prefix.

### Index

- *Subsumption* — \[⇐\] Sub
- *Literals* — \[⇒\] Lit-Int, \[⇒\] Lit-Bool, \[⇒\] Lit-String, \[⇒\] Lit-Decimal
- *Variables* — \[⇒\] Var-Local, \[⇒\] Var-Field, \[⇒\] Var-Declare
- *Control flow* — \[⇒\] If-NoElse, \[⇒\] If, \[⇐\] If, \[⇐\] If-NoElse;
  \[⇒\] Block, \[⇒\] Block-Empty, \[⇐\] Block, \[⇐\] Block-Empty; \[⇒\] Exit;
  \[⇒\] Return-None, \[⇒\] Return-Some, \[⇒\] Return-Void-Error,
  \[⇒\] Return-Multi-Error; \[⇒\] While
- *Verification statements* — \[⇒\] Assert, \[⇒\] Assume
- *Assignment* — \[⇒\] Assign
- *Calls* — \[⇒\] Static-Call, \[⇒\] Static-Call-Multi, \[⇒\] Instance-Call
- *Primitive operations* — \[⇒\] Op-Bool, \[⇒\] Op-Cmp, \[⇒\] Op-Eq, \[⇒\] Op-Arith,
  \[⇒\] Op-Concat
- *Object forms* — \[⇒\] New-Ok, \[⇒\] New-Fallback; \[⇒\] AsType; \[⇒\] IsType;
  \[⇒\] RefEq; \[⇒\] PureFieldUpdate
- *Verification expressions* — \[⇒\] Quantifier, \[⇒\] Assigned, \[⇒\] Old,
  \[⇒\] Fresh, \[⇒\] ProveBy
- *Self reference* — \[⇒\] This-Inside, \[⇒\] This-Outside
- *Untyped forms* — \[⇒\] Abstract / All
- *ContractOf* — \[⇒\] ContractOf-Bool, \[⇒\] ContractOf-Set, \[⇒\] ContractOf-Error
- *Holes* — \[⇒\] Hole-Some, \[⇒\] Hole-None, \[⇐\] Hole-None

### Subsumption

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

Fallback in `checkStmtExpr` whenever no bespoke check rule applies.

### Literals

$$`\frac{}{\Gamma \vdash \mathsf{LiteralInt}\;n \Rightarrow \mathsf{TInt}} \quad \text{([⇒] Lit-Int)}`

$$`\frac{}{\Gamma \vdash \mathsf{LiteralBool}\;b \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Lit-Bool)}`

$$`\frac{}{\Gamma \vdash \mathsf{LiteralString}\;s \Rightarrow \mathsf{TString}} \quad \text{([⇒] Lit-String)}`

$$`\frac{}{\Gamma \vdash \mathsf{LiteralDecimal}\;d \Rightarrow \mathsf{TReal}} \quad \text{([⇒] Lit-Decimal)}`

### Variables

$$`\frac{\Gamma(x) = T}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Local}\;x) \Rightarrow T} \quad \text{([⇒] Var-Local)}`

$$`\frac{\Gamma \vdash e \Rightarrow \_ \quad \Gamma(f) = T_f}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Field}\;e\;f) \Rightarrow T_f} \quad \text{([⇒] Var-Field)}`

Resolution looks `f` up against the type of `e` (or the enclosing instance type for
`self.f`); the typing rule itself is path-agnostic.

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, T\rangle) \Rightarrow \mathsf{TVoid} \dashv \Gamma, x : T} \quad \text{([⇒] Var-Declare)}`

`⊣ Γ, x : T` records that the surrounding `Γ` is extended with the new binding for the
remainder of the enclosing scope.

### Control flow

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow \mathsf{TVoid}}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] If-NoElse)}`

The construct synthesizes {name Strata.Laurel.HighType.TVoid}`TVoid` because there is no
value when `cond` is false; the then-branch is checked against
{name Strata.Laurel.HighType.TVoid}`TVoid` so `x : int := if c then 5` is rejected at the
branch rather than slipping through to a downstream subsumption.

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow T_t \quad \Gamma \vdash \mathit{elseBr} \Rightarrow T_e}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Rightarrow T_t \sqcup T_e} \quad \text{([⇒] If)}`

The result is the join (least upper bound) of the two branch types, so
`if c then small else big` synthesizes the common supertype rather than committing to one
branch arbitrarily. The join walks `extending` chains for composites; when no common
supertype exists (e.g. a value branch paired with a `TVoid` `return`/`exit`), it falls
back to `T_t` and the enclosing context's check (\[⇐\] Sub, or a containing
`checkSubtype` like an assignment) surfaces any mismatch downstream against the
then-branch's type.

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \Gamma \vdash \mathit{elseBr} \Leftarrow T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Leftarrow T} \quad \text{([⇐] If)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \mathsf{TVoid} <: T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Leftarrow T} \quad \text{([⇐] If-NoElse)}`

Check mode pushes `T` into both branches (rather than going through \[⇒\] If + \[⇐\] Sub at
the boundary). Errors fire at the offending branch instead of the surrounding `if`.
Without an else branch, the construct can only succeed when `T` admits
{name Strata.Laurel.HighType.TVoid}`TVoid` — the same subsumption check `\[⇐\] Block-Empty`
performs for an empty block.

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \Rightarrow \_ \dashv \Gamma_i \;(1 \le i < n) \quad \Gamma_{n-1} \vdash s_n \Rightarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n]\;\mathit{label} \Rightarrow T} \quad \text{([⇒] Block)}`

`Γ_{i-1} ⊢ s_i ⇒ _ ⊣ Γ_i` says each statement is resolved in the scope produced by its
predecessor and may itself extend it (`Var (.Declare …)` does); `s_n` is typed in
`Γ_{n-1}`. Bindings introduced inside the block don't escape — `Γ` is what surrounds the
block.

Non-last statements are synthesized but their types discarded (the lax rule). This matches
Java/Python/JS where `f(x);` is normal even when `f` returns a value. The trade-off: `5;`
is silently accepted; flagging it belongs to a lint.

$$`\frac{}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Block-Empty)}`

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \Rightarrow \_ \dashv \Gamma_i \;(1 \le i < n) \quad \Gamma_{n-1} \vdash s_n \Leftarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block)}`

Pushes `T` into the *last* statement rather than comparing the block's synthesized type at
the boundary. Errors fire at the offending subexpression, and `T` keeps propagating through
nested {name Strata.Laurel.StmtExpr.Block}`Block` /
{name Strata.Laurel.StmtExpr.IfThenElse}`IfThenElse` /
{name Strata.Laurel.StmtExpr.Hole}`Hole` /
{name Strata.Laurel.StmtExpr.Quantifier}`Quantifier`.

$$`\frac{\mathsf{TVoid} <: T}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block-Empty)}`

$$`\frac{}{\Gamma \vdash \mathsf{Exit}\;\mathit{target} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Exit)}`

`Return` matches the optional return value against the enclosing procedure's declared
outputs. The expected output types are threaded through
{name Strata.Laurel.ResolveState}`ResolveState`'s `expectedReturnTypes`, set from
`proc.outputs` by {name Strata.Laurel.resolveProcedure}`resolveProcedure` /
{name Strata.Laurel.resolveInstanceProcedure}`resolveInstanceProcedure` for the duration of
the body. `none` means "no enclosing procedure" — e.g. resolving a constant initializer —
and skips all `Return` checks.

$$`\frac{}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None)}`

A bare `return;` is allowed in any context. In a single-output procedure it acts as a
Dafny-style early exit — the output parameter retains whatever was last assigned to it.

$$`\frac{\Gamma_{\mathit{proc}}.\mathit{outputs} = [T] \quad \Gamma \vdash e \Leftarrow T}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-Some)}`

In a single-output procedure, the value is checked against the declared output type. This
closes the prior soundness gap where `return 0` in a `bool`-returning procedure went
uncaught.

$$`\frac{\Gamma_{\mathit{proc}}.\mathit{outputs} = []}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “void procedure cannot return a value”}} \quad \text{([⇒] Return-Void-Error)}`

$$`\frac{\Gamma_{\mathit{proc}}.\mathit{outputs} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “multi-output procedure cannot use ‘return e’; assign to named outputs instead”}} \quad \text{([⇒] Return-Multi-Error)}`

Multi-output procedures use named-output assignment (`r := …` on the declared output
parameters). `return e` syntactically takes a single
{name Strata.Laurel.StmtExpr.Return}`Option StmtExpr`, so it cannot carry multiple values;
flagging it points users at the named-output convention.

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{invs}_i \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{dec} \Leftarrow {?} \quad \Gamma \vdash \mathit{body} \Rightarrow \_}{\Gamma \vdash \mathsf{While}\;\mathit{cond}\;\mathit{invs}\;\mathit{dec}\;\mathit{body} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] While)}`

`dec` (the optional decreases clause) is resolved without a type check today; the intended
target is a numeric type.

### Verification statements

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assert}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assert)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assume}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assume)}`

### Assignment

$$`\frac{\Gamma \vdash \mathit{targets}_i \Rightarrow T_i \quad \Gamma \vdash e \Rightarrow T_e \quad T_e <: \mathit{ExpectedTy}}{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assign)}`

where `ExpectedTy = T_1` if `|targets| = 1` and `MultiValuedExpr [T_1; …; T_n]` otherwise.

The target's declared type `T_i` comes from the variable's scope entry (for
{name Strata.Laurel.Variable.Local}`Local` and {name Strata.Laurel.Variable.Field}`Field`)
or from the {name Strata.Laurel.Variable.Declare}`Declare`-bound parameter type. Both
single- and multi-target forms collapse into one tuple-vs-tuple check: when the RHS is a
{name Strata.Laurel.HighType.MultiValuedExpr}`MultiValuedExpr`, both arity and per-position
type mismatches surface in a single diagnostic of shape *"expected '(int, int, int)', got
'(int, string)'"*. When the RHS is {name Strata.Laurel.HighType.TVoid}`TVoid` (a
side-effecting statement: `while`, `return`, …), all checks are skipped — there's no value
to assign.

### Calls

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T] \quad \Gamma \vdash \mathit{args} \Rightarrow Us \quad U_i <: T_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Static-Call)}`

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T_1; \ldots; T_n],\; n \ne 1 \quad \Gamma \vdash \mathit{args} \Rightarrow Us \quad U_i <: T_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Static-Call-Multi)}`

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance-procedure with inputs } [\mathit{self}; Ts] \text{ and outputs } [T] \quad \Gamma \vdash \mathit{args} \Rightarrow Us \quad U_i <: T_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Instance-Call)}`

### Primitive operations

`Numeric` abbreviates "consistent with one of {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`".

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathsf{TBool} \quad \mathit{op} \in \{\mathsf{And}, \mathsf{Or}, \mathsf{AndThen}, \mathsf{OrElse}, \mathsf{Not}, \mathsf{Implies}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Bool)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathit{Numeric} \quad \mathit{op} \in \{\mathsf{Lt}, \mathsf{Leq}, \mathsf{Gt}, \mathsf{Geq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Cmp)}`

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad T_l \sim T_r \quad \mathit{op} \in \{\mathsf{Eq}, \mathsf{Neq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;[\mathit{lhs}; \mathit{rhs}] \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Eq)}`

`~` is the consistency relation `isConsistent` — symmetric, with the
{name Strata.Laurel.HighType.Unknown}`Unknown` wildcard.

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathit{Numeric} \quad \Gamma \vdash \mathit{args}.\mathsf{head} \Rightarrow T \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Op-Arith)}`

"Result is the type of the first argument" handles `int + int → int`, `real + real → real`,
etc. without unification. Known relaxation: `int + real` passes (each operand individually
passes `Numeric`); a proper fix needs numeric promotion or unification.

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathsf{TString} \quad \mathit{op} = \mathsf{StrConcat}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TString}} \quad \text{([⇒] Op-Concat)}`

### Object forms

$$`\frac{\Gamma(\mathit{ref}) \text{ is a composite or datatype } T}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{UserDefined}\;T} \quad \text{([⇒] New-Ok)}`

$$`\frac{\Gamma(\mathit{ref}) \text{ is not a composite or datatype}}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] New-Fallback)}`

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_}{\Gamma \vdash \mathsf{AsType}\;\mathit{target}\;T \Rightarrow T} \quad \text{([⇒] AsType)}`

`target` is resolved but not checked against `T` — the cast is the user's claim.

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_}{\Gamma \vdash \mathsf{IsType}\;\mathit{target}\;T \Rightarrow \mathsf{TBool}} \quad \text{([⇒] IsType)}`

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad \mathsf{isReference}\;T_l \quad \mathsf{isReference}\;T_r \quad T_l \sim T_r}{\Gamma \vdash \mathsf{ReferenceEquals}\;\mathit{lhs}\;\mathit{rhs} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] RefEq)}`

`isReference T` holds when `T` is a {name Strata.Laurel.HighType.UserDefined}`UserDefined`
or {name Strata.Laurel.HighType.Unknown}`Unknown`
type. Reference equality is meaningless on primitives. The operands must also be
consistent under `~` (Siek–Taha consistency), matching the rule applied by
{name Strata.Laurel.Operation.Eq}`==`: two distinct user-defined types like `Cat` and
`Dog` are rejected, while either side being `Unknown` is accepted as a gradual escape
hatch.

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T_t \quad \Gamma(f) = T_f \quad \Gamma \vdash \mathit{newVal} \Leftarrow T_f}{\Gamma \vdash \mathsf{PureFieldUpdate}\;\mathit{target}\;f\;\mathit{newVal} \Rightarrow T_t} \quad \text{([⇒] PureFieldUpdate)}`

`f` is resolved against `T_t` (or the enclosing instance type) and `newVal` is checked
against the field's declared type.

### Verification expressions

$$`\frac{\Gamma, x : T \vdash \mathit{body} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Quantifier}\;\mathit{mode}\;\langle x, T\rangle\;\mathit{trig}\;\mathit{body} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Quantifier)}`

The bound variable `x : T` is introduced in scope only for the body (and trigger). The body
is checked against {name Strata.Laurel.HighType.TBool}`TBool` since a quantifier is a
proposition; without this, `forall x: int :: x + 1` would be silently accepted.

$$`\frac{\Gamma \vdash \mathit{name} \Rightarrow \_}{\Gamma \vdash \mathsf{Assigned}\;\mathit{name} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Assigned)}`

$$`\frac{\Gamma \vdash v \Rightarrow T}{\Gamma \vdash \mathsf{Old}\;v \Rightarrow T} \quad \text{([⇒] Old)}`

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \mathsf{isReference}\;T}{\Gamma \vdash \mathsf{Fresh}\;v \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Fresh)}`

`isReference T` is the same predicate as in {name Strata.Laurel.StmtExpr.ReferenceEquals}`ReferenceEquals`.
{name Strata.Laurel.StmtExpr.Fresh}`Fresh` only makes sense on heap-allocated references;
`fresh(5)` is rejected.

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \Gamma \vdash \mathit{proof} \Rightarrow \_}{\Gamma \vdash \mathsf{ProveBy}\;v\;\mathit{proof} \Rightarrow T} \quad \text{([⇒] ProveBy)}`

### Self reference

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{some}\;T}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{UserDefined}\;T} \quad \text{([⇒] This-Inside)}`

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{none}}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{Unknown}\;\;[\text{emits “‘this’ is not allowed outside instance methods”}]} \quad \text{([⇒] This-Outside)}`

`Γ.instanceTypeName` is the
{name Strata.Laurel.ResolveState}`ResolveState` field set by
{name Strata.Laurel.resolveInstanceProcedure}`resolveInstanceProcedure` for the duration of
an instance method body. With it, `this.field` and instance-method dispatch synthesize real
types instead of being wildcarded through {name Strata.Laurel.HighType.Unknown}`Unknown`.

### Untyped forms

$$`\frac{}{\Gamma \vdash \mathsf{Abstract}\;/\;\mathsf{All}\;\ldots \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Abstract / All)}`

### ContractOf

`ContractOf ty fn` extracts a procedure's contract clause as a value: its preconditions
(`Precondition`), postconditions (`PostCondition`), reads set (`Reads`), or modifies set
(`Modifies`). `fn` must be a direct identifier reference to a procedure — a contract belongs
to a *named* procedure, not an arbitrary expression.

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Precondition}\;\mathit{fn} \Rightarrow \mathsf{TBool} \quad\quad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{PostCondition}\;\mathit{fn} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] ContractOf-Bool)}`

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Reads}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown} \quad\quad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{Modifies}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown}} \quad \text{([⇒] ContractOf-Set)}`

`Precondition` and `PostCondition` are propositions, hence
{name Strata.Laurel.HighType.TBool}`TBool`. `Reads` and `Modifies` are sets of heap-allocated
locations — composite/datatype references and fields. The element type is left as
{name Strata.Laurel.HighType.Unknown}`Unknown` for now since the rule doesn't yet recover it
from `fn`'s declared modifies/reads clauses.

$$`\frac{\mathit{fn} \text{ is not a procedure reference}}{\Gamma \vdash \mathsf{ContractOf}\;\ldots\;\mathit{fn} \rightsquigarrow \text{error: “‘contractOf’ expected a procedure reference”}} \quad \text{([⇒] ContractOf-Error)}`

When `fn` doesn't resolve to a procedure (e.g. it's an arbitrary expression, or resolves to
a constant/variable), the diagnostic fires and the construct synthesizes
{name Strata.Laurel.HighType.Unknown}`Unknown` to suppress cascading errors.

The constructor is reserved for future use — Laurel's grammar has no `contractOf`
production today, and the translator emits "not yet implemented" for it. The typing rule
exists so resolution remains exhaustive over `StmtExpr`.

### Holes

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;(\mathsf{some}\;T) \Rightarrow T} \quad \text{([⇒] Hole-Some)}`

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Hole-None)}`

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Leftarrow T \;\;\mapsto\;\; \mathsf{Hole}\;d\;(\mathsf{some}\;T)} \quad \text{([⇐] Hole-None)}`

In check mode, an untyped hole records the expected type `T` on the node directly. The
subsumption check is trivial (`Unknown <: T` always holds), so this rule never fails — it
just preserves the type information that's available at the check-mode boundary instead of
discarding it.

A separate `InferHoleTypes` pass still runs after resolution to annotate holes that ended
up in synth-only positions. When that pass encounters a hole whose type was already set
(by \[⇐\] Hole-None or by a user-written `?: T`), it checks the resolution-time and
inference-time types for consistency under `~`; a disagreement fires the diagnostic
*"hole annotated with 'T_resolution' but context expects 'T_inference'"*, surfacing what
would otherwise be a silent overwrite.

## Future structural changes

The current pipeline has resolution and several downstream passes that recompute or
re-derive type information that resolution already synthesized. A few cleanups worth
considering:

### Rename `Resolution.lean` → `NameTypeResolution.lean`

The pass resolves names *and* type-checks expressions in one walk; the file name only
advertises the first half. A rename (e.g. `NameTypeResolution.lean` or
`ResolutionAndTyping.lean`) would describe what the pass actually does. The
`SemanticModel` and `ResolvedNode` types could keep their names — they're about resolved
references, not typing.

### Eliminate `LaurelTypes.computeExprType` by caching types

`LaurelTypes.lean` exports `computeExprType : SemanticModel → StmtExprMd → HighTypeMd`,
which five later passes call (`LaurelToCoreTranslator`, `ModifiesClauses`,
`LiftImperativeExpressions`, `HeapParameterization`, `TypeHierarchy`) to ask "what's the
type of this expression?" after resolution. Resolution already synthesizes the same types
during its walk, then discards them. Two ways to remove the duplication:

- *Cache types on the AST.* Add a `HighTypeMd` field to `StmtExpr` (or a parallel
  `Std.HashMap Nat HighTypeMd` keyed by node-id, attached to `SemanticModel`), populate it
  during resolution, and have later passes read it. `computeExprType` becomes a lookup,
  not a re-traversal.
- *Make the cache opt-in.* Same idea, but only enable the type-cache for passes that need
  it. Less invasive but partially defeats the point.

The duplication isn't a correctness issue today (both paths produce consistent results),
just wasted work and a maintenance hazard.

### Shrink or remove `InferHoleTypes`

`InferHoleTypes` walks the post-resolution AST a second time to annotate holes. Now that
\[⇐\] Hole-None writes the expected type during resolution for holes in check-mode
positions, the post-pass only needs to handle holes in synth-only positions (e.g. call
arguments resolved through `synthStmtExpr` instead of `checkStmtExpr`). As more constructs
gain bespoke check rules, fewer holes will reach `InferHoleTypes`; eventually the pass
can be deleted entirely.

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

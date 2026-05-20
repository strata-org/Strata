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
Γ ⊢ e ⇒ T            -- "e synthesizes T"     (Synth.resolveStmtExpr)
Γ ⊢ e ⇐ T            -- "e checks against T"  (Check.resolveStmtExpr)
```

Synthesis returns a type inferred from the expression itself; checking verifies that the
expression has a given expected type. Each construct picks a mode based on whether its
type is determined locally (synth) or by context (check). The two judgments are connected
by a single change-of-direction rule, *subsumption*:

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

The two judgments are implemented as
{name Strata.Laurel.Resolution.Synth.resolveStmtExpr}`Synth.resolveStmtExpr` and
{name Strata.Laurel.Resolution.Check.resolveStmtExpr}`Check.resolveStmtExpr`:

{docstring Strata.Laurel.Resolution.Synth.resolveStmtExpr}

{docstring Strata.Laurel.Resolution.Check.resolveStmtExpr}

### Gradual typing

The relation `<:` (used in \[⇐\] Sub) is built from three Lean functions —
{name Strata.Laurel.isSubtype}`isSubtype`, {name Strata.Laurel.isConsistent}`isConsistent`,
and {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`:

{docstring Strata.Laurel.isSubtype}

{docstring Strata.Laurel.isConsistent}

{docstring Strata.Laurel.isConsistentSubtype}

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
direction explicit.

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

Fallback in {name Strata.Laurel.Resolution.Check.resolveStmtExpr}`Check.resolveStmtExpr` whenever no bespoke check
rule applies.

### Literals

$$`\frac{}{\Gamma \vdash \mathsf{LiteralInt}\;n \Rightarrow \mathsf{TInt}} \quad \text{([⇒] Lit-Int)}`

{docstring Strata.Laurel.Resolution.Synth.litInt}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralBool}\;b \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Lit-Bool)}`

{docstring Strata.Laurel.Resolution.Synth.litBool}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralString}\;s \Rightarrow \mathsf{TString}} \quad \text{([⇒] Lit-String)}`

{docstring Strata.Laurel.Resolution.Synth.litString}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralDecimal}\;d \Rightarrow \mathsf{TReal}} \quad \text{([⇒] Lit-Decimal)}`

{docstring Strata.Laurel.Resolution.Synth.litDecimal}

### Variables

$$`\frac{\Gamma(x) = T}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Local}\;x) \Rightarrow T} \quad \text{([⇒] Var-Local)}`

{docstring Strata.Laurel.Resolution.Synth.varLocal}

$$`\frac{\Gamma \vdash e \Rightarrow \_ \quad \Gamma(f) = T_f}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Field}\;e\;f) \Rightarrow T_f} \quad \text{([⇒] Var-Field)}`

{docstring Strata.Laurel.Resolution.Synth.varField}

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, T\rangle) \Rightarrow \mathsf{TVoid} \dashv \Gamma, x : T} \quad \text{([⇒] Var-Declare)}`

{docstring Strata.Laurel.Resolution.Synth.varDeclare}

### Control flow

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow \mathsf{TVoid}}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] If-NoElse)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow T_t \quad \Gamma \vdash \mathit{elseBr} \Rightarrow T_e}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Rightarrow T_t \sqcup T_e} \quad \text{([⇒] If)}`

{docstring Strata.Laurel.Resolution.Synth.ifThenElse}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \Gamma \vdash \mathit{elseBr} \Leftarrow T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Leftarrow T} \quad \text{([⇐] If)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \mathsf{TVoid} <: T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Leftarrow T} \quad \text{([⇐] If-NoElse)}`

{docstring Strata.Laurel.Resolution.Check.ifThenElse}

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \Rightarrow \_ \dashv \Gamma_i \;(1 \le i < n) \quad \Gamma_{n-1} \vdash s_n \Rightarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n]\;\mathit{label} \Rightarrow T} \quad \text{([⇒] Block)}`

Reading the premise: $`\Gamma_{i-1} \vdash s_i \Rightarrow \_ \dashv \Gamma_i` means $`s_i`
is resolved under the scope $`\Gamma_{i-1}` produced by its predecessor, synthesizes some
type (the `_` discards it — non-last statements are sequenced for effect, not value), and
produces a possibly extended scope $`\Gamma_i` that the next statement sees. In practice
only `Var (.Declare …)` actually extends the scope; every other construct leaves it
unchanged so $`\Gamma_i = \Gamma_{i-1}`. The last statement $`s_n` is typed in
$`\Gamma_{n-1}` and *its* synthesized type $`T` becomes the block's type. The block
opens a fresh nested scope, so declarations made inside don't leak out — once the block
ends, the surrounding $`\Gamma` is restored.

Discarding the types of non-last statements matches Java/Python/JavaScript, where
`f(x);` is a normal statement even when `f` returns a value. The trade-off is that a
stray expression like `5;` is silently accepted; flagging that belongs to a lint, not
the type checker.

$$`\frac{}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Block-Empty)}`

An empty block has no last statement to take a type from, so it defaults to `TVoid`.

{docstring Strata.Laurel.Resolution.Synth.block}

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \Rightarrow \_ \dashv \Gamma_i \;(1 \le i < n) \quad \Gamma_{n-1} \vdash s_n \Leftarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block)}`

The check form differs from the synth form in exactly one place: the *last* statement is
checked against the block's expected type $`T` instead of synthesizing freely. Non-last
statements are still synthesized-and-discarded, just as in the synth rule. Pushing $`T`
into the tail (rather than synthesizing the whole block and applying \[⇐\] Sub at the
boundary) means a type mismatch is reported at the offending subexpression's source
location, and the expectation continues to propagate through nested `Block` /
`IfThenElse` / `Hole` / `Quantifier` constructs that have their own check rules.

$$`\frac{\mathsf{TVoid} <: T}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block-Empty)}`

With no last statement to push the expectation into, the empty-block check falls back to
a single subsumption test: an empty block is acceptable wherever `TVoid` is.

{docstring Strata.Laurel.Resolution.Check.block}

$$`\frac{}{\Gamma \vdash \mathsf{Exit}\;\mathit{target} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Exit)}`

{docstring Strata.Laurel.Resolution.Synth.exit}

$$`\frac{}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None)}`

$$`\frac{\Gamma_{\mathit{proc}}.\mathit{outputs} = [T] \quad \Gamma \vdash e \Leftarrow T}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-Some)}`

$$`\frac{\Gamma_{\mathit{proc}}.\mathit{outputs} = []}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “void procedure cannot return a value”}} \quad \text{([⇒] Return-Void-Error)}`

$$`\frac{\Gamma_{\mathit{proc}}.\mathit{outputs} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “multi-output procedure cannot use ‘return e’; assign to named outputs instead”}} \quad \text{([⇒] Return-Multi-Error)}`

{docstring Strata.Laurel.Resolution.Synth.return}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{invs}_i \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{dec} \Leftarrow {?} \quad \Gamma \vdash \mathit{body} \Rightarrow \_}{\Gamma \vdash \mathsf{While}\;\mathit{cond}\;\mathit{invs}\;\mathit{dec}\;\mathit{body} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] While)}`

{docstring Strata.Laurel.Resolution.Synth.while}

### Verification statements

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assert}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assert)}`

{docstring Strata.Laurel.Resolution.Synth.assert}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assume}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assume)}`

{docstring Strata.Laurel.Resolution.Synth.assume}

### Assignment

$$`\frac{\Gamma \vdash \mathit{targets}_i \Rightarrow T_i \quad \Gamma \vdash e \Rightarrow T_e \quad T_e <: \mathit{ExpectedTy}}{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assign)}`

where `ExpectedTy = T_1` if `|targets| = 1` and `MultiValuedExpr [T_1; …; T_n]` otherwise.
The target's declared type `T_i` comes from the variable's scope entry (for
{name Strata.Laurel.Variable.Local}`Local` and {name Strata.Laurel.Variable.Field}`Field`)
or from the {name Strata.Laurel.Variable.Declare}`Declare`-bound parameter type.

{docstring Strata.Laurel.Resolution.Synth.assign}

{docstring Strata.Laurel.Resolution.Check.assign}

### Calls

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T] \quad \Gamma \vdash \mathit{args} \Rightarrow Us \quad U_i <: T_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Static-Call)}`

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T_1; \ldots; T_n],\; n \ne 1 \quad \Gamma \vdash \mathit{args} \Rightarrow Us \quad U_i <: T_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Static-Call-Multi)}`

{docstring Strata.Laurel.Resolution.Synth.staticCall}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance-procedure with inputs } [\mathit{self}; Ts] \text{ and outputs } [T] \quad \Gamma \vdash \mathit{args} \Rightarrow Us \quad U_i <: T_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Instance-Call)}`

{docstring Strata.Laurel.Resolution.Synth.instanceCall}

### Primitive operations

`Numeric` abbreviates "consistent with one of {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`".

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathsf{TBool} \quad \mathit{op} \in \{\mathsf{And}, \mathsf{Or}, \mathsf{AndThen}, \mathsf{OrElse}, \mathsf{Not}, \mathsf{Implies}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Bool)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathit{Numeric} \quad \mathit{op} \in \{\mathsf{Lt}, \mathsf{Leq}, \mathsf{Gt}, \mathsf{Geq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Cmp)}`

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad T_l \sim T_r \quad \mathit{op} \in \{\mathsf{Eq}, \mathsf{Neq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;[\mathit{lhs}; \mathit{rhs}] \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Eq)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathit{Numeric} \quad \Gamma \vdash \mathit{args}.\mathsf{head} \Rightarrow T \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Op-Arith)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Leftarrow \mathsf{TString} \quad \mathit{op} = \mathsf{StrConcat}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TString}} \quad \text{([⇒] Op-Concat)}`

{docstring Strata.Laurel.Resolution.Synth.primitiveOp}

### Object forms

$$`\frac{\Gamma(\mathit{ref}) \text{ is a composite or datatype } T}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{UserDefined}\;T} \quad \text{([⇒] New-Ok)}`

$$`\frac{\Gamma(\mathit{ref}) \text{ is not a composite or datatype}}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] New-Fallback)}`

{docstring Strata.Laurel.Resolution.Synth.new}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_}{\Gamma \vdash \mathsf{AsType}\;\mathit{target}\;T \Rightarrow T} \quad \text{([⇒] AsType)}`

{docstring Strata.Laurel.Resolution.Synth.asType}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_}{\Gamma \vdash \mathsf{IsType}\;\mathit{target}\;T \Rightarrow \mathsf{TBool}} \quad \text{([⇒] IsType)}`

{docstring Strata.Laurel.Resolution.Synth.isType}

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad \mathsf{isReference}\;T_l \quad \mathsf{isReference}\;T_r \quad T_l \sim T_r}{\Gamma \vdash \mathsf{ReferenceEquals}\;\mathit{lhs}\;\mathit{rhs} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] RefEq)}`

`isReference T` holds when `T` is a {name Strata.Laurel.HighType.UserDefined}`UserDefined`
or {name Strata.Laurel.HighType.Unknown}`Unknown` type. `~` is the consistency relation
{name Strata.Laurel.isConsistent}`isConsistent` — symmetric, with the
{name Strata.Laurel.HighType.Unknown}`Unknown` wildcard.

{docstring Strata.Laurel.Resolution.Synth.refEq}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T_t \quad \Gamma(f) = T_f \quad \Gamma \vdash \mathit{newVal} \Leftarrow T_f}{\Gamma \vdash \mathsf{PureFieldUpdate}\;\mathit{target}\;f\;\mathit{newVal} \Rightarrow T_t} \quad \text{([⇒] PureFieldUpdate)}`

{docstring Strata.Laurel.Resolution.Synth.pureFieldUpdate}

### Verification expressions

$$`\frac{\Gamma, x : T \vdash \mathit{body} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Quantifier}\;\mathit{mode}\;\langle x, T\rangle\;\mathit{trig}\;\mathit{body} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Quantifier)}`

{docstring Strata.Laurel.Resolution.Synth.quantifier}

$$`\frac{\Gamma \vdash \mathit{name} \Rightarrow \_}{\Gamma \vdash \mathsf{Assigned}\;\mathit{name} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Assigned)}`

{docstring Strata.Laurel.Resolution.Synth.assigned}

$$`\frac{\Gamma \vdash v \Rightarrow T}{\Gamma \vdash \mathsf{Old}\;v \Rightarrow T} \quad \text{([⇒] Old)}`

{docstring Strata.Laurel.Resolution.Synth.old}

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \mathsf{isReference}\;T}{\Gamma \vdash \mathsf{Fresh}\;v \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Fresh)}`

{docstring Strata.Laurel.Resolution.Synth.fresh}

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \Gamma \vdash \mathit{proof} \Rightarrow \_}{\Gamma \vdash \mathsf{ProveBy}\;v\;\mathit{proof} \Rightarrow T} \quad \text{([⇒] ProveBy)}`

{docstring Strata.Laurel.Resolution.Synth.proveBy}

### Self reference

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{some}\;T}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{UserDefined}\;T} \quad \text{([⇒] This-Inside)}`

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{none}}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{Unknown}\;\;[\text{emits “‘this’ is not allowed outside instance methods”}]} \quad \text{([⇒] This-Outside)}`

{docstring Strata.Laurel.Resolution.Synth.this}

### Untyped forms

$$`\frac{}{\Gamma \vdash \mathsf{Abstract}\;/\;\mathsf{All}\;\ldots \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Abstract / All)}`

{docstring Strata.Laurel.Resolution.Synth.abstract}

{docstring Strata.Laurel.Resolution.Synth.all}

### ContractOf

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Precondition}\;\mathit{fn} \Rightarrow \mathsf{TBool} \quad\quad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{PostCondition}\;\mathit{fn} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] ContractOf-Bool)}`

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Reads}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown} \quad\quad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{Modifies}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown}} \quad \text{([⇒] ContractOf-Set)}`

$$`\frac{\mathit{fn} \text{ is not a procedure reference}}{\Gamma \vdash \mathsf{ContractOf}\;\ldots\;\mathit{fn} \rightsquigarrow \text{error: “‘contractOf’ expected a procedure reference”}} \quad \text{([⇒] ContractOf-Error)}`

{docstring Strata.Laurel.Resolution.Synth.contractOf}

### Holes

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;(\mathsf{some}\;T) \Rightarrow T} \quad \text{([⇒] Hole-Some)}`

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Hole-None)}`

{docstring Strata.Laurel.Resolution.Synth.hole}

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Leftarrow T \;\;\mapsto\;\; \mathsf{Hole}\;d\;(\mathsf{some}\;T)} \quad \text{([⇐] Hole-None)}`

{docstring Strata.Laurel.Resolution.Check.holeNone}

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
arguments resolved through `Synth.resolveStmtExpr` instead of `Check.resolveStmtExpr`). As more constructs
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
